import V185TrunkScan23Chunk0745

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_4410992 : List Nat := [2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4]
def baseStart_4410992 : Nat := 118140960795 + 4410992 * 2 ^ 59
def prefixEnd_4410992 : Nat := 4983230072969 + 3 ^ 40 * 4410992 * 2
def baseEnd_4410992 : Nat := 2264959059137111207214223

theorem tailTrace_4410992 : CollatzResearch.WordTrace tailWord_4410992 prefixEnd_4410992 2264959059137111207214223 := by
  unfold tailWord_4410992
  simp only [CollatzResearch.WordTrace]
  refine ⟨80441047617868398151225615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107254730157157864201634153 80441047617868398151225615)
  ·
    refine ⟨120661571426802597226838423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80441047617868398151225615 120661571426802597226838423)
    ·
      refine ⟨180992357140203895840257635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120661571426802597226838423 180992357140203895840257635)
      ·
        refine ⟨271488535710305843760386453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180992357140203895840257635 271488535710305843760386453)
        ·
          refine ⟨12726025111420586426268115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 271488535710305843760386453 12726025111420586426268115)
          ·
            refine ⟨19089037667130879639402173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12726025111420586426268115 19089037667130879639402173)
            ·
              refine ⟨7158389125174079864775815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19089037667130879639402173 7158389125174079864775815)
              ·
                refine ⟨10737583687761119797163723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7158389125174079864775815 10737583687761119797163723)
                ·
                  refine ⟨16106375531641679695745585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10737583687761119797163723 16106375531641679695745585)
                  ·
                    refine ⟨12079781648731259771809189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16106375531641679695745585 12079781648731259771809189)
                    ·
                      refine ⟨2264959059137111207214223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12079781648731259771809189 2264959059137111207214223)
                      ·
                        rfl

theorem cell23_4410992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 1, 3, 1, 1, 2, 4].length) (baseStart_4410992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4410992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4410992 prefixEnd_4410992 := by exact prefixLift 4410992
  have htrace : WordTrace (prefixWord ++ tailWord_4410992) baseStart_4410992 baseEnd_4410992 := by
    simpa [prefixWord, tailWord_4410992, baseEnd_4410992] using wordTrace_append hprefix tailTrace_4410992
  have hstable : (prefixWord ++ tailWord_4410992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4410992).length < 2 ^ (prefixWord ++ tailWord_4410992).sum := by decide
  have hdescent : baseEnd_4410992 < baseStart_4410992 := by decide
  rcases family_descends (prefixWord ++ tailWord_4410992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411045 : List Nat := [1, 3, 1, 2, 1, 2, 2, 3, 2, 6]
def baseStart_4411045 : Nat := 118140960795 + 4411045 * 2 ^ 59
def prefixEnd_4411045 : Nat := 4983230072969 + 3 ^ 40 * 4411045 * 2
def baseEnd_4411045 : Nat := 754995424537266499950493

theorem tailTrace_4411045 : CollatzResearch.WordTrace tailWord_4411045 prefixEnd_4411045 754995424537266499950493 := by
  unfold tailWord_4411045
  simp only [CollatzResearch.WordTrace]
  refine ⟨160884028304544786354130589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107256018869696524236087059 160884028304544786354130589)
  ·
    refine ⟨60331510614204294882798971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160884028304544786354130589 60331510614204294882798971)
    ·
      refine ⟨90497265921306442324198457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60331510614204294882798971 90497265921306442324198457)
      ·
        refine ⟨67872949440979831743148843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90497265921306442324198457 67872949440979831743148843)
        ·
          refine ⟨101809424161469747614723265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67872949440979831743148843 101809424161469747614723265)
          ·
            refine ⟨76357068121102310711042449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101809424161469747614723265 76357068121102310711042449)
            ·
              refine ⟨57267801090826733033281837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76357068121102310711042449 57267801090826733033281837)
              ·
                refine ⟨21475425409060024887480689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57267801090826733033281837 21475425409060024887480689)
                ·
                  refine ⟨16106569056795018665610517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21475425409060024887480689 16106569056795018665610517)
                  ·
                    refine ⟨754995424537266499950493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16106569056795018665610517 754995424537266499950493)
                    ·
                      rfl

theorem cell23_4411045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 2, 2, 3, 2, 6].length) (baseStart_4411045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411045 prefixEnd_4411045 := by exact prefixLift 4411045
  have htrace : WordTrace (prefixWord ++ tailWord_4411045) baseStart_4411045 baseEnd_4411045 := by
    simpa [prefixWord, tailWord_4411045, baseEnd_4411045] using wordTrace_append hprefix tailTrace_4411045
  have hstable : (prefixWord ++ tailWord_4411045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411045).length < 2 ^ (prefixWord ++ tailWord_4411045).sum := by decide
  have hdescent : baseEnd_4411045 < baseStart_4411045 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411052 : List Nat := [2, 2, 1, 1, 1, 1, 1, 1, 7, 4, 2]
def baseStart_4411052 : Nat := 118140960795 + 4411052 * 2 ^ 59
def prefixEnd_4411052 : Nat := 4983230072969 + 3 ^ 40 * 4411052 * 2
def baseEnd_4411052 : Nat := 2264989867976380972463947

theorem tailTrace_4411052 : CollatzResearch.WordTrace tailWord_4411052 prefixEnd_4411052 2264989867976380972463947 := by
  unfold tailWord_4411052
  simp only [CollatzResearch.WordTrace]
  refine ⟨80442141807759713274817705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107256189077012951033090273 80442141807759713274817705)
  ·
    refine ⟨60331606355819784956113279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80442141807759713274817705 60331606355819784956113279)
    ·
      refine ⟨90497409533729677434169919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60331606355819784956113279 90497409533729677434169919)
      ·
        refine ⟨135746114300594516151254879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90497409533729677434169919 135746114300594516151254879)
        ·
          refine ⟨203619171450891774226882319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135746114300594516151254879 203619171450891774226882319)
          ·
            refine ⟨305428757176337661340323479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203619171450891774226882319 305428757176337661340323479)
            ·
              refine ⟨458143135764506492010485219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305428757176337661340323479 458143135764506492010485219)
              ·
                refine ⟨687214703646759738015727829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 458143135764506492010485219 687214703646759738015727829)
                ·
                  refine ⟨16106594616720931359743621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 687214703646759738015727829 16106594616720931359743621)
                  ·
                    refine ⟨3019986490635174629951929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16106594616720931359743621 3019986490635174629951929)
                    ·
                      refine ⟨2264989867976380972463947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019986490635174629951929 2264989867976380972463947)
                      ·
                        rfl

theorem cell23_4411052_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 4, 2].length) (baseStart_4411052 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411052 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411052 prefixEnd_4411052 := by exact prefixLift 4411052
  have htrace : WordTrace (prefixWord ++ tailWord_4411052) baseStart_4411052 baseEnd_4411052 := by
    simpa [prefixWord, tailWord_4411052, baseEnd_4411052] using wordTrace_append hprefix tailTrace_4411052
  have hstable : (prefixWord ++ tailWord_4411052).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411052).length < 2 ^ (prefixWord ++ tailWord_4411052).sum := by decide
  have hdescent : baseEnd_4411052 < baseStart_4411052 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411052) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411055 : List Nat := [1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 5]
def baseStart_4411055 : Nat := 118140960795 + 4411055 * 2 ^ 59
def prefixEnd_4411055 : Nat := 4983230072969 + 3 ^ 40 * 4411055 * 2
def baseEnd_4411055 : Nat := 2264991408418344460726433

theorem tailTrace_4411055 : CollatzResearch.WordTrace tailWord_4411055 prefixEnd_4411055 2264991408418344460726433 := by
  unfold tailWord_4411055
  simp only [CollatzResearch.WordTrace]
  refine ⟨160884393034508558061994619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107256262023005705374663079 160884393034508558061994619)
  ·
    refine ⟨241326589551762837092991929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160884393034508558061994619 241326589551762837092991929)
    ·
      refine ⟨180994942163822127819743947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241326589551762837092991929 180994942163822127819743947)
      ·
        refine ⟨271492413245733191729615921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 180994942163822127819743947 271492413245733191729615921)
        ·
          refine ⟨203619309934299893797211941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271492413245733191729615921 203619309934299893797211941)
          ·
            refine ⟨38178620612681230086977239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203619309934299893797211941 38178620612681230086977239)
            ·
              refine ⟨57267930919021845130465859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38178620612681230086977239 57267930919021845130465859)
              ·
                refine ⟨85901896378532767695698789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57267930919021845130465859 85901896378532767695698789)
                ·
                  refine ⟨16106605570974893942943523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85901896378532767695698789 16106605570974893942943523)
                  ·
                    refine ⟨24159908356462340914415285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16106605570974893942943523 24159908356462340914415285)
                    ·
                      refine ⟨2264991408418344460726433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24159908356462340914415285 2264991408418344460726433)
                      ·
                        rfl

theorem cell23_4411055_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 1, 4, 1, 5].length) (baseStart_4411055 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411055 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411055 prefixEnd_4411055 := by exact prefixLift 4411055
  have htrace : WordTrace (prefixWord ++ tailWord_4411055) baseStart_4411055 baseEnd_4411055 := by
    simpa [prefixWord, tailWord_4411055, baseEnd_4411055] using wordTrace_append hprefix tailTrace_4411055
  have hstable : (prefixWord ++ tailWord_4411055).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411055).length < 2 ^ (prefixWord ++ tailWord_4411055).sum := by decide
  have hdescent : baseEnd_4411055 < baseStart_4411055 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411055) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411069 : List Nat := [1, 4, 1, 2, 1, 2, 3, 2, 1, 4, 2]
def baseStart_4411069 : Nat := 118140960795 + 4411069 * 2 ^ 59
def prefixEnd_4411069 : Nat := 4983230072969 + 3 ^ 40 * 4411069 * 2
def baseEnd_4411069 : Nat := 2264998597147507405951369

theorem tailTrace_4411069 : CollatzResearch.WordTrace tailWord_4411069 prefixEnd_4411069 2264998597147507405951369 := by
  unfold tailWord_4411069
  simp only [CollatzResearch.WordTrace]
  refine ⟨160884903656457838453004261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107256602437638558968669507 160884903656457838453004261)
  ·
    refine ⟨30165919435585844709938299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160884903656457838453004261 30165919435585844709938299)
    ·
      refine ⟨45248879153378767064907449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30165919435585844709938299 45248879153378767064907449)
      ·
        refine ⟨33936659365034075298680587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45248879153378767064907449 33936659365034075298680587)
        ·
          refine ⟨50904989047551112948020881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33936659365034075298680587 50904989047551112948020881)
          ·
            refine ⟨38178741785663334711015661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50904989047551112948020881 38178741785663334711015661)
            ·
              refine ⟨14317028169623750516630873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38178741785663334711015661 14317028169623750516630873)
              ·
                refine ⟨10737771127217812887473155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14317028169623750516630873 10737771127217812887473155)
                ·
                  refine ⟨16106656690826719331209733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10737771127217812887473155 16106656690826719331209733)
                  ·
                    refine ⟨3019998129530009874601825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16106656690826719331209733 3019998129530009874601825)
                    ·
                      refine ⟨2264998597147507405951369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3019998129530009874601825 2264998597147507405951369)
                      ·
                        rfl

theorem cell23_4411069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 3, 2, 1, 4, 2].length) (baseStart_4411069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411069 prefixEnd_4411069 := by exact prefixLift 4411069
  have htrace : WordTrace (prefixWord ++ tailWord_4411069) baseStart_4411069 baseEnd_4411069 := by
    simpa [prefixWord, tailWord_4411069, baseEnd_4411069] using wordTrace_append hprefix tailTrace_4411069
  have hstable : (prefixWord ++ tailWord_4411069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411069).length < 2 ^ (prefixWord ++ tailWord_4411069).sum := by decide
  have hdescent : baseEnd_4411069 < baseStart_4411069 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411115 : List Nat := [1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7]
def baseStart_4411115 : Nat := 118140960795 + 4411115 * 2 ^ 59
def prefixEnd_4411115 : Nat := 4983230072969 + 3 ^ 40 * 4411115 * 2
def baseEnd_4411115 : Nat := 2265022217257614225976157

theorem tailTrace_4411115 : CollatzResearch.WordTrace tailWord_4411115 prefixEnd_4411115 2265022217257614225976157 := by
  unfold tailWord_4411115
  simp only [CollatzResearch.WordTrace]
  refine ⟨160886581414291188309178799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107257720942860792206119199 160886581414291188309178799)
  ·
    refine ⟨241329872121436782463768199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160886581414291188309178799 241329872121436782463768199)
    ·
      refine ⟨361994808182155173695652299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241329872121436782463768199 361994808182155173695652299)
      ·
        refine ⟨542992212273232760543478449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 361994808182155173695652299 542992212273232760543478449)
        ·
          refine ⟨407244159204924570407608837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 542992212273232760543478449 407244159204924570407608837)
          ·
            refine ⟨76358279850923356951426657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 407244159204924570407608837 76358279850923356951426657)
            ·
              refine ⟨57268709888192517713569993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76358279850923356951426657 57268709888192517713569993)
              ·
                refine ⟨42951532416144388285177495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57268709888192517713569993 42951532416144388285177495)
                ·
                  refine ⟨64427298624216582427766243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42951532416144388285177495 64427298624216582427766243)
                  ·
                    refine ⟨96640947936324873641649365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64427298624216582427766243 96640947936324873641649365)
                    ·
                      refine ⟨2265022217257614225976157, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96640947936324873641649365 2265022217257614225976157)
                      ·
                        rfl

theorem cell23_4411115_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 2, 2, 1, 1, 7].length) (baseStart_4411115 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411115 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411115 prefixEnd_4411115 := by exact prefixLift 4411115
  have htrace : WordTrace (prefixWord ++ tailWord_4411115) baseStart_4411115 baseEnd_4411115 := by
    simpa [prefixWord, tailWord_4411115, baseEnd_4411115] using wordTrace_append hprefix tailTrace_4411115
  have hstable : (prefixWord ++ tailWord_4411115).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411115).length < 2 ^ (prefixWord ++ tailWord_4411115).sum := by decide
  have hdescent : baseEnd_4411115 < baseStart_4411115 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411115) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411122 : List Nat := [3, 2, 1, 3, 1, 1, 3, 1, 1, 7]
def baseStart_4411122 : Nat := 118140960795 + 4411122 * 2 ^ 59
def prefixEnd_4411122 : Nat := 4983230072969 + 3 ^ 40 * 4411122 * 2
def baseEnd_4411122 : Nat := 755008603874065232862875

theorem tailTrace_4411122 : CollatzResearch.WordTrace tailWord_4411122 prefixEnd_4411122 755008603874065232862875 := by
  unfold tailWord_4411122
  simp only [CollatzResearch.WordTrace]
  refine ⟨40221709181316457126170905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107257891150177219003122413 40221709181316457126170905)
  ·
    refine ⟨30166281885987342844628179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40221709181316457126170905 30166281885987342844628179)
    ·
      refine ⟨45249422828981014266942269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30166281885987342844628179 45249422828981014266942269)
      ·
        refine ⟨16968533560867880350103351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45249422828981014266942269 16968533560867880350103351)
        ·
          refine ⟨25452800341301820525155027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16968533560867880350103351 25452800341301820525155027)
          ·
            refine ⟨38179200511952730787732541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25452800341301820525155027 38179200511952730787732541)
            ·
              refine ⟨14317200191982274045399703, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38179200511952730787732541 14317200191982274045399703)
              ·
                refine ⟨21475800287973411068099555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14317200191982274045399703 21475800287973411068099555)
                ·
                  refine ⟨32213700431960116602149333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21475800287973411068099555 32213700431960116602149333)
                  ·
                    refine ⟨755008603874065232862875, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32213700431960116602149333 755008603874065232862875)
                    ·
                      rfl

theorem cell23_4411122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 3, 1, 1, 7].length) (baseStart_4411122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411122 prefixEnd_4411122 := by exact prefixLift 4411122
  have htrace : WordTrace (prefixWord ++ tailWord_4411122) baseStart_4411122 baseEnd_4411122 := by
    simpa [prefixWord, tailWord_4411122, baseEnd_4411122] using wordTrace_append hprefix tailTrace_4411122
  have hstable : (prefixWord ++ tailWord_4411122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411122).length < 2 ^ (prefixWord ++ tailWord_4411122).sum := by decide
  have hdescent : baseEnd_4411122 < baseStart_4411122 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411126 : List Nat := [5, 1, 1, 1, 1, 4, 2, 3, 5]
def baseStart_4411126 : Nat := 118140960795 + 4411126 * 2 ^ 59
def prefixEnd_4411126 : Nat := 4983230072969 + 3 ^ 40 * 4411126 * 2
def baseEnd_4411126 : Nat := 251669762838312631437623

theorem tailTrace_4411126 : CollatzResearch.WordTrace tailWord_4411126 prefixEnd_4411126 251669762838312631437623 := by
  unfold tailWord_4411126
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055436413578208574239327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107257988411500891458552821 10055436413578208574239327)
  ·
    refine ⟨15083154620367312861358991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10055436413578208574239327 15083154620367312861358991)
    ·
      refine ⟨22624731930550969292038487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15083154620367312861358991 22624731930550969292038487)
      ·
        refine ⟨33937097895826453938057731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22624731930550969292038487 33937097895826453938057731)
        ·
          refine ⟨50905646843739680907086597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33937097895826453938057731 50905646843739680907086597)
          ·
            refine ⟨9544808783201190170078737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50905646843739680907086597 9544808783201190170078737)
            ·
              refine ⟨7158606587400892627559053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9544808783201190170078737 7158606587400892627559053)
              ·
                refine ⟨2684477470275334735334645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7158606587400892627559053 2684477470275334735334645)
                ·
                  refine ⟨251669762838312631437623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2684477470275334735334645 251669762838312631437623)
                  ·
                    rfl

theorem cell23_4411126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 4, 2, 3, 5].length) (baseStart_4411126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411126 prefixEnd_4411126 := by exact prefixLift 4411126
  have htrace : WordTrace (prefixWord ++ tailWord_4411126) baseStart_4411126 baseEnd_4411126 := by
    simpa [prefixWord, tailWord_4411126, baseEnd_4411126] using wordTrace_append hprefix tailTrace_4411126
  have hstable : (prefixWord ++ tailWord_4411126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411126).length < 2 ^ (prefixWord ++ tailWord_4411126).sum := by decide
  have hdescent : baseEnd_4411126 < baseStart_4411126 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411169 : List Nat := [1, 2, 3, 2, 1, 3, 2, 2, 3, 4]
def baseStart_4411169 : Nat := 118140960795 + 4411169 * 2 ^ 59
def prefixEnd_4411169 : Nat := 4983230072969 + 3 ^ 40 * 4411169 * 2
def baseEnd_4411169 : Nat := 755016648404319004900303

theorem tailTrace_4411169 : CollatzResearch.WordTrace tailWord_4411169 prefixEnd_4411169 755016648404319004900303 := by
  unfold tailWord_4411169
  simp only [CollatzResearch.WordTrace]
  refine ⟨160888550956095555531644561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107259033970730370354429707 160888550956095555531644561)
  ·
    refine ⟨120666413217071666648733421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160888550956095555531644561 120666413217071666648733421)
    ·
      refine ⟨45249904956401874993275033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120666413217071666648733421 45249904956401874993275033)
      ·
        refine ⟨33937428717301406244956275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45249904956401874993275033 33937428717301406244956275)
        ·
          refine ⟨50906143075952109367434413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33937428717301406244956275 50906143075952109367434413)
          ·
            refine ⟨19089803653482041012787905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50906143075952109367434413 19089803653482041012787905)
            ·
              refine ⟨14317352740111530759590929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19089803653482041012787905 14317352740111530759590929)
              ·
                refine ⟨10738014555083648069693197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14317352740111530759590929 10738014555083648069693197)
                ·
                  refine ⟨4026755458156368026134949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10738014555083648069693197 4026755458156368026134949)
                  ·
                    refine ⟨755016648404319004900303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4026755458156368026134949 755016648404319004900303)
                    ·
                      rfl

theorem cell23_4411169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 3, 2, 2, 3, 4].length) (baseStart_4411169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411169 prefixEnd_4411169 := by exact prefixLift 4411169
  have htrace : WordTrace (prefixWord ++ tailWord_4411169) baseStart_4411169 baseEnd_4411169 := by
    simpa [prefixWord, tailWord_4411169, baseEnd_4411169] using wordTrace_append hprefix tailTrace_4411169
  have hstable : (prefixWord ++ tailWord_4411169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411169).length < 2 ^ (prefixWord ++ tailWord_4411169).sum := by decide
  have hdescent : baseEnd_4411169 < baseStart_4411169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411203 : List Nat := [1, 1, 1, 3, 1, 6, 3, 2, 1, 4]
def baseStart_4411203 : Nat := 118140960795 + 4411203 * 2 ^ 59
def prefixEnd_4411203 : Nat := 4983230072969 + 3 ^ 40 * 4411203 * 2
def baseEnd_4411203 : Nat := 755022467851736627225251

theorem tailTrace_4411203 : CollatzResearch.WordTrace tailWord_4411203 prefixEnd_4411203 755022467851736627225251 := by
  unfold tailWord_4411203
  simp only [CollatzResearch.WordTrace]
  refine ⟨160889791037972379338382263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107259860691981586225588175 160889791037972379338382263)
  ·
    refine ⟨241334686556958569007573395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160889791037972379338382263 241334686556958569007573395)
    ·
      refine ⟨362002029835437853511360093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241334686556958569007573395 362002029835437853511360093)
      ·
        refine ⟨135750761188289195066760035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362002029835437853511360093 135750761188289195066760035)
        ·
          refine ⟨203626141782433792600140053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135750761188289195066760035 203626141782433792600140053)
          ·
            refine ⟨9544975396051584028131565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203626141782433792600140053 9544975396051584028131565)
            ·
              refine ⟨3579365773519344010549337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9544975396051584028131565 3579365773519344010549337)
              ·
                refine ⟨2684524330139508007912003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579365773519344010549337 2684524330139508007912003)
                ·
                  refine ⟨4026786495209262011868005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684524330139508007912003 4026786495209262011868005)
                  ·
                    refine ⟨755022467851736627225251, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4026786495209262011868005 755022467851736627225251)
                    ·
                      rfl

theorem cell23_4411203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 3, 2, 1, 4].length) (baseStart_4411203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411203 prefixEnd_4411203 := by exact prefixLift 4411203
  have htrace : WordTrace (prefixWord ++ tailWord_4411203) baseStart_4411203 baseEnd_4411203 := by
    simpa [prefixWord, tailWord_4411203, baseEnd_4411203] using wordTrace_append hprefix tailTrace_4411203
  have hstable : (prefixWord ++ tailWord_4411203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411203).length < 2 ^ (prefixWord ++ tailWord_4411203).sum := by decide
  have hdescent : baseEnd_4411203 < baseStart_4411203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411254 : List Nat := [5, 1, 1, 3, 3, 1, 2, 2, 1, 4]
def baseStart_4411254 : Nat := 118140960795 + 4411254 * 2 ^ 59
def prefixEnd_4411254 : Nat := 4983230072969 + 3 ^ 40 * 4411254 * 2
def baseEnd_4411254 : Nat := 755031197022863060712673

theorem tailTrace_4411254 : CollatzResearch.WordTrace tailWord_4411254 prefixEnd_4411254 755031197022863060712673 := by
  unfold tailWord_4411254
  simp only [CollatzResearch.WordTrace]
  refine ⟨10055728197549225940530551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107261100773858410032325877 10055728197549225940530551)
  ·
    refine ⟨15083592296323838910795827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10055728197549225940530551 15083592296323838910795827)
    ·
      refine ⟨22625388444485758366193741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15083592296323838910795827 22625388444485758366193741)
      ·
        refine ⟨8484520666682159387322653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22625388444485758366193741 8484520666682159387322653)
        ·
          refine ⟨3181695250005809770245995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8484520666682159387322653 3181695250005809770245995)
          ·
            refine ⟨4772542875008714655368993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3181695250005809770245995 4772542875008714655368993)
            ·
              refine ⟨3579407156256535991526745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4772542875008714655368993 3579407156256535991526745)
              ·
                refine ⟨2684555367192401993645059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3579407156256535991526745 2684555367192401993645059)
                ·
                  refine ⟨4026833050788602990467589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684555367192401993645059 4026833050788602990467589)
                  ·
                    refine ⟨755031197022863060712673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4026833050788602990467589 755031197022863060712673)
                    ·
                      rfl

theorem cell23_4411254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 2, 2, 1, 4].length) (baseStart_4411254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411254 prefixEnd_4411254 := by exact prefixLift 4411254
  have htrace : WordTrace (prefixWord ++ tailWord_4411254) baseStart_4411254 baseEnd_4411254 := by
    simpa [prefixWord, tailWord_4411254, baseEnd_4411254] using wordTrace_append hprefix tailTrace_4411254
  have hstable : (prefixWord ++ tailWord_4411254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411254).length < 2 ^ (prefixWord ++ tailWord_4411254).sum := by decide
  have hdescent : baseEnd_4411254 < baseStart_4411254 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411269 : List Nat := [1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 3]
def baseStart_4411269 : Nat := 118140960795 + 4411269 * 2 ^ 59
def prefixEnd_4411269 : Nat := 4983230072969 + 3 ^ 40 * 4411269 * 2
def baseEnd_4411269 : Nat := 2265101293278406623450449

theorem tailTrace_4411269 : CollatzResearch.WordTrace tailWord_4411269 prefixEnd_4411269 2265101293278406623450449 := by
  unfold tailWord_4411269
  simp only [CollatzResearch.WordTrace]
  refine ⟨160892198255733272610284861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107261465503822181740189907 160892198255733272610284861)
  ·
    refine ⟨60334574345899977228856823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160892198255733272610284861 60334574345899977228856823)
    ·
      refine ⟨90501861518849965843285235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60334574345899977228856823 90501861518849965843285235)
      ·
        refine ⟨135752792278274948764927853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90501861518849965843285235 135752792278274948764927853)
        ·
          refine ⟨50907297104353105786847945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135752792278274948764927853 50907297104353105786847945)
          ·
            refine ⟨38180472828264829340135959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50907297104353105786847945 38180472828264829340135959)
            ·
              refine ⟨57270709242397244010203939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38180472828264829340135959 57270709242397244010203939)
              ·
                refine ⟨85906063863595866015305909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57270709242397244010203939 85906063863595866015305909)
                ·
                  refine ⟨8053693487212112438934929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85906063863595866015305909 8053693487212112438934929)
                  ·
                    refine ⟨6040270115409084329201197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8053693487212112438934929 6040270115409084329201197)
                    ·
                      refine ⟨2265101293278406623450449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6040270115409084329201197 2265101293278406623450449)
                      ·
                        rfl

theorem cell23_4411269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 1, 1, 5, 2, 3].length) (baseStart_4411269 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411269 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411269 prefixEnd_4411269 := by exact prefixLift 4411269
  have htrace : WordTrace (prefixWord ++ tailWord_4411269) baseStart_4411269 baseEnd_4411269 := by
    simpa [prefixWord, tailWord_4411269, baseEnd_4411269] using wordTrace_append hprefix tailTrace_4411269
  have hstable : (prefixWord ++ tailWord_4411269).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411269).length < 2 ^ (prefixWord ++ tailWord_4411269).sum := by decide
  have hdescent : baseEnd_4411269 < baseStart_4411269 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411294 : List Nat := [4, 3, 1, 3, 1, 1, 2, 3, 1, 1, 3]
def baseStart_4411294 : Nat := 118140960795 + 4411294 * 2 ^ 59
def prefixEnd_4411294 : Nat := 4983230072969 + 3 ^ 40 * 4411294 * 2
def baseEnd_4411294 : Nat := 2265114130294769025637835

theorem tailTrace_4411294 : CollatzResearch.WordTrace tailWord_4411294 prefixEnd_4411294 2265114130294769025637835 := by
  unfold tailWord_4411294
  simp only [CollatzResearch.WordTrace]
  refine ⟨20111638760080337734993117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107262073387095134586629957 20111638760080337734993117)
  ·
    refine ⟨7541864535030126650622419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20111638760080337734993117 7541864535030126650622419)
    ·
      refine ⟨11312796802545189975933629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7541864535030126650622419 11312796802545189975933629)
      ·
        refine ⟨4242298800954446240975111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11312796802545189975933629 4242298800954446240975111)
        ·
          refine ⟨6363448201431669361462667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4242298800954446240975111 6363448201431669361462667)
          ·
            refine ⟨9545172302147504042194001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6363448201431669361462667 9545172302147504042194001)
            ·
              refine ⟨7158879226610628031645501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9545172302147504042194001 7158879226610628031645501)
              ·
                refine ⟨2684579709978985511867063, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7158879226610628031645501 2684579709978985511867063)
                ·
                  refine ⟨4026869564968478267800595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684579709978985511867063 4026869564968478267800595)
                  ·
                    refine ⟨6040304347452717401700893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4026869564968478267800595 6040304347452717401700893)
                    ·
                      refine ⟨2265114130294769025637835, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6040304347452717401700893 2265114130294769025637835)
                      ·
                        rfl

theorem cell23_4411294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 3, 1, 1, 3].length) (baseStart_4411294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411294 prefixEnd_4411294 := by exact prefixLift 4411294
  have htrace : WordTrace (prefixWord ++ tailWord_4411294) baseStart_4411294 baseEnd_4411294 := by
    simpa [prefixWord, tailWord_4411294, baseEnd_4411294] using wordTrace_append hprefix tailTrace_4411294
  have hstable : (prefixWord ++ tailWord_4411294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411294).length < 2 ^ (prefixWord ++ tailWord_4411294).sum := by decide
  have hdescent : baseEnd_4411294 < baseStart_4411294 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411300 : List Nat := [2, 3, 1, 2, 1, 3, 1, 5, 1, 2, 2]
def baseStart_4411300 : Nat := 118140960795 + 4411300 * 2 ^ 59
def prefixEnd_4411300 : Nat := 4983230072969 + 3 ^ 40 * 4411300 * 2
def baseEnd_4411300 : Nat := 2265117211178696002162807

theorem tailTrace_4411300 : CollatzResearch.WordTrace tailWord_4411300 prefixEnd_4411300 2265117211178696002162807 := by
  unfold tailWord_4411300
  simp only [CollatzResearch.WordTrace]
  refine ⟨80446664459310482452331677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107262219279080643269775569 80446664459310482452331677)
  ·
    refine ⟨30167499172241430919624379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80446664459310482452331677 30167499172241430919624379)
    ·
      refine ⟨45251248758362146379436569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30167499172241430919624379 45251248758362146379436569)
      ·
        refine ⟨33938436568771609784577427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45251248758362146379436569 33938436568771609784577427)
        ·
          refine ⟨50907654853157414676866141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33938436568771609784577427 50907654853157414676866141)
          ·
            refine ⟨19090370569934030503824803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50907654853157414676866141 19090370569934030503824803)
            ·
              refine ⟨28635555854901045755737205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19090370569934030503824803 28635555854901045755737205)
              ·
                refine ⟨2684583361396973039600363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28635555854901045755737205 2684583361396973039600363)
                ·
                  refine ⟨4026875042095459559400545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2684583361396973039600363 4026875042095459559400545)
                  ·
                    refine ⟨3020156281571594669550409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4026875042095459559400545 3020156281571594669550409)
                    ·
                      refine ⟨2265117211178696002162807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020156281571594669550409 2265117211178696002162807)
                      ·
                        rfl

theorem cell23_4411300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 3, 1, 5, 1, 2, 2].length) (baseStart_4411300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411300 prefixEnd_4411300 := by exact prefixLift 4411300
  have htrace : WordTrace (prefixWord ++ tailWord_4411300) baseStart_4411300 baseEnd_4411300 := by
    simpa [prefixWord, tailWord_4411300, baseEnd_4411300] using wordTrace_append hprefix tailTrace_4411300
  have hstable : (prefixWord ++ tailWord_4411300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411300).length < 2 ^ (prefixWord ++ tailWord_4411300).sum := by decide
  have hdescent : baseEnd_4411300 < baseStart_4411300 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411303 : List Nat := [1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 3]
def baseStart_4411303 : Nat := 118140960795 + 4411303 * 2 ^ 59
def prefixEnd_4411303 : Nat := 4983230072969 + 3 ^ 40 * 4411303 * 2
def baseEnd_4411303 : Nat := 2265118751620659490425293

theorem tailTrace_4411303 : CollatzResearch.WordTrace tailWord_4411303 prefixEnd_4411303 2265118751620659490425293 := by
  unfold tailWord_4411303
  simp only [CollatzResearch.WordTrace]
  refine ⟨160893438337610096417022563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107262292225073397611348375 160893438337610096417022563)
  ·
    refine ⟨241340157506415144625533845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160893438337610096417022563 241340157506415144625533845)
    ·
      refine ⟨11312819883113209904321899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 241340157506415144625533845 11312819883113209904321899)
      ·
        refine ⟨16969229824669814856482849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11312819883113209904321899 16969229824669814856482849)
        ·
          refine ⟨12726922368502361142362137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16969229824669814856482849 12726922368502361142362137)
          ·
            refine ⟨9545191776376770856771603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12726922368502361142362137 9545191776376770856771603)
            ·
              refine ⟨14317787664565156285157405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9545191776376770856771603 14317787664565156285157405)
              ·
                refine ⟨5369170374211933606934027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14317787664565156285157405 5369170374211933606934027)
                ·
                  refine ⟨8053755561317900410401041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5369170374211933606934027 8053755561317900410401041)
                  ·
                    refine ⟨6040316670988425307800781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8053755561317900410401041 6040316670988425307800781)
                    ·
                      refine ⟨2265118751620659490425293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6040316670988425307800781 2265118751620659490425293)
                      ·
                        rfl

theorem cell23_4411303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 2, 1, 3, 1, 2, 3].length) (baseStart_4411303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411303 prefixEnd_4411303 := by exact prefixLift 4411303
  have htrace : WordTrace (prefixWord ++ tailWord_4411303) baseStart_4411303 baseEnd_4411303 := by
    simpa [prefixWord, tailWord_4411303, baseEnd_4411303] using wordTrace_append hprefix tailTrace_4411303
  have hstable : (prefixWord ++ tailWord_4411303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411303).length < 2 ^ (prefixWord ++ tailWord_4411303).sum := by decide
  have hdescent : baseEnd_4411303 < baseStart_4411303 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411343 : List Nat := [1, 1, 2, 1, 1, 5, 4, 2, 1, 3, 2]
def baseStart_4411343 : Nat := 118140960795 + 4411343 * 2 ^ 59
def prefixEnd_4411343 : Nat := 4983230072969 + 3 ^ 40 * 4411343 * 2
def baseEnd_4411343 : Nat := 2265139290846839333925109

theorem tailTrace_4411343 : CollatzResearch.WordTrace tailWord_4411343 prefixEnd_4411343 2265139290846839333925109 := by
  unfold tailWord_4411343
  simp only [CollatzResearch.WordTrace]
  refine ⟨160894897257465183248478683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107263264838310122165652455 160894897257465183248478683)
  ·
    refine ⟨241342345886197774872718025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160894897257465183248478683 241342345886197774872718025)
    ·
      refine ⟨181006759414648331154538519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241342345886197774872718025 181006759414648331154538519)
      ·
        refine ⟨271510139121972496731807779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181006759414648331154538519 271510139121972496731807779)
        ·
          refine ⟨407265208682958745097711669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271510139121972496731807779 407265208682958745097711669)
          ·
            refine ⟨38181113314027382352910469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 407265208682958745097711669 38181113314027382352910469)
            ·
              refine ⟨7158958746380134191170713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38181113314027382352910469 7158958746380134191170713)
              ·
                refine ⟨5369219059785100643378035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7158958746380134191170713 5369219059785100643378035)
                ·
                  refine ⟨8053828589677650965067053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5369219059785100643378035 8053828589677650965067053)
                  ·
                    refine ⟨3020185721129119111900145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8053828589677650965067053 3020185721129119111900145)
                    ·
                      refine ⟨2265139290846839333925109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020185721129119111900145 2265139290846839333925109)
                      ·
                        rfl

theorem cell23_4411343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 5, 4, 2, 1, 3, 2].length) (baseStart_4411343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411343 prefixEnd_4411343 := by exact prefixLift 4411343
  have htrace : WordTrace (prefixWord ++ tailWord_4411343) baseStart_4411343 baseEnd_4411343 := by
    simpa [prefixWord, tailWord_4411343, baseEnd_4411343] using wordTrace_append hprefix tailTrace_4411343
  have hstable : (prefixWord ++ tailWord_4411343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411343).length < 2 ^ (prefixWord ++ tailWord_4411343).sum := by decide
  have hdescent : baseEnd_4411343 < baseStart_4411343 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411359 : List Nat := [1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 5]
def baseStart_4411359 : Nat := 118140960795 + 4411359 * 2 ^ 59
def prefixEnd_4411359 : Nat := 4983230072969 + 3 ^ 40 * 4411359 * 2
def baseEnd_4411359 : Nat := 2265147506537311271325035

theorem tailTrace_4411359 : CollatzResearch.WordTrace tailWord_4411359 prefixEnd_4411359 2265147506537311271325035 := by
  unfold tailWord_4411359
  simp only [CollatzResearch.WordTrace]
  refine ⟨160895480825407217981061131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107263653883604811987374087 160895480825407217981061131)
  ·
    refine ⟨241343221238110826971591697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160895480825407217981061131 241343221238110826971591697)
    ·
      refine ⟨181007415928583120228693773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241343221238110826971591697 181007415928583120228693773)
      ·
        refine ⟨67877780973218670085760165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181007415928583120228693773 67877780973218670085760165)
        ·
          refine ⟨12727083932478500641080031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67877780973218670085760165 12727083932478500641080031)
          ·
            refine ⟨19090625898717750961620047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12727083932478500641080031 19090625898717750961620047)
            ·
              refine ⟨28635938848076626442430071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19090625898717750961620047 28635938848076626442430071)
              ·
                refine ⟨42953908272114939663645107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28635938848076626442430071 42953908272114939663645107)
                ·
                  refine ⟨64430862408172409495467661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42953908272114939663645107 64430862408172409495467661)
                  ·
                    refine ⟨24161573403064653560800373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64430862408172409495467661 24161573403064653560800373)
                    ·
                      refine ⟨2265147506537311271325035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24161573403064653560800373 2265147506537311271325035)
                      ·
                        rfl

theorem cell23_4411359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 4, 1, 1, 1, 1, 3, 5].length) (baseStart_4411359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411359 prefixEnd_4411359 := by exact prefixLift 4411359
  have htrace : WordTrace (prefixWord ++ tailWord_4411359) baseStart_4411359 baseEnd_4411359 := by
    simpa [prefixWord, tailWord_4411359, baseEnd_4411359] using wordTrace_append hprefix tailTrace_4411359
  have hstable : (prefixWord ++ tailWord_4411359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411359).length < 2 ^ (prefixWord ++ tailWord_4411359).sum := by decide
  have hdescent : baseEnd_4411359 < baseStart_4411359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411426 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 2, 5]
def baseStart_4411426 : Nat := 118140960795 + 4411426 * 2 ^ 59
def prefixEnd_4411426 : Nat := 4983230072969 + 3 ^ 40 * 4411426 * 2
def baseEnd_4411426 : Nat := 755060636580387503062409

theorem tailTrace_4411426 : CollatzResearch.WordTrace tailWord_4411426 prefixEnd_4411426 755060636580387503062409 := by
  unfold tailWord_4411426
  simp only [CollatzResearch.WordTrace]
  refine ⟨40224481129041122105937533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107265283010776325615833421 40224481129041122105937533)
  ·
    refine ⟨15084180423390420789726575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40224481129041122105937533 15084180423390420789726575)
    ·
      refine ⟨22626270635085631184589863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15084180423390420789726575 22626270635085631184589863)
      ·
        refine ⟨33939405952628446776884795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22626270635085631184589863 33939405952628446776884795)
        ·
          refine ⟨50909108928942670165327193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33939405952628446776884795 50909108928942670165327193)
          ·
            refine ⟨38181831696707002623995395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50909108928942670165327193 38181831696707002623995395)
            ·
              refine ⟨57272747545060503935993093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38181831696707002623995395 57272747545060503935993093)
              ·
                refine ⟨10738640164698844487998705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57272747545060503935993093 10738640164698844487998705)
                ·
                  refine ⟨8053980123524133365999029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10738640164698844487998705 8053980123524133365999029)
                  ·
                    refine ⟨755060636580387503062409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8053980123524133365999029 755060636580387503062409)
                    ·
                      rfl

theorem cell23_4411426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 2, 5].length) (baseStart_4411426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411426 prefixEnd_4411426 := by exact prefixLift 4411426
  have htrace : WordTrace (prefixWord ++ tailWord_4411426) baseStart_4411426 baseEnd_4411426 := by
    simpa [prefixWord, tailWord_4411426, baseEnd_4411426] using wordTrace_append hprefix tailTrace_4411426
  have hstable : (prefixWord ++ tailWord_4411426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411426).length < 2 ^ (prefixWord ++ tailWord_4411426).sum := by decide
  have hdescent : baseEnd_4411426 < baseStart_4411426 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411456 : List Nat := [2, 1, 1, 2, 2, 4, 1, 1, 5, 4]
def baseStart_4411456 : Nat := 118140960795 + 4411456 * 2 ^ 59
def prefixEnd_4411456 : Nat := 4983230072969 + 3 ^ 40 * 4411456 * 2
def baseEnd_4411456 : Nat := 755065771386932463937363

theorem tailTrace_4411456 : CollatzResearch.WordTrace tailWord_4411456 prefixEnd_4411456 755065771386932463937363 := by
  unfold tailWord_4411456
  simp only [CollatzResearch.WordTrace]
  refine ⟨80449509353027901773671111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107266012470703869031561481 80449509353027901773671111)
  ·
    refine ⟨120674264029541852660506667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80449509353027901773671111 120674264029541852660506667)
    ·
      refine ⟨181011396044312778990760001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120674264029541852660506667 181011396044312778990760001)
      ·
        refine ⟨135758547033234584243070001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181011396044312778990760001 135758547033234584243070001)
        ·
          refine ⟨101818910274925938182302501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135758547033234584243070001 101818910274925938182302501)
          ·
            refine ⟨19091045676548613409181719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101818910274925938182302501 19091045676548613409181719)
            ·
              refine ⟨28636568514822920113772579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19091045676548613409181719 28636568514822920113772579)
              ·
                refine ⟨42954852772234380170658869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28636568514822920113772579 42954852772234380170658869)
                ·
                  refine ⟨4027017447396973140999269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42954852772234380170658869 4027017447396973140999269)
                  ·
                    refine ⟨755065771386932463937363, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027017447396973140999269 755065771386932463937363)
                    ·
                      rfl

theorem cell23_4411456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 1, 1, 5, 4].length) (baseStart_4411456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411456 prefixEnd_4411456 := by exact prefixLift 4411456
  have htrace : WordTrace (prefixWord ++ tailWord_4411456) baseStart_4411456 baseEnd_4411456 := by
    simpa [prefixWord, tailWord_4411456, baseEnd_4411456] using wordTrace_append hprefix tailTrace_4411456
  have hstable : (prefixWord ++ tailWord_4411456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411456).length < 2 ^ (prefixWord ++ tailWord_4411456).sum := by decide
  have hdescent : baseEnd_4411456 < baseStart_4411456 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411459 : List Nat := [1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4]
def baseStart_4411459 : Nat := 118140960795 + 4411459 * 2 ^ 59
def prefixEnd_4411459 : Nat := 4983230072969 + 3 ^ 40 * 4411459 * 2
def baseEnd_4411459 : Nat := 2265198854602760880074575

theorem tailTrace_4411459 : CollatzResearch.WordTrace tailWord_4411459 prefixEnd_4411459 2265198854602760880074575 := by
  unfold tailWord_4411459
  simp only [CollatzResearch.WordTrace]
  refine ⟨160899128125044935059701431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107266085416696623373134287 160899128125044935059701431)
  ·
    refine ⟨241348692187567402589552147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160899128125044935059701431 241348692187567402589552147)
    ·
      refine ⟨362023038281351103884328221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241348692187567402589552147 362023038281351103884328221)
      ·
        refine ⟨135758639355506663956623083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362023038281351103884328221 135758639355506663956623083)
        ·
          refine ⟨203637959033259995934934625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135758639355506663956623083 203637959033259995934934625)
          ·
            refine ⟨152728469274944996951200969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203637959033259995934934625 152728469274944996951200969)
            ·
              refine ⟨114546351956208747713400727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152728469274944996951200969 114546351956208747713400727)
              ·
                refine ⟨171819527934313121570101091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114546351956208747713400727 171819527934313121570101091)
                ·
                  refine ⟨257729291901469682355151637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 171819527934313121570101091 257729291901469682355151637)
                  ·
                    refine ⟨12081060557881391360397733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 257729291901469682355151637 12081060557881391360397733)
                    ·
                      refine ⟨2265198854602760880074575, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12081060557881391360397733 2265198854602760880074575)
                      ·
                        rfl

theorem cell23_4411459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 2, 1, 1, 6, 4].length) (baseStart_4411459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411459 prefixEnd_4411459 := by exact prefixLift 4411459
  have htrace : WordTrace (prefixWord ++ tailWord_4411459) baseStart_4411459 baseEnd_4411459 := by
    simpa [prefixWord, tailWord_4411459, baseEnd_4411459] using wordTrace_append hprefix tailTrace_4411459
  have hstable : (prefixWord ++ tailWord_4411459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411459).length < 2 ^ (prefixWord ++ tailWord_4411459).sum := by decide
  have hdescent : baseEnd_4411459 < baseStart_4411459 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411503 : List Nat := [1, 1, 2, 1, 3, 5, 3, 1, 6]
def baseStart_4411503 : Nat := 118140960795 + 4411503 * 2 ^ 59
def prefixEnd_4411503 : Nat := 4983230072969 + 3 ^ 40 * 4411503 * 2
def baseEnd_4411503 : Nat := 251691271972395411991597

theorem tailTrace_4411503 : CollatzResearch.WordTrace tailWord_4411503 prefixEnd_4411503 251691271972395411991597 := by
  unfold tailWord_4411503
  simp only [CollatzResearch.WordTrace]
  refine ⟨160900732936885530574303163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107267155291257020382868775 160900732936885530574303163)
  ·
    refine ⟨241351099405328295861454745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160900732936885530574303163 241351099405328295861454745)
    ·
      refine ⟨181013324553996221896091059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241351099405328295861454745 181013324553996221896091059)
      ·
        refine ⟨271519986830994332844136589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181013324553996221896091059 271519986830994332844136589)
        ·
          refine ⟨101819995061622874816551221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271519986830994332844136589 101819995061622874816551221)
          ·
            refine ⟨9545624537027144514051677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101819995061622874816551221 9545624537027144514051677)
            ·
              refine ⟨3579609201385179192769379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9545624537027144514051677 3579609201385179192769379)
              ·
                refine ⟨5369413802077768789154069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3579609201385179192769379 5369413802077768789154069)
                ·
                  refine ⟨251691271972395411991597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5369413802077768789154069 251691271972395411991597)
                  ·
                    rfl

theorem cell23_4411503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 5, 3, 1, 6].length) (baseStart_4411503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411503 prefixEnd_4411503 := by exact prefixLift 4411503
  have htrace : WordTrace (prefixWord ++ tailWord_4411503) baseStart_4411503 baseEnd_4411503 := by
    simpa [prefixWord, tailWord_4411503, baseEnd_4411503] using wordTrace_append hprefix tailTrace_4411503
  have hstable : (prefixWord ++ tailWord_4411503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411503).length < 2 ^ (prefixWord ++ tailWord_4411503).sum := by decide
  have hdescent : baseEnd_4411503 < baseStart_4411503 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411523 : List Nat := [1, 1, 1, 3, 3, 3, 2, 1, 1, 5, 2]
def baseStart_4411523 : Nat := 118140960795 + 4411523 * 2 ^ 59
def prefixEnd_4411523 : Nat := 4983230072969 + 3 ^ 40 * 4411523 * 2
def baseEnd_4411523 : Nat := 2265231717364648629674281

theorem tailTrace_4411523 : CollatzResearch.WordTrace tailWord_4411523 prefixEnd_4411523 2265231717364648629674281 := by
  unfold tailWord_4411523
  simp only [CollatzResearch.WordTrace]
  refine ⟨160901462396813073990031223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107267641597875382660020815 160901462396813073990031223)
  ·
    refine ⟨241352193595219610985046835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160901462396813073990031223 241352193595219610985046835)
    ·
      refine ⟨362028290392829416477570253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241352193595219610985046835 362028290392829416477570253)
      ·
        refine ⟨135760608897311031179088845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362028290392829416477570253 135760608897311031179088845)
        ·
          refine ⟨50910228336491636692158317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135760608897311031179088845 50910228336491636692158317)
          ·
            refine ⟨19091335626184363759559369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50910228336491636692158317 19091335626184363759559369)
            ·
              refine ⟨14318501719638272819669527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19091335626184363759559369 14318501719638272819669527)
              ·
                refine ⟨21477752579457409229504291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14318501719638272819669527 21477752579457409229504291)
                ·
                  refine ⟨32216628869186113844256437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21477752579457409229504291 32216628869186113844256437)
                  ·
                    refine ⟨3020308956486198172899041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32216628869186113844256437 3020308956486198172899041)
                    ·
                      refine ⟨2265231717364648629674281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020308956486198172899041 2265231717364648629674281)
                      ·
                        rfl

theorem cell23_4411523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 3, 2, 1, 1, 5, 2].length) (baseStart_4411523 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411523 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411523 prefixEnd_4411523 := by exact prefixLift 4411523
  have htrace : WordTrace (prefixWord ++ tailWord_4411523) baseStart_4411523 baseEnd_4411523 := by
    simpa [prefixWord, tailWord_4411523, baseEnd_4411523] using wordTrace_append hprefix tailTrace_4411523
  have hstable : (prefixWord ++ tailWord_4411523).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411523).length < 2 ^ (prefixWord ++ tailWord_4411523).sum := by decide
  have hdescent : baseEnd_4411523 < baseStart_4411523 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411570 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2]
def baseStart_4411570 : Nat := 118140960795 + 4411570 * 2 ^ 59
def prefixEnd_4411570 : Nat := 4983230072969 + 3 ^ 40 * 4411570 * 2
def baseEnd_4411570 : Nat := 2265255850955409945786565

theorem tailTrace_4411570 : CollatzResearch.WordTrace tailWord_4411570 prefixEnd_4411570 2265255850955409945786565 := by
  unfold tailWord_4411570
  simp only [CollatzResearch.WordTrace]
  refine ⟨40225794156910700254248041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107268784418428534011328109 40225794156910700254248041)
  ·
    refine ⟨30169345617683025190686031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40225794156910700254248041 30169345617683025190686031)
    ·
      refine ⟨45254018426524537786029047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30169345617683025190686031 45254018426524537786029047)
      ·
        refine ⟨67881027639786806679043571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45254018426524537786029047 67881027639786806679043571)
        ·
          refine ⟨101821541459680210018565357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67881027639786806679043571 101821541459680210018565357)
          ·
            refine ⟨38183078047380078756962009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101821541459680210018565357 38183078047380078756962009)
            ·
              refine ⟨28637308535535059067721507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38183078047380078756962009 28637308535535059067721507)
              ·
                refine ⟨42955962803302588601582261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28637308535535059067721507 42955962803302588601582261)
                ·
                  refine ⟨4027121512809617681398337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 42955962803302588601582261 4027121512809617681398337)
                  ·
                    refine ⟨3020341134607213261048753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4027121512809617681398337 3020341134607213261048753)
                    ·
                      refine ⟨2265255850955409945786565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020341134607213261048753 2265255850955409945786565)
                      ·
                        rfl

theorem cell23_4411570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 5, 2, 2].length) (baseStart_4411570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411570 prefixEnd_4411570 := by exact prefixLift 4411570
  have htrace : WordTrace (prefixWord ++ tailWord_4411570) baseStart_4411570 baseEnd_4411570 := by
    simpa [prefixWord, tailWord_4411570, baseEnd_4411570] using wordTrace_append hprefix tailTrace_4411570
  have hstable : (prefixWord ++ tailWord_4411570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411570).length < 2 ^ (prefixWord ++ tailWord_4411570).sum := by decide
  have hdescent : baseEnd_4411570 < baseStart_4411570 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411798 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 2, 5]
def baseStart_4411798 : Nat := 118140960795 + 4411798 * 2 ^ 59
def prefixEnd_4411798 : Nat := 4983230072969 + 3 ^ 40 * 4411798 * 2
def baseEnd_4411798 : Nat := 755124308181545017911839

theorem tailTrace_4411798 : CollatzResearch.WordTrace tailWord_4411798 prefixEnd_4411798 755124308181545017911839 := by
  unfold tailWord_4411798
  simp only [CollatzResearch.WordTrace]
  refine ⟨10056968279426049747268253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107274328313877863970861365 10056968279426049747268253)
  ·
    refine ⟨3771363104784768655225595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 10056968279426049747268253 3771363104784768655225595)
    ·
      refine ⟨5657044657177152982838393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3771363104784768655225595 5657044657177152982838393)
      ·
        refine ⟨4242783492882864737128795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5657044657177152982838393 4242783492882864737128795)
        ·
          refine ⟨6364175239324297105693193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4242783492882864737128795 6364175239324297105693193)
          ·
            refine ⟨4773131429493222829269895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6364175239324297105693193 4773131429493222829269895)
            ·
              refine ⟨7159697144239834243904843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773131429493222829269895 7159697144239834243904843)
              ·
                refine ⟨10739545716359751365857265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7159697144239834243904843 10739545716359751365857265)
                ·
                  refine ⟨8054659287269813524392949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10739545716359751365857265 8054659287269813524392949)
                  ·
                    refine ⟨755124308181545017911839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8054659287269813524392949 755124308181545017911839)
                    ·
                      rfl

theorem cell23_4411798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 2, 5].length) (baseStart_4411798 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411798 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411798 prefixEnd_4411798 := by exact prefixLift 4411798
  have htrace : WordTrace (prefixWord ++ tailWord_4411798) baseStart_4411798 baseEnd_4411798 := by
    simpa [prefixWord, tailWord_4411798, baseEnd_4411798] using wordTrace_append hprefix tailTrace_4411798
  have hstable : (prefixWord ++ tailWord_4411798).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411798).length < 2 ^ (prefixWord ++ tailWord_4411798).sum := by decide
  have hdescent : baseEnd_4411798 < baseStart_4411798 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411880 : List Nat := [2, 1, 4, 1, 1, 5, 9]
def baseStart_4411880 : Nat := 118140960795 + 4411880 * 2 ^ 59
def prefixEnd_4411880 : Nat := 4983230072969 + 3 ^ 40 * 4411880 * 2
def baseEnd_4411880 : Nat := 27968086789608688060619

theorem tailTrace_4411880 : CollatzResearch.WordTrace tailWord_4411880 prefixEnd_4411880 27968086789608688060619 := by
  unfold tailWord_4411880
  simp only [CollatzResearch.WordTrace]
  refine ⟨80457241628259861980388547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107276322171013149307184729 80457241628259861980388547)
  ·
    refine ⟨120685862442389792970582821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80457241628259861980388547 120685862442389792970582821)
    ·
      refine ⟨22628599207948086181984279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120685862442389792970582821 22628599207948086181984279)
      ·
        refine ⟨33942898811922129272976419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22628599207948086181984279 33942898811922129272976419)
        ·
          refine ⟨50914348217883193909464629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33942898811922129272976419 50914348217883193909464629)
          ·
            refine ⟨4773220145426549429012309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50914348217883193909464629 4773220145426549429012309)
            ·
              refine ⟨27968086789608688060619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 4773220145426549429012309 27968086789608688060619)
              ·
                rfl

theorem cell23_4411880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 9].length) (baseStart_4411880 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411880 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411880 prefixEnd_4411880 := by exact prefixLift 4411880
  have htrace : WordTrace (prefixWord ++ tailWord_4411880) baseStart_4411880 baseEnd_4411880 := by
    simpa [prefixWord, tailWord_4411880, baseEnd_4411880] using wordTrace_append hprefix tailTrace_4411880
  have hstable : (prefixWord ++ tailWord_4411880).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411880).length < 2 ^ (prefixWord ++ tailWord_4411880).sum := by decide
  have hdescent : baseEnd_4411880 < baseStart_4411880 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411911 : List Nat := [1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 3]
def baseStart_4411911 : Nat := 118140960795 + 4411911 * 2 ^ 59
def prefixEnd_4411911 : Nat := 4983230072969 + 3 ^ 40 * 4411911 * 2
def baseEnd_4411911 : Nat := 2265430947858593111622497

theorem tailTrace_4411911 : CollatzResearch.WordTrace tailWord_4411911 prefixEnd_4411911 2265430947858593111622497 := by
  unfold tailWord_4411911
  simp only [CollatzResearch.WordTrace]
  refine ⟨160915613919407416255155587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107277075946271610836770391 160915613919407416255155587)
  ·
    refine ⟨241373420879111124382733381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160915613919407416255155587 241373420879111124382733381)
    ·
      refine ⟨45257516414833335821762509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241373420879111124382733381 45257516414833335821762509)
      ·
        refine ⟨16971568655562500933160941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45257516414833335821762509 16971568655562500933160941)
        ·
          refine ⟨6364338245835937849935353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16971568655562500933160941 6364338245835937849935353)
          ·
            refine ⟨4773253684376953387451515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6364338245835937849935353 4773253684376953387451515)
            ·
              refine ⟨7159880526565430081177273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773253684376953387451515 7159880526565430081177273)
              ·
                refine ⟨5369910394924072560882955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7159880526565430081177273 5369910394924072560882955)
                ·
                  refine ⟨8054865592386108841324433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5369910394924072560882955 8054865592386108841324433)
                  ·
                    refine ⟨6041149194289581630993325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8054865592386108841324433 6041149194289581630993325)
                    ·
                      refine ⟨2265430947858593111622497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6041149194289581630993325 2265430947858593111622497)
                      ·
                        rfl

theorem cell23_4411911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 1, 2, 1, 2, 3].length) (baseStart_4411911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411911 prefixEnd_4411911 := by exact prefixLift 4411911
  have htrace : WordTrace (prefixWord ++ tailWord_4411911) baseStart_4411911 baseEnd_4411911 := by
    simpa [prefixWord, tailWord_4411911, baseEnd_4411911] using wordTrace_append hprefix tailTrace_4411911
  have hstable : (prefixWord ++ tailWord_4411911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411911).length < 2 ^ (prefixWord ++ tailWord_4411911).sum := by decide
  have hdescent : baseEnd_4411911 < baseStart_4411911 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411924 : List Nat := [2, 4, 3, 1, 1, 1, 1, 1, 3, 3, 3]
def baseStart_4411924 : Nat := 118140960795 + 4411924 * 2 ^ 59
def prefixEnd_4411924 : Nat := 4983230072969 + 3 ^ 40 * 4411924 * 2
def baseEnd_4411924 : Nat := 2265437623107101560759937

theorem tailTrace_4411924 : CollatzResearch.WordTrace tailWord_4411924 prefixEnd_4411924 2265437623107101560759937 := by
  unfold tailWord_4411924
  simp only [CollatzResearch.WordTrace]
  refine ⟨80458044034180159737689413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107277392045573546316919217 80458044034180159737689413)
  ·
    refine ⟨15085883256408779950816765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80458044034180159737689413 15085883256408779950816765)
    ·
      refine ⟨5657206221153292481556287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15085883256408779950816765 5657206221153292481556287)
      ·
        refine ⟨8485809331729938722334431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657206221153292481556287 8485809331729938722334431)
        ·
          refine ⟨12728713997594908083501647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8485809331729938722334431 12728713997594908083501647)
          ·
            refine ⟨19093070996392362125252471, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12728713997594908083501647 19093070996392362125252471)
            ·
              refine ⟨28639606494588543187878707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19093070996392362125252471 28639606494588543187878707)
              ·
                refine ⟨42959409741882814781818061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28639606494588543187878707 42959409741882814781818061)
                ·
                  refine ⟨16109778653206055543181773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42959409741882814781818061 16109778653206055543181773)
                  ·
                    refine ⟨6041166994952270828693165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16109778653206055543181773 6041166994952270828693165)
                    ·
                      refine ⟨2265437623107101560759937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6041166994952270828693165 2265437623107101560759937)
                      ·
                        rfl

theorem cell23_4411924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_4411924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411924 prefixEnd_4411924 := by exact prefixLift 4411924
  have htrace : WordTrace (prefixWord ++ tailWord_4411924) baseStart_4411924 baseEnd_4411924 := by
    simpa [prefixWord, tailWord_4411924, baseEnd_4411924] using wordTrace_append hprefix tailTrace_4411924
  have hstable : (prefixWord ++ tailWord_4411924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411924).length < 2 ^ (prefixWord ++ tailWord_4411924).sum := by decide
  have hdescent : baseEnd_4411924 < baseStart_4411924 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411964 : List Nat := [2, 2, 2, 2, 3, 1, 1, 3, 1, 4, 2]
def baseStart_4411964 : Nat := 118140960795 + 4411964 * 2 ^ 59
def prefixEnd_4411964 : Nat := 4983230072969 + 3 ^ 40 * 4411964 * 2
def baseEnd_4411964 : Nat := 2265458162333281404259753

theorem tailTrace_4411964 : CollatzResearch.WordTrace tailWord_4411964 prefixEnd_4411964 2265458162333281404259753 := by
  unfold tailWord_4411964
  simp only [CollatzResearch.WordTrace]
  refine ⟨80458773494107703153417473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107278364658810270871223297 80458773494107703153417473)
  ·
    refine ⟨60344080120580777365063105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80458773494107703153417473 60344080120580777365063105)
    ·
      refine ⟨45258060090435583023797329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60344080120580777365063105 45258060090435583023797329)
      ·
        refine ⟨33943545067826687267847997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45258060090435583023797329 33943545067826687267847997)
        ·
          refine ⟨12728829400435007725442999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33943545067826687267847997 12728829400435007725442999)
          ·
            refine ⟨19093244100652511588164499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12728829400435007725442999 19093244100652511588164499)
            ·
              refine ⟨28639866150978767382246749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19093244100652511588164499 28639866150978767382246749)
              ·
                refine ⟨10739949806617037768342531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28639866150978767382246749 10739949806617037768342531)
                ·
                  refine ⟨16109924709925556652513797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10739949806617037768342531 16109924709925556652513797)
                  ·
                    refine ⟨3020610883111041872346337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16109924709925556652513797 3020610883111041872346337)
                    ·
                      refine ⟨2265458162333281404259753, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020610883111041872346337 2265458162333281404259753)
                      ·
                        rfl

theorem cell23_4411964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 3, 1, 4, 2].length) (baseStart_4411964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411964 prefixEnd_4411964 := by exact prefixLift 4411964
  have htrace : WordTrace (prefixWord ++ tailWord_4411964) baseStart_4411964 baseEnd_4411964 := by
    simpa [prefixWord, tailWord_4411964, baseEnd_4411964] using wordTrace_append hprefix tailTrace_4411964
  have hstable : (prefixWord ++ tailWord_4411964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411964).length < 2 ^ (prefixWord ++ tailWord_4411964).sum := by decide
  have hdescent : baseEnd_4411964 < baseStart_4411964 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4411981 : List Nat := [1, 6, 1, 1, 2, 1, 2, 2, 1, 4, 2]
def baseStart_4411981 : Nat := 118140960795 + 4411981 * 2 ^ 59
def prefixEnd_4411981 : Nat := 4983230072969 + 3 ^ 40 * 4411981 * 2
def baseEnd_4411981 : Nat := 2265466891504407837747175

theorem tailTrace_4411981 : CollatzResearch.WordTrace tailWord_4411981 prefixEnd_4411981 2265466891504407837747175 := by
  unfold tailWord_4411981
  simp only [CollatzResearch.WordTrace]
  refine ⟨160918167029153818210203797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107278778019435878806802531 160918167029153818210203797)
  ·
    refine ⟨7543039079491585228603303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 160918167029153818210203797 7543039079491585228603303)
    ·
      refine ⟨11314558619237377842904955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7543039079491585228603303 11314558619237377842904955)
      ·
        refine ⟨16971837928856066764357433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11314558619237377842904955 16971837928856066764357433)
        ·
          refine ⟨12728878446642050073268075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16971837928856066764357433 12728878446642050073268075)
          ·
            refine ⟨19093317669963075109902113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12728878446642050073268075 19093317669963075109902113)
            ·
              refine ⟨14319988252472306332426585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19093317669963075109902113 14319988252472306332426585)
              ·
                refine ⟨10739991189354229749319939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14319988252472306332426585 10739991189354229749319939)
                ·
                  refine ⟨16109986784031344623979909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10739991189354229749319939 16109986784031344623979909)
                  ·
                    refine ⟨3020622522005877116996233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16109986784031344623979909 3020622522005877116996233)
                    ·
                      refine ⟨2265466891504407837747175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020622522005877116996233 2265466891504407837747175)
                      ·
                        rfl

theorem cell23_4411981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 2, 1, 4, 2].length) (baseStart_4411981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4411981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4411981 prefixEnd_4411981 := by exact prefixLift 4411981
  have htrace : WordTrace (prefixWord ++ tailWord_4411981) baseStart_4411981 baseEnd_4411981 := by
    simpa [prefixWord, tailWord_4411981, baseEnd_4411981] using wordTrace_append hprefix tailTrace_4411981
  have hstable : (prefixWord ++ tailWord_4411981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4411981).length < 2 ^ (prefixWord ++ tailWord_4411981).sum := by decide
  have hdescent : baseEnd_4411981 < baseStart_4411981 := by decide
  rcases family_descends (prefixWord ++ tailWord_4411981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412014 : List Nat := [4, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3]
def baseStart_4412014 : Nat := 118140960795 + 4412014 * 2 ^ 59
def prefixEnd_4412014 : Nat := 4983230072969 + 3 ^ 40 * 4412014 * 2
def baseEnd_4412014 : Nat := 2265483836366006208634523

theorem tailTrace_4412014 : CollatzResearch.WordTrace tailWord_4412014 prefixEnd_4412014 2265483836366006208634523 := by
  unfold tailWord_4412014
  simp only [CollatzResearch.WordTrace]
  refine ⟨20114921329754283105769387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107279580425356176564103397 20114921329754283105769387)
  ·
    refine ⟨30172381994631424658654081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20114921329754283105769387 30172381994631424658654081)
    ·
      refine ⟨22629286495973568493990561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30172381994631424658654081 22629286495973568493990561)
      ·
        refine ⟨16971964871980176370492921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22629286495973568493990561 16971964871980176370492921)
        ·
          refine ⟨12728973653985132277869691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16971964871980176370492921 12728973653985132277869691)
          ·
            refine ⟨19093460480977698416804537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12728973653985132277869691 19093460480977698416804537)
            ·
              refine ⟨14320095360733273812603403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19093460480977698416804537 14320095360733273812603403)
              ·
                refine ⟨21480143041099910718905105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14320095360733273812603403 21480143041099910718905105)
                ·
                  refine ⟨16110107280824933039178829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21480143041099910718905105 16110107280824933039178829)
                  ·
                    refine ⟨6041290230309349889692061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16110107280824933039178829 6041290230309349889692061)
                    ·
                      refine ⟨2265483836366006208634523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6041290230309349889692061 2265483836366006208634523)
                      ·
                        rfl

theorem cell23_4412014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_4412014 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412014 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412014 prefixEnd_4412014 := by exact prefixLift 4412014
  have htrace : WordTrace (prefixWord ++ tailWord_4412014) baseStart_4412014 baseEnd_4412014 := by
    simpa [prefixWord, tailWord_4412014, baseEnd_4412014] using wordTrace_append hprefix tailTrace_4412014
  have hstable : (prefixWord ++ tailWord_4412014).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412014).length < 2 ^ (prefixWord ++ tailWord_4412014).sum := by decide
  have hdescent : baseEnd_4412014 < baseStart_4412014 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412037 : List Nat := [1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 4]
def baseStart_4412037 : Nat := 118140960795 + 4412037 * 2 ^ 59
def prefixEnd_4412037 : Nat := 4983230072969 + 3 ^ 40 * 4412037 * 2
def baseEnd_4412037 : Nat := 2265495646421059618646917

theorem tailTrace_4412037 : CollatzResearch.WordTrace tailWord_4412037 prefixEnd_4412037 2265495646421059618646917 := by
  unfold tailWord_4412037
  simp only [CollatzResearch.WordTrace]
  refine ⟨160920209516950939774242365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107280139677967293182828243 160920209516950939774242365)
  ·
    refine ⟨60345078568856602415340887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160920209516950939774242365 60345078568856602415340887)
    ·
      refine ⟨90517617853284903623011331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60345078568856602415340887 90517617853284903623011331)
      ·
        refine ⟨135776426779927355434516997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90517617853284903623011331 135776426779927355434516997)
        ·
          refine ⟨25458080021236379143971937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135776426779927355434516997 25458080021236379143971937)
          ·
            refine ⟨19093560015927284357978953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25458080021236379143971937 19093560015927284357978953)
            ·
              refine ⟨14320170011945463268484215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19093560015927284357978953 14320170011945463268484215)
              ·
                refine ⟨21480255017918194902726323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14320170011945463268484215 21480255017918194902726323)
                ·
                  refine ⟨32220382526877292354089485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21480255017918194902726323 32220382526877292354089485)
                  ·
                    refine ⟨12082643447578984632783557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32220382526877292354089485 12082643447578984632783557)
                    ·
                      refine ⟨2265495646421059618646917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12082643447578984632783557 2265495646421059618646917)
                      ·
                        rfl

theorem cell23_4412037_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 1, 1, 3, 4].length) (baseStart_4412037 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412037 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412037 prefixEnd_4412037 := by exact prefixLift 4412037
  have htrace : WordTrace (prefixWord ++ tailWord_4412037) baseStart_4412037 baseEnd_4412037 := by
    simpa [prefixWord, tailWord_4412037, baseEnd_4412037] using wordTrace_append hprefix tailTrace_4412037
  have hstable : (prefixWord ++ tailWord_4412037).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412037).length < 2 ^ (prefixWord ++ tailWord_4412037).sum := by decide
  have hdescent : baseEnd_4412037 < baseStart_4412037 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412037) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412137 : List Nat := [1, 2, 1, 1, 1, 2, 5, 3, 1, 6]
def baseStart_4412137 : Nat := 118140960795 + 4412137 * 2 ^ 59
def prefixEnd_4412137 : Nat := 4983230072969 + 3 ^ 40 * 4412137 * 2
def baseEnd_4412137 : Nat := 755182331495503075798819

theorem tailTrace_4412137 : CollatzResearch.WordTrace tailWord_4412137 prefixEnd_4412137 755182331495503075798819 := by
  unfold tailWord_4412137
  simp only [CollatzResearch.WordTrace]
  refine ⟨160923856816588656852882665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107282571211059104568588443 160923856816588656852882665)
  ·
    refine ⟨120692892612441492639661999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160923856816588656852882665 120692892612441492639661999)
    ·
      refine ⟨181039338918662238959492999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120692892612441492639661999 181039338918662238959492999)
      ·
        refine ⟨271559008377993358439239499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181039338918662238959492999 271559008377993358439239499)
        ·
          refine ⟨407338512566990037658859249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271559008377993358439239499 407338512566990037658859249)
          ·
            refine ⟨305503884425242528244144437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407338512566990037658859249 305503884425242528244144437)
            ·
              refine ⟨28640989164866487022888541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 305503884425242528244144437 28640989164866487022888541)
              ·
                refine ⟨10740370936824932633583203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28640989164866487022888541 10740370936824932633583203)
                ·
                  refine ⟨16110556405237398950374805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10740370936824932633583203 16110556405237398950374805)
                  ·
                    refine ⟨755182331495503075798819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16110556405237398950374805 755182331495503075798819)
                    ·
                      rfl

theorem cell23_4412137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 3, 1, 6].length) (baseStart_4412137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412137 prefixEnd_4412137 := by exact prefixLift 4412137
  have htrace : WordTrace (prefixWord ++ tailWord_4412137) baseStart_4412137 baseEnd_4412137 := by
    simpa [prefixWord, tailWord_4412137, baseEnd_4412137] using wordTrace_append hprefix tailTrace_4412137
  have hstable : (prefixWord ++ tailWord_4412137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412137).length < 2 ^ (prefixWord ++ tailWord_4412137).sum := by decide
  have hdescent : baseEnd_4412137 < baseStart_4412137 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412144 : List Nat := [2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4]
def baseStart_4412144 : Nat := 118140960795 + 4412144 * 2 ^ 59
def prefixEnd_4412144 : Nat := 4983230072969 + 3 ^ 40 * 4412144 * 2
def baseEnd_4412144 : Nat := 2265550588851090700008925

theorem tailTrace_4412144 : CollatzResearch.WordTrace tailWord_4412144 prefixEnd_4412144 2265550588851090700008925 := by
  unfold tailWord_4412144
  simp only [CollatzResearch.WordTrace]
  refine ⟨80462056063781648524193743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107282741418375531365591657 80462056063781648524193743)
  ·
    refine ⟨120693084095672472786290615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80462056063781648524193743 120693084095672472786290615)
    ·
      refine ⟨181039626143508709179435923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120693084095672472786290615 181039626143508709179435923)
      ·
        refine ⟨271559439215263063769153885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181039626143508709179435923 271559439215263063769153885)
        ·
          refine ⟨101834789705723648913432707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271559439215263063769153885 101834789705723648913432707)
          ·
            refine ⟨152752184558585473370149061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101834789705723648913432707 152752184558585473370149061)
            ·
              refine ⟨28641034604734776256902949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152752184558585473370149061 28641034604734776256902949)
              ·
                refine ⟨5370193988387770548169303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28641034604734776256902949 5370193988387770548169303)
                ·
                  refine ⟨8055290982581655822253955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5370193988387770548169303 8055290982581655822253955)
                  ·
                    refine ⟨12082936473872483733380933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8055290982581655822253955 12082936473872483733380933)
                    ·
                      refine ⟨2265550588851090700008925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12082936473872483733380933 2265550588851090700008925)
                      ·
                        rfl

theorem cell23_4412144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 4, 4, 1, 1, 4].length) (baseStart_4412144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412144 prefixEnd_4412144 := by exact prefixLift 4412144
  have htrace : WordTrace (prefixWord ++ tailWord_4412144) baseStart_4412144 baseEnd_4412144 := by
    simpa [prefixWord, tailWord_4412144, baseEnd_4412144] using wordTrace_append hprefix tailTrace_4412144
  have hstable : (prefixWord ++ tailWord_4412144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412144).length < 2 ^ (prefixWord ++ tailWord_4412144).sum := by decide
  have hdescent : baseEnd_4412144 < baseStart_4412144 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412158 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4412158 : Nat := 118140960795 + 4412158 * 2 ^ 59
def prefixEnd_4412158 : Nat := 4983230072969 + 3 ^ 40 * 4412158 * 2
def baseEnd_4412158 : Nat := 755185925860084548411287

theorem tailTrace_4412158 : CollatzResearch.WordTrace tailWord_4412158 prefixEnd_4412158 755185925860084548411287 := by
  unfold tailWord_4412158
  simp only [CollatzResearch.WordTrace]
  refine ⟨20115577843689072179924641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107283081833008384959598085 20115577843689072179924641)
  ·
    refine ⟨15086683382766804134943481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20115577843689072179924641 15086683382766804134943481)
    ·
      refine ⟨11315012537075103101207611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15086683382766804134943481 11315012537075103101207611)
      ·
        refine ⟨16972518805612654651811417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11315012537075103101207611 16972518805612654651811417)
        ·
          refine ⟨12729389104209490988858563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16972518805612654651811417 12729389104209490988858563)
          ·
            refine ⟨19094083656314236483287845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12729389104209490988858563 19094083656314236483287845)
            ·
              refine ⟨3580140685558919340616471, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19094083656314236483287845 3580140685558919340616471)
              ·
                refine ⟨5370211028338379010924707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580140685558919340616471 5370211028338379010924707)
                ·
                  refine ⟨8055316542507568516387061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5370211028338379010924707 8055316542507568516387061)
                  ·
                    refine ⟨755185925860084548411287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8055316542507568516387061 755185925860084548411287)
                    ·
                      rfl

theorem cell23_4412158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4412158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412158 prefixEnd_4412158 := by exact prefixLift 4412158
  have htrace : WordTrace (prefixWord ++ tailWord_4412158) baseStart_4412158 baseEnd_4412158 := by
    simpa [prefixWord, tailWord_4412158, baseEnd_4412158] using wordTrace_append hprefix tailTrace_4412158
  have hstable : (prefixWord ++ tailWord_4412158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412158).length < 2 ^ (prefixWord ++ tailWord_4412158).sum := by decide
  have hdescent : baseEnd_4412158 < baseStart_4412158 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412161 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 7, 2, 2]
def baseStart_4412161 : Nat := 118140960795 + 4412161 * 2 ^ 59
def prefixEnd_4412161 : Nat := 4983230072969 + 3 ^ 40 * 4412161 * 2
def baseEnd_4412161 : Nat := 2265559318022217133496347

theorem tailTrace_4412161 : CollatzResearch.WordTrace tailWord_4412161 prefixEnd_4412161 2265559318022217133496347 := by
  unfold tailWord_4412161
  simp only [CollatzResearch.WordTrace]
  refine ⟨160924732168501708951756337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107283154779001139301170891 160924732168501708951756337)
  ·
    refine ⟨120693549126376281713817253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160924732168501708951756337 120693549126376281713817253)
    ·
      refine ⟨22630040461195552821340735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120693549126376281713817253 22630040461195552821340735)
      ·
        refine ⟨33945060691793329232011103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22630040461195552821340735 33945060691793329232011103)
        ·
          refine ⟨50917591037689993848016655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33945060691793329232011103 50917591037689993848016655)
          ·
            refine ⟨76376386556534990772024983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50917591037689993848016655 76376386556534990772024983)
            ·
              refine ⟨114564579834802486158037475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76376386556534990772024983 114564579834802486158037475)
              ·
                refine ⟨171846869752203729237056213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114564579834802486158037475 171846869752203729237056213)
                ·
                  refine ⟨4027661009817274903993505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 171846869752203729237056213 4027661009817274903993505)
                  ·
                    refine ⟨3020745757362956177995129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4027661009817274903993505 3020745757362956177995129)
                    ·
                      refine ⟨2265559318022217133496347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020745757362956177995129 2265559318022217133496347)
                      ·
                        rfl

theorem cell23_4412161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 7, 2, 2].length) (baseStart_4412161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412161 prefixEnd_4412161 := by exact prefixLift 4412161
  have htrace : WordTrace (prefixWord ++ tailWord_4412161) baseStart_4412161 baseEnd_4412161 := by
    simpa [prefixWord, tailWord_4412161, baseEnd_4412161] using wordTrace_append hprefix tailTrace_4412161
  have hstable : (prefixWord ++ tailWord_4412161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412161).length < 2 ^ (prefixWord ++ tailWord_4412161).sum := by decide
  have hdescent : baseEnd_4412161 < baseStart_4412161 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412164 : List Nat := [2, 3, 2, 2, 1, 1, 2, 3, 1, 1, 5]
def baseStart_4412164 : Nat := 118140960795 + 4412164 * 2 ^ 59
def prefixEnd_4412164 : Nat := 4983230072969 + 3 ^ 40 * 4412164 * 2
def baseEnd_4412164 : Nat := 2265560858464180621758833

theorem tailTrace_4412164 : CollatzResearch.WordTrace tailWord_4412164 prefixEnd_4412164 2265560858464180621758833 := by
  unfold tailWord_4412164
  simp only [CollatzResearch.WordTrace]
  refine ⟨80462420793745420232057773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107283227724993893642743697 80462420793745420232057773)
  ·
    refine ⟨30173407797654532587021665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80462420793745420232057773 30173407797654532587021665)
    ·
      refine ⟨22630055848240899440266249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30173407797654532587021665 22630055848240899440266249)
      ·
        refine ⟨16972541886180674580199687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22630055848240899440266249 16972541886180674580199687)
        ·
          refine ⟨25458812829271011870299531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16972541886180674580199687 25458812829271011870299531)
          ·
            refine ⟨38188219243906517805449297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25458812829271011870299531 38188219243906517805449297)
            ·
              refine ⟨28641164432929888354086973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38188219243906517805449297 28641164432929888354086973)
              ·
                refine ⟨10740436662348708132782615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28641164432929888354086973 10740436662348708132782615)
                ·
                  refine ⟨16110654993523062199173923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10740436662348708132782615 16110654993523062199173923)
                  ·
                    refine ⟨24165982490284593298760885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16110654993523062199173923 24165982490284593298760885)
                    ·
                      refine ⟨2265560858464180621758833, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24165982490284593298760885 2265560858464180621758833)
                      ·
                        rfl

theorem cell23_4412164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 3, 1, 1, 5].length) (baseStart_4412164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412164 prefixEnd_4412164 := by exact prefixLift 4412164
  have htrace : WordTrace (prefixWord ++ tailWord_4412164) baseStart_4412164 baseEnd_4412164 := by
    simpa [prefixWord, tailWord_4412164, baseEnd_4412164] using wordTrace_append hprefix tailTrace_4412164
  have hstable : (prefixWord ++ tailWord_4412164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412164).length < 2 ^ (prefixWord ++ tailWord_4412164).sum := by decide
  have hdescent : baseEnd_4412164 < baseStart_4412164 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412188 : List Nat := [2, 2, 3, 1, 1, 4, 3, 1, 2, 4]
def baseStart_4412188 : Nat := 118140960795 + 4412188 * 2 ^ 59
def prefixEnd_4412188 : Nat := 4983230072969 + 3 ^ 40 * 4412188 * 2
def baseEnd_4412188 : Nat := 755191060666629509286241

theorem tailTrace_4412188 : CollatzResearch.WordTrace tailWord_4412188 prefixEnd_4412188 755191060666629509286241 := by
  unfold tailWord_4412188
  simp only [CollatzResearch.WordTrace]
  refine ⟨80462858469701946281494609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107283811292935928375326145 80462858469701946281494609)
  ·
    refine ⟨60347143852276459711120957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80462858469701946281494609 60347143852276459711120957)
    ·
      refine ⟨22630178944603672391670359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60347143852276459711120957 22630178944603672391670359)
      ·
        refine ⟨33945268416905508587505539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22630178944603672391670359 33945268416905508587505539)
        ·
          refine ⟨50917902625358262881258309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33945268416905508587505539 50917902625358262881258309)
          ·
            refine ⟨9547106742254674290235933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50917902625358262881258309 9547106742254674290235933)
            ·
              refine ⟨3580165028345502858838475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9547106742254674290235933 3580165028345502858838475)
              ·
                refine ⟨5370247542518254288257713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580165028345502858838475 5370247542518254288257713)
                ·
                  refine ⟨4027685656888690716193285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5370247542518254288257713 4027685656888690716193285)
                  ·
                    refine ⟨755191060666629509286241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027685656888690716193285 755191060666629509286241)
                    ·
                      rfl

theorem cell23_4412188_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_4412188 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412188 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412188 prefixEnd_4412188 := by exact prefixLift 4412188
  have htrace : WordTrace (prefixWord ++ tailWord_4412188) baseStart_4412188 baseEnd_4412188 := by
    simpa [prefixWord, tailWord_4412188, baseEnd_4412188] using wordTrace_append hprefix tailTrace_4412188
  have hstable : (prefixWord ++ tailWord_4412188).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412188).length < 2 ^ (prefixWord ++ tailWord_4412188).sum := by decide
  have hdescent : baseEnd_4412188 < baseStart_4412188 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412188) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412191 : List Nat := [1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 4]
def baseStart_4412191 : Nat := 118140960795 + 4412191 * 2 ^ 59
def prefixEnd_4412191 : Nat := 4983230072969 + 3 ^ 40 * 4412191 * 2
def baseEnd_4412191 : Nat := 2265574722441852016121209

theorem tailTrace_4412191 : CollatzResearch.WordTrace tailWord_4412191 prefixEnd_4412191 2265574722441852016121209 := by
  unfold tailWord_4412191
  simp only [CollatzResearch.WordTrace]
  refine ⟨160925826358393024075348427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107283884238928682716898951 160925826358393024075348427)
  ·
    refine ⟨241388739537589536113022641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160925826358393024075348427 241388739537589536113022641)
    ·
      refine ⟨181041554653192152084766981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241388739537589536113022641 181041554653192152084766981)
      ·
        refine ⟨33945291497473528515893809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181041554653192152084766981 33945291497473528515893809)
        ·
          refine ⟨25458968623105146386920357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33945291497473528515893809 25458968623105146386920357)
          ·
            refine ⟨4773556616832214947547567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25458968623105146386920357 4773556616832214947547567)
            ·
              refine ⟨7160334925248322421321351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773556616832214947547567 7160334925248322421321351)
              ·
                refine ⟨10740502387872483631982027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7160334925248322421321351 10740502387872483631982027)
                ·
                  refine ⟨16110753581808725447973041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10740502387872483631982027 16110753581808725447973041)
                  ·
                    refine ⟨12083065186356544085979781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16110753581808725447973041 12083065186356544085979781)
                    ·
                      refine ⟨2265574722441852016121209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12083065186356544085979781 2265574722441852016121209)
                      ·
                        rfl

theorem cell23_4412191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_4412191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412191 prefixEnd_4412191 := by exact prefixLift 4412191
  have htrace : WordTrace (prefixWord ++ tailWord_4412191) baseStart_4412191 baseEnd_4412191 := by
    simpa [prefixWord, tailWord_4412191, baseEnd_4412191] using wordTrace_append hprefix tailTrace_4412191
  have hstable : (prefixWord ++ tailWord_4412191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412191).length < 2 ^ (prefixWord ++ tailWord_4412191).sum := by decide
  have hdescent : baseEnd_4412191 < baseStart_4412191 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412211 : List Nat := [1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 3]
def baseStart_4412211 : Nat := 118140960795 + 4412211 * 2 ^ 59
def prefixEnd_4412211 : Nat := 4983230072969 + 3 ^ 40 * 4412211 * 2
def baseEnd_4412211 : Nat := 2265584992054941937871117

theorem tailTrace_4412211 : CollatzResearch.WordTrace tailWord_4412211 prefixEnd_4412211 2265584992054941937871117 := by
  unfold tailWord_4412211
  simp only [CollatzResearch.WordTrace]
  refine ⟨160926555818320567491076487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107284370545547044994050991 160926555818320567491076487)
  ·
    refine ⟨241389833727480851236614731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160926555818320567491076487 241389833727480851236614731)
    ·
      refine ⟨362084750591221276854922097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241389833727480851236614731 362084750591221276854922097)
      ·
        refine ⟨271563562943415957641191573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362084750591221276854922097 271563562943415957641191573)
        ·
          refine ⟨12729542012972623014430855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 271563562943415957641191573 12729542012972623014430855)
          ·
            refine ⟨19094313019458934521646283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12729542012972623014430855 19094313019458934521646283)
            ·
              refine ⟨28641469529188401782469425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19094313019458934521646283 28641469529188401782469425)
              ·
                refine ⟨21481102146891301336852069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28641469529188401782469425 21481102146891301336852069)
                ·
                  refine ⟨4027706652542119000659763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21481102146891301336852069 4027706652542119000659763)
                  ·
                    refine ⟨6041559978813178500989645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4027706652542119000659763 6041559978813178500989645)
                    ·
                      refine ⟨2265584992054941937871117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6041559978813178500989645 2265584992054941937871117)
                      ·
                        rfl

theorem cell23_4412211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 2, 4, 1, 3].length) (baseStart_4412211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412211 prefixEnd_4412211 := by exact prefixLift 4412211
  have htrace : WordTrace (prefixWord ++ tailWord_4412211) baseStart_4412211 baseEnd_4412211 := by
    simpa [prefixWord, tailWord_4412211, baseEnd_4412211] using wordTrace_append hprefix tailTrace_4412211
  have hstable : (prefixWord ++ tailWord_4412211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412211).length < 2 ^ (prefixWord ++ tailWord_4412211).sum := by decide
  have hdescent : baseEnd_4412211 < baseStart_4412211 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412284 : List Nat := [2, 2, 2, 1, 1, 1, 1, 2, 3, 5, 3]
def baseStart_4412284 : Nat := 118140960795 + 4412284 * 2 ^ 59
def prefixEnd_4412284 : Nat := 4983230072969 + 3 ^ 40 * 4412284 * 2
def baseEnd_4412284 : Nat := 2265622476142720152258281

theorem tailTrace_4412284 : CollatzResearch.WordTrace tailWord_4412284 prefixEnd_4412284 2265622476142720152258281 := by
  unfold tailWord_4412284
  simp only [CollatzResearch.WordTrace]
  refine ⟨80464609173528050479241953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107286145564704067305655937 80464609173528050479241953)
  ·
    refine ⟨60348456880146037859431465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80464609173528050479241953 60348456880146037859431465)
    ·
      refine ⟨45261342660109528394573599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60348456880146037859431465 45261342660109528394573599)
      ·
        refine ⟨67892013990164292591860399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45261342660109528394573599 67892013990164292591860399)
        ·
          refine ⟨101838020985246438887790599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67892013990164292591860399 101838020985246438887790599)
          ·
            refine ⟨152757031477869658331685899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101838020985246438887790599 152757031477869658331685899)
            ·
              refine ⟨229135547216804487497528849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152757031477869658331685899 229135547216804487497528849)
              ·
                refine ⟨171851660412603365623146637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229135547216804487497528849 171851660412603365623146637)
                ·
                  refine ⟨64444372654726262108679989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 171851660412603365623146637 64444372654726262108679989)
                  ·
                    refine ⟨6041659936380587072688749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 64444372654726262108679989 6041659936380587072688749)
                    ·
                      refine ⟨2265622476142720152258281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6041659936380587072688749 2265622476142720152258281)
                      ·
                        rfl

theorem cell23_4412284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 2, 3, 5, 3].length) (baseStart_4412284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412284 prefixEnd_4412284 := by exact prefixLift 4412284
  have htrace : WordTrace (prefixWord ++ tailWord_4412284) baseStart_4412284 baseEnd_4412284 := by
    simpa [prefixWord, tailWord_4412284, baseEnd_4412284] using wordTrace_append hprefix tailTrace_4412284
  have hstable : (prefixWord ++ tailWord_4412284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412284).length < 2 ^ (prefixWord ++ tailWord_4412284).sum := by decide
  have hdescent : baseEnd_4412284 < baseStart_4412284 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412291 : List Nat := [1, 1, 1, 3, 4, 1, 3, 4, 5]
def baseStart_4412291 : Nat := 118140960795 + 4412291 * 2 ^ 59
def prefixEnd_4412291 : Nat := 4983230072969 + 3 ^ 40 * 4412291 * 2
def baseEnd_4412291 : Nat := 251736230056366847207861

theorem tailTrace_4412291 : CollatzResearch.WordTrace tailWord_4412291 prefixEnd_4412291 251736230056366847207861 := by
  unfold tailWord_4412291
  simp only [CollatzResearch.WordTrace]
  refine ⟨160929473658030741153988727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107286315772020494102659151 160929473658030741153988727)
  ·
    refine ⟨241394210487046111730983091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160929473658030741153988727 241394210487046111730983091)
    ·
      refine ⟨362091315730569167596474637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241394210487046111730983091 362091315730569167596474637)
      ·
        refine ⟨135784243398963437848677989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362091315730569167596474637 135784243398963437848677989)
        ·
          refine ⟨25459545637305644596627123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135784243398963437848677989 25459545637305644596627123)
          ·
            refine ⟨38189318455958466894940685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25459545637305644596627123 38189318455958466894940685)
            ·
              refine ⟨14320994420984425085602757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38189318455958466894940685 14320994420984425085602757)
              ·
                refine ⟨2685186453934579703550517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14320994420984425085602757 2685186453934579703550517)
                ·
                  refine ⟨251736230056366847207861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2685186453934579703550517 251736230056366847207861)
                  ·
                    rfl

theorem cell23_4412291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 3, 4, 5].length) (baseStart_4412291 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412291 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412291 prefixEnd_4412291 := by exact prefixLift 4412291
  have htrace : WordTrace (prefixWord ++ tailWord_4412291) baseStart_4412291 baseEnd_4412291 := by
    simpa [prefixWord, tailWord_4412291, baseEnd_4412291] using wordTrace_append hprefix tailTrace_4412291
  have hstable : (prefixWord ++ tailWord_4412291).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412291).length < 2 ^ (prefixWord ++ tailWord_4412291).sum := by decide
  have hdescent : baseEnd_4412291 < baseStart_4412291 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412311 : List Nat := [1, 1, 3, 3, 1, 2, 1, 2, 2, 5, 2]
def baseStart_4412311 : Nat := 118140960795 + 4412311 * 2 ^ 59
def prefixEnd_4412311 : Nat := 4983230072969 + 3 ^ 40 * 4412311 * 2
def baseEnd_4412311 : Nat := 2265636340120391546620657

theorem tailTrace_4412311 : CollatzResearch.WordTrace tailWord_4412311 prefixEnd_4412311 2265636340120391546620657 := by
  unfold tailWord_4412311
  simp only [CollatzResearch.WordTrace]
  refine ⟨160930203117958284569716787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107286802078638856379811191 160930203117958284569716787)
  ·
    refine ⟨241395304676937426854575181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160930203117958284569716787 241395304676937426854575181)
    ·
      refine ⟨90523239253851535070465693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241395304676937426854575181 90523239253851535070465693)
      ·
        refine ⟨33946214720194325651424635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90523239253851535070465693 33946214720194325651424635)
        ·
          refine ⟨50919322080291488477136953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33946214720194325651424635 50919322080291488477136953)
          ·
            refine ⟨38189491560218616357852715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50919322080291488477136953 38189491560218616357852715)
            ·
              refine ⟨57284237340327924536779073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38189491560218616357852715 57284237340327924536779073)
              ·
                refine ⟨42963178005245943402584305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57284237340327924536779073 42963178005245943402584305)
                ·
                  refine ⟨32222383503934457551938229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42963178005245943402584305 32222383503934457551938229)
                  ·
                    refine ⟨3020848453493855395494209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32222383503934457551938229 3020848453493855395494209)
                    ·
                      refine ⟨2265636340120391546620657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020848453493855395494209 2265636340120391546620657)
                      ·
                        rfl

theorem cell23_4412311_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 1, 2, 2, 5, 2].length) (baseStart_4412311 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412311 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412311 prefixEnd_4412311 := by exact prefixLift 4412311
  have htrace : WordTrace (prefixWord ++ tailWord_4412311) baseStart_4412311 baseEnd_4412311 := by
    simpa [prefixWord, tailWord_4412311, baseEnd_4412311] using wordTrace_append hprefix tailTrace_4412311
  have hstable : (prefixWord ++ tailWord_4412311).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412311).length < 2 ^ (prefixWord ++ tailWord_4412311).sum := by decide
  have hdescent : baseEnd_4412311 < baseStart_4412311 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412311) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412321 : List Nat := [1, 2, 3, 4, 1, 2, 1, 1, 1, 7]
def baseStart_4412321 : Nat := 118140960795 + 4412321 * 2 ^ 59
def prefixEnd_4412321 : Nat := 4983230072969 + 3 ^ 40 * 4412321 * 2
def baseEnd_4412321 : Nat := 755213824975645502498537

theorem tailTrace_4412321 : CollatzResearch.WordTrace tailWord_4412321 prefixEnd_4412321 755213824975645502498537 := by
  unfold tailWord_4412321
  simp only [CollatzResearch.WordTrace]
  refine ⟨160930567847922056277580817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107287045231948037518387211 160930567847922056277580817)
  ·
    refine ⟨120697925885941542208185613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160930567847922056277580817 120697925885941542208185613)
    ·
      refine ⟨45261722207228078328069605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120697925885941542208185613 45261722207228078328069605)
      ·
        refine ⟨8486572913855264686513051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45261722207228078328069605 8486572913855264686513051)
        ·
          refine ⟨12729859370782897029769577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8486572913855264686513051 12729859370782897029769577)
          ·
            refine ⟨9547394528087172772327183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12729859370782897029769577 9547394528087172772327183)
            ·
              refine ⟨14321091792130759158490775, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9547394528087172772327183 14321091792130759158490775)
              ·
                refine ⟨21481637688196138737736163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14321091792130759158490775 21481637688196138737736163)
                ·
                  refine ⟨32222456532294208106604245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21481637688196138737736163 32222456532294208106604245)
                  ·
                    refine ⟨755213824975645502498537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32222456532294208106604245 755213824975645502498537)
                    ·
                      rfl

theorem cell23_4412321_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 1, 1, 7].length) (baseStart_4412321 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412321 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412321 prefixEnd_4412321 := by exact prefixLift 4412321
  have htrace : WordTrace (prefixWord ++ tailWord_4412321) baseStart_4412321 baseEnd_4412321 := by
    simpa [prefixWord, tailWord_4412321, baseEnd_4412321] using wordTrace_append hprefix tailTrace_4412321
  have hstable : (prefixWord ++ tailWord_4412321).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412321).length < 2 ^ (prefixWord ++ tailWord_4412321).sum := by decide
  have hdescent : baseEnd_4412321 < baseStart_4412321 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412321) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412341 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 4]
def baseStart_4412341 : Nat := 118140960795 + 4412341 * 2 ^ 59
def prefixEnd_4412341 : Nat := 4983230072969 + 3 ^ 40 * 4412341 * 2
def baseEnd_4412341 : Nat := 2265651744540026429245519

theorem tailTrace_4412341 : CollatzResearch.WordTrace tailWord_4412341 prefixEnd_4412341 2265651744540026429245519 := by
  unfold tailWord_4412341
  simp only [CollatzResearch.WordTrace]
  refine ⟨160931297307849599693308877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107287531538566399795539251 160931297307849599693308877)
  ·
    refine ⟨60349236490443599884990829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160931297307849599693308877 60349236490443599884990829)
    ·
      refine ⟨22630963683916349956871561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60349236490443599884990829 22630963683916349956871561)
      ·
        refine ⟨16973222762937262467653671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22630963683916349956871561 16973222762937262467653671)
        ·
          refine ⟨25459834144405893701480507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16973222762937262467653671 25459834144405893701480507)
          ·
            refine ⟨38189751216608840552220761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25459834144405893701480507 38189751216608840552220761)
            ·
              refine ⟨28642313412456630414165571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38189751216608840552220761 28642313412456630414165571)
              ·
                refine ⟨42963470118684945621248357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28642313412456630414165571 42963470118684945621248357)
                ·
                  refine ⟨8055650647253427303984067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42963470118684945621248357 8055650647253427303984067)
                  ·
                    refine ⟨12083475970880140955976101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8055650647253427303984067 12083475970880140955976101)
                    ·
                      refine ⟨2265651744540026429245519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12083475970880140955976101 2265651744540026429245519)
                      ·
                        rfl

theorem cell23_4412341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 4, 1, 4].length) (baseStart_4412341 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412341 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412341 prefixEnd_4412341 := by exact prefixLift 4412341
  have htrace : WordTrace (prefixWord ++ tailWord_4412341) baseStart_4412341 baseEnd_4412341 := by
    simpa [prefixWord, tailWord_4412341, baseEnd_4412341] using wordTrace_append hprefix tailTrace_4412341
  have hstable : (prefixWord ++ tailWord_4412341).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412341).length < 2 ^ (prefixWord ++ tailWord_4412341).sum := by decide
  have hdescent : baseEnd_4412341 < baseStart_4412341 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412342 : List Nat := [5, 1, 4, 1, 1, 1, 2, 1, 7]
def baseStart_4412342 : Nat := 118140960795 + 4412342 * 2 ^ 59
def prefixEnd_4412342 : Nat := 4983230072969 + 3 ^ 40 * 4412342 * 2
def baseEnd_4412342 : Nat := 251739139780075658370335

theorem tailTrace_4412342 : CollatzResearch.WordTrace tailWord_4412342 prefixEnd_4412342 251739139780075658370335 := by
  unfold tailWord_4412342
  simp only [CollatzResearch.WordTrace]
  refine ⟨10058208361302873554005955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107287555853897317909396853 10058208361302873554005955)
  ·
    refine ⟨15087312541954310331008933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10058208361302873554005955 15087312541954310331008933)
    ·
      refine ⟨2828871101616433187064175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15087312541954310331008933 2828871101616433187064175)
      ·
        refine ⟨4243306652424649780596263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2828871101616433187064175 4243306652424649780596263)
        ·
          refine ⟨6364959978636974670894395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243306652424649780596263 6364959978636974670894395)
          ·
            refine ⟨9547439967955462006341593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6364959978636974670894395 9547439967955462006341593)
            ·
              refine ⟨7160579975966596504756195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9547439967955462006341593 7160579975966596504756195)
              ·
                refine ⟨10740869963949894757134293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7160579975966596504756195 10740869963949894757134293)
                ·
                  refine ⟨251739139780075658370335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10740869963949894757134293 251739139780075658370335)
                  ·
                    rfl

theorem cell23_4412342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 1, 2, 1, 7].length) (baseStart_4412342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412342 prefixEnd_4412342 := by exact prefixLift 4412342
  have htrace : WordTrace (prefixWord ++ tailWord_4412342) baseStart_4412342 baseEnd_4412342 := by
    simpa [prefixWord, tailWord_4412342, baseEnd_4412342] using wordTrace_append hprefix tailTrace_4412342
  have hstable : (prefixWord ++ tailWord_4412342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412342).length < 2 ^ (prefixWord ++ tailWord_4412342).sum := by decide
  have hdescent : baseEnd_4412342 < baseStart_4412342 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412381 : List Nat := [1, 4, 3, 1, 2, 1, 1, 2, 8]
def baseStart_4412381 : Nat := 118140960795 + 4412381 * 2 ^ 59
def prefixEnd_4412381 : Nat := 4983230072969 + 3 ^ 40 * 4412381 * 2
def baseEnd_4412381 : Nat := 251741364862911808082815

theorem tailTrace_4412381 : CollatzResearch.WordTrace tailWord_4412381 prefixEnd_4412381 251741364862911808082815 := by
  unfold tailWord_4412381
  simp only [CollatzResearch.WordTrace]
  refine ⟨160932756227704686524764997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107288504151803124349843331 160932756227704686524764997)
  ·
    refine ⟨30174891792694628723393437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160932756227704686524764997 30174891792694628723393437)
    ·
      refine ⟨11315584422260485771272539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30174891792694628723393437 11315584422260485771272539)
      ·
        refine ⟨16973376633390728656908809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11315584422260485771272539 16973376633390728656908809)
        ·
          refine ⟨12730032475043046492681607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16973376633390728656908809 12730032475043046492681607)
          ·
            refine ⟨19095048712564569739022411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12730032475043046492681607 19095048712564569739022411)
            ·
              refine ⟨28642573068846854608533617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19095048712564569739022411 28642573068846854608533617)
              ·
                refine ⟨21481929801635140956400213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28642573068846854608533617 21481929801635140956400213)
                ·
                  refine ⟨251741364862911808082815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21481929801635140956400213 251741364862911808082815)
                  ·
                    rfl

theorem cell23_4412381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 2, 8].length) (baseStart_4412381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412381 prefixEnd_4412381 := by exact prefixLift 4412381
  have htrace : WordTrace (prefixWord ++ tailWord_4412381) baseStart_4412381 baseEnd_4412381 := by
    simpa [prefixWord, tailWord_4412381, baseEnd_4412381] using wordTrace_append hprefix tailTrace_4412381
  have hstable : (prefixWord ++ tailWord_4412381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412381).length < 2 ^ (prefixWord ++ tailWord_4412381).sum := by decide
  have hdescent : baseEnd_4412381 < baseStart_4412381 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412402 : List Nat := [3, 2, 1, 5, 1, 2, 1, 1, 3, 4]
def baseStart_4412402 : Nat := 118140960795 + 4412402 * 2 ^ 59
def prefixEnd_4412402 : Nat := 4983230072969 + 3 ^ 40 * 4412402 * 2
def baseEnd_4412402 : Nat := 755227688953316896860913

theorem tailTrace_4412402 : CollatzResearch.WordTrace tailWord_4412402 prefixEnd_4412402 755227688953316896860913 := by
  unfold tailWord_4412402
  simp only [CollatzResearch.WordTrace]
  refine ⟨40233380540157151777819865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107289014773752404740852973 40233380540157151777819865)
  ·
    refine ⟨30175035405117863833364899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40233380540157151777819865 30175035405117863833364899)
    ·
      refine ⟨45262553107676795750047349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30175035405117863833364899 45262553107676795750047349)
      ·
        refine ⟨4243364353844699601566939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45262553107676795750047349 4243364353844699601566939)
        ·
          refine ⟨6365046530767049402350409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4243364353844699601566939 6365046530767049402350409)
          ·
            refine ⟨4773784898075287051762807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6365046530767049402350409 4773784898075287051762807)
            ·
              refine ⟨7160677347112930577644211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773784898075287051762807 7160677347112930577644211)
              ·
                refine ⟨10741016020669395866466317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7160677347112930577644211 10741016020669395866466317)
                ·
                  refine ⟨4027881007751023449924869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10741016020669395866466317 4027881007751023449924869)
                  ·
                    refine ⟨755227688953316896860913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027881007751023449924869 755227688953316896860913)
                    ·
                      rfl

theorem cell23_4412402_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 5, 1, 2, 1, 1, 3, 4].length) (baseStart_4412402 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412402 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412402 prefixEnd_4412402 := by exact prefixLift 4412402
  have htrace : WordTrace (prefixWord ++ tailWord_4412402) baseStart_4412402 baseEnd_4412402 := by
    simpa [prefixWord, tailWord_4412402, baseEnd_4412402] using wordTrace_append hprefix tailTrace_4412402
  have hstable : (prefixWord ++ tailWord_4412402).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412402).length < 2 ^ (prefixWord ++ tailWord_4412402).sum := by decide
  have hdescent : baseEnd_4412402 < baseStart_4412402 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412402) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412428 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 1, 5]
def baseStart_4412428 : Nat := 118140960795 + 4412428 * 2 ^ 59
def prefixEnd_4412428 : Nat := 4983230072969 + 3 ^ 40 * 4412428 * 2
def baseEnd_4412428 : Nat := 755232139118989196285873

theorem tailTrace_4412428 : CollatzResearch.WordTrace tailWord_4412428 prefixEnd_4412428 755232139118989196285873 := by
  unfold tailWord_4412428
  simp only [CollatzResearch.WordTrace]
  refine ⟨80467235229267206775862969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107289646972356275701150625 80467235229267206775862969)
  ·
    refine ⟨60350426421950405081897227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80467235229267206775862969 60350426421950405081897227)
    ·
      refine ⟨90525639632925607622845841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60350426421950405081897227 90525639632925607622845841)
      ·
        refine ⟨67894229724694205717134381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90525639632925607622845841 67894229724694205717134381)
        ·
          refine ⟨25460336146760327143925393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67894229724694205717134381 25460336146760327143925393)
          ·
            refine ⟨19095252110070245357944045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25460336146760327143925393 19095252110070245357944045)
            ·
              refine ⟨7160719541276342009229017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19095252110070245357944045 7160719541276342009229017)
              ·
                refine ⟨5370539655957256506921763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7160719541276342009229017 5370539655957256506921763)
                ·
                  refine ⟨8055809483935884760382645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5370539655957256506921763 8055809483935884760382645)
                  ·
                    refine ⟨755232139118989196285873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8055809483935884760382645 755232139118989196285873)
                    ·
                      rfl

theorem cell23_4412428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 1, 5].length) (baseStart_4412428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412428 prefixEnd_4412428 := by exact prefixLift 4412428
  have htrace : WordTrace (prefixWord ++ tailWord_4412428) baseStart_4412428 baseEnd_4412428 := by
    simpa [prefixWord, tailWord_4412428, baseEnd_4412428] using wordTrace_append hprefix tailTrace_4412428
  have hstable : (prefixWord ++ tailWord_4412428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412428).length < 2 ^ (prefixWord ++ tailWord_4412428).sum := by decide
  have hdescent : baseEnd_4412428 < baseStart_4412428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412441 : List Nat := [1, 2, 1, 2, 1, 1, 4, 1, 6, 4]
def baseStart_4412441 : Nat := 118140960795 + 4412441 * 2 ^ 59
def prefixEnd_4412441 : Nat := 4983230072969 + 3 ^ 40 * 4412441 * 2
def baseEnd_4412441 : Nat := 755234364201825345998353

theorem tailTrace_4412441 : CollatzResearch.WordTrace tailWord_4412441 prefixEnd_4412441 755234364201825345998353 := by
  unfold tailWord_4412441
  simp only [CollatzResearch.WordTrace]
  refine ⟨160934944607487316771949177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107289963071658211181299451 160934944607487316771949177)
  ·
    refine ⟨120701208455615487578961883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160934944607487316771949177 120701208455615487578961883)
    ·
      refine ⟨181051812683423231368442825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120701208455615487578961883 181051812683423231368442825)
      ·
        refine ⟨135788859512567423526332119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181051812683423231368442825 135788859512567423526332119)
        ·
          refine ⟨203683289268851135289498179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135788859512567423526332119 203683289268851135289498179)
          ·
            refine ⟨305524933903276702934247269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203683289268851135289498179 305524933903276702934247269)
            ·
              refine ⟨57285925106864381800171363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305524933903276702934247269 57285925106864381800171363)
              ·
                refine ⟨85928887660296572700257045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57285925106864381800171363 85928887660296572700257045)
                ·
                  refine ⟨4027916609076401845324549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 85928887660296572700257045 4027916609076401845324549)
                  ·
                    refine ⟨755234364201825345998353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027916609076401845324549 755234364201825345998353)
                    ·
                      rfl

theorem cell23_4412441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 4, 1, 6, 4].length) (baseStart_4412441 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412441 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412441 prefixEnd_4412441 := by exact prefixLift 4412441
  have htrace : WordTrace (prefixWord ++ tailWord_4412441) baseStart_4412441 baseEnd_4412441 := by
    simpa [prefixWord, tailWord_4412441, baseEnd_4412441] using wordTrace_append hprefix tailTrace_4412441
  have hstable : (prefixWord ++ tailWord_4412441).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412441).length < 2 ^ (prefixWord ++ tailWord_4412441).sum := by decide
  have hdescent : baseEnd_4412441 < baseStart_4412441 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412465 : List Nat := [1, 2, 2, 3, 1, 2, 2, 3, 3, 2, 2]
def baseStart_4412465 : Nat := 118140960795 + 4412465 * 2 ^ 59
def prefixEnd_4412465 : Nat := 4983230072969 + 3 ^ 40 * 4412465 * 2
def baseEnd_4412465 : Nat := 2265715416141183944094949

theorem tailTrace_4412465 : CollatzResearch.WordTrace tailWord_4412465 prefixEnd_4412465 2265715416141183944094949 := by
  unfold tailWord_4412465
  simp only [CollatzResearch.WordTrace]
  refine ⟨160935819959400368870822849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107290546639600245913881899 160935819959400368870822849)
  ·
    refine ⟨120701864969550276653117137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160935819959400368870822849 120701864969550276653117137)
    ·
      refine ⟨90526398727162707489837853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120701864969550276653117137 90526398727162707489837853)
      ·
        refine ⟨33947399522686015308689195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90526398727162707489837853 33947399522686015308689195)
        ·
          refine ⟨50921099284029022963033793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33947399522686015308689195 50921099284029022963033793)
          ·
            refine ⟨38190824463021767222275345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50921099284029022963033793 38190824463021767222275345)
            ·
              refine ⟨28643118347266325416706509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38190824463021767222275345 28643118347266325416706509)
              ·
                refine ⟨10741169380224872031264941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28643118347266325416706509 10741169380224872031264941)
                ·
                  refine ⟨4027938517584327011724353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10741169380224872031264941 4027938517584327011724353)
                  ·
                    refine ⟨3020953888188245258793265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4027938517584327011724353 3020953888188245258793265)
                    ·
                      refine ⟨2265715416141183944094949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3020953888188245258793265 2265715416141183944094949)
                      ·
                        rfl

theorem cell23_4412465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 3, 3, 2, 2].length) (baseStart_4412465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412465 prefixEnd_4412465 := by exact prefixLift 4412465
  have htrace : WordTrace (prefixWord ++ tailWord_4412465) baseStart_4412465 baseEnd_4412465 := by
    simpa [prefixWord, tailWord_4412465, baseEnd_4412465] using wordTrace_append hprefix tailTrace_4412465
  have hstable : (prefixWord ++ tailWord_4412465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412465).length < 2 ^ (prefixWord ++ tailWord_4412465).sum := by decide
  have hdescent : baseEnd_4412465 < baseStart_4412465 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412509 : List Nat := [1, 4, 4, 1, 2, 2, 1, 2, 2, 4]
def baseStart_4412509 : Nat := 118140960795 + 4412509 * 2 ^ 59
def prefixEnd_4412509 : Nat := 4983230072969 + 3 ^ 40 * 4412509 * 2
def baseEnd_4412509 : Nat := 755246003096660590648249

theorem tailTrace_4412509 : CollatzResearch.WordTrace tailWord_4412509 prefixEnd_4412509 755246003096660590648249 := by
  unfold tailWord_4412509
  simp only [CollatzResearch.WordTrace]
  refine ⟨160937424771240964385424581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107291616514160642923616387 160937424771240964385424581)
  ·
    refine ⟨30175767144607680822267109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160937424771240964385424581 30175767144607680822267109)
    ·
      refine ⟨5657956339613940154175083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30175767144607680822267109 5657956339613940154175083)
      ·
        refine ⟨8486934509420910231262625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5657956339613940154175083 8486934509420910231262625)
        ·
          refine ⟨6365200882065682673446969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8486934509420910231262625 6365200882065682673446969)
          ·
            refine ⟨4773900661549262005085227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6365200882065682673446969 4773900661549262005085227)
            ·
              refine ⟨7160850992323893007627841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4773900661549262005085227 7160850992323893007627841)
              ·
                refine ⟨5370638244242919755720881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7160850992323893007627841 5370638244242919755720881)
                ·
                  refine ⟨4027978683182189816790661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5370638244242919755720881 4027978683182189816790661)
                  ·
                    refine ⟨755246003096660590648249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4027978683182189816790661 755246003096660590648249)
                    ·
                      rfl

theorem cell23_4412509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 1, 2, 2, 4].length) (baseStart_4412509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412509 prefixEnd_4412509 := by exact prefixLift 4412509
  have htrace : WordTrace (prefixWord ++ tailWord_4412509) baseStart_4412509 baseEnd_4412509 := by
    simpa [prefixWord, tailWord_4412509, baseEnd_4412509] using wordTrace_append hprefix tailTrace_4412509
  have hstable : (prefixWord ++ tailWord_4412509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412509).length < 2 ^ (prefixWord ++ tailWord_4412509).sum := by decide
  have hdescent : baseEnd_4412509 < baseStart_4412509 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412558 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_4412558 : Nat := 118140960795 + 4412558 * 2 ^ 59
def prefixEnd_4412558 : Nat := 4983230072969 + 3 ^ 40 * 4412558 * 2
def baseEnd_4412558 : Nat := 2265763169842052080232021

theorem tailTrace_4412558 : CollatzResearch.WordTrace tailWord_4412558 prefixEnd_4412558 2265763169842052080232021 := by
  unfold tailWord_4412558
  simp only [CollatzResearch.WordTrace]
  refine ⟨20117401493507930719244791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107292807965375630502638885 20117401493507930719244791)
  ·
    refine ⟨30176102240261896078867187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20117401493507930719244791 30176102240261896078867187)
    ·
      refine ⟨45264153360392844118300781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30176102240261896078867187 45264153360392844118300781)
      ·
        refine ⟨16974057510147316544362793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45264153360392844118300781 16974057510147316544362793)
        ·
          refine ⟨12730543132610487408272095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16974057510147316544362793 12730543132610487408272095)
          ·
            refine ⟨19095814698915731112408143, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12730543132610487408272095 19095814698915731112408143)
            ·
              refine ⟨28643722048373596668612215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19095814698915731112408143 28643722048373596668612215)
              ·
                refine ⟨42965583072560395002918323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28643722048373596668612215 42965583072560395002918323)
                ·
                  refine ⟨64448374608840592504377485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42965583072560395002918323 64448374608840592504377485)
                  ·
                    refine ⟨24168140478315222189141557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64448374608840592504377485 24168140478315222189141557)
                    ·
                      refine ⟨2265763169842052080232021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24168140478315222189141557 2265763169842052080232021)
                      ·
                        rfl

theorem cell23_4412558_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_4412558 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412558 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412558 prefixEnd_4412558 := by exact prefixLift 4412558
  have htrace : WordTrace (prefixWord ++ tailWord_4412558) baseStart_4412558 baseEnd_4412558 := by
    simpa [prefixWord, tailWord_4412558, baseEnd_4412558] using wordTrace_append hprefix tailTrace_4412558
  have hstable : (prefixWord ++ tailWord_4412558).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412558).length < 2 ^ (prefixWord ++ tailWord_4412558).sum := by decide
  have hdescent : baseEnd_4412558 < baseStart_4412558 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412558) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412572 : List Nat := [2, 2, 3, 2, 1, 2, 2, 1, 4, 2, 2]
def baseStart_4412572 : Nat := 118140960795 + 4412572 * 2 ^ 59
def prefixEnd_4412572 : Nat := 4983230072969 + 3 ^ 40 * 4412572 * 2
def baseEnd_4412572 : Nat := 2265770358571215025456957

theorem tailTrace_4412572 : CollatzResearch.WordTrace tailWord_4412572 prefixEnd_4412572 2265770358571215025456957 := by
  unfold tailWord_4412572
  simp only [CollatzResearch.WordTrace]
  refine ⟨80469861285006363072483985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107293148380008484096645313 80469861285006363072483985)
  ·
    refine ⟨60352395963754772304362989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80469861285006363072483985 60352395963754772304362989)
    ·
      refine ⟨22632148486408039614136121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60352395963754772304362989 22632148486408039614136121)
      ·
        refine ⟨16974111364806029710602091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22632148486408039614136121 16974111364806029710602091)
        ·
          refine ⟨25461167047209044565903137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16974111364806029710602091 25461167047209044565903137)
          ·
            refine ⟨19095875285406783424427353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25461167047209044565903137 19095875285406783424427353)
            ·
              refine ⟨14321906464055087568320515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19095875285406783424427353 14321906464055087568320515)
              ·
                refine ⟨21482859696082631352480773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14321906464055087568320515 21482859696082631352480773)
                ·
                  refine ⟨4028036193015493378590145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21482859696082631352480773 4028036193015493378590145)
                  ·
                    refine ⟨3021027144761620033942609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028036193015493378590145 3021027144761620033942609)
                    ·
                      refine ⟨2265770358571215025456957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021027144761620033942609 2265770358571215025456957)
                      ·
                        rfl

theorem cell23_4412572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 1, 4, 2, 2].length) (baseStart_4412572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412572 prefixEnd_4412572 := by exact prefixLift 4412572
  have htrace : WordTrace (prefixWord ++ tailWord_4412572) baseStart_4412572 baseEnd_4412572 := by
    simpa [prefixWord, tailWord_4412572, baseEnd_4412572] using wordTrace_append hprefix tailTrace_4412572
  have hstable : (prefixWord ++ tailWord_4412572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412572).length < 2 ^ (prefixWord ++ tailWord_4412572).sum := by decide
  have hdescent : baseEnd_4412572 < baseStart_4412572 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412591 : List Nat := [1, 1, 2, 1, 2, 3, 2, 1, 3, 7]
def baseStart_4412591 : Nat := 118140960795 + 4412591 * 2 ^ 59
def prefixEnd_4412591 : Nat := 4983230072969 + 3 ^ 40 * 4412591 * 2
def baseEnd_4412591 : Nat := 755260038234550150373123

theorem tailTrace_4412591 : CollatzResearch.WordTrace tailWord_4412591 prefixEnd_4412591 755260038234550150373123 := by
  unfold tailWord_4412591
  simp only [CollatzResearch.WordTrace]
  refine ⟨160940415556943892389909627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107293610371295928259939751 160940415556943892389909627)
  ·
    refine ⟨241410623335415838584864441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160940415556943892389909627 241410623335415838584864441)
    ·
      refine ⟨181057967501561878938648331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241410623335415838584864441 181057967501561878938648331)
      ·
        refine ⟨271586951252342818407972497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181057967501561878938648331 271586951252342818407972497)
        ·
          refine ⟨203690213439257113805979373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271586951252342818407972497 203690213439257113805979373)
          ·
            refine ⟨76383830039721417677242265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203690213439257113805979373 76383830039721417677242265)
            ·
              refine ⟨57287872529791063257931699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76383830039721417677242265 57287872529791063257931699)
              ·
                refine ⟨85931808794686594886897549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57287872529791063257931699 85931808794686594886897549)
                ·
                  refine ⟨32224428298007473082586581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85931808794686594886897549 32224428298007473082586581)
                  ·
                    refine ⟨755260038234550150373123, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32224428298007473082586581 755260038234550150373123)
                    ·
                      rfl

theorem cell23_4412591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 1, 3, 7].length) (baseStart_4412591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412591 prefixEnd_4412591 := by exact prefixLift 4412591
  have htrace : WordTrace (prefixWord ++ tailWord_4412591) baseStart_4412591 baseEnd_4412591 := by
    simpa [prefixWord, tailWord_4412591, baseEnd_4412591] using wordTrace_append hprefix tailTrace_4412591
  have hstable : (prefixWord ++ tailWord_4412591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412591).length < 2 ^ (prefixWord ++ tailWord_4412591).sum := by decide
  have hdescent : baseEnd_4412591 < baseStart_4412591 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412618 : List Nat := [3, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5]
def baseStart_4412618 : Nat := 118140960795 + 4412618 * 2 ^ 59
def prefixEnd_4412618 : Nat := 4983230072969 + 3 ^ 40 * 4412618 * 2
def baseEnd_4412618 : Nat := 2265793978681321845481745

theorem tailTrace_4412618 : CollatzResearch.WordTrace tailWord_4412618 prefixEnd_4412618 2265793978681321845481745 := by
  unfold tailWord_4412618
  simp only [CollatzResearch.WordTrace]
  refine ⟨40235350081961519000285627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107294266885230717334095005 40235350081961519000285627)
  ·
    refine ⟨60353025122942278500428441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40235350081961519000285627 60353025122942278500428441)
    ·
      refine ⟨45264768842206708875321331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60353025122942278500428441 45264768842206708875321331)
      ·
        refine ⟨67897153263310063312981997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45264768842206708875321331 67897153263310063312981997)
        ·
          refine ⟨25461432473741273742368249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67897153263310063312981997 25461432473741273742368249)
          ·
            refine ⟨19096074355305955306776187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25461432473741273742368249 19096074355305955306776187)
            ·
              refine ⟨28644111532958932960164281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19096074355305955306776187 28644111532958932960164281)
              ·
                refine ⟨21483083649719199720123211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28644111532958932960164281 21483083649719199720123211)
                ·
                  refine ⟨32224625474578799580184817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21483083649719199720123211 32224625474578799580184817)
                  ·
                    refine ⟨24168469105934099685138613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32224625474578799580184817 24168469105934099685138613)
                    ·
                      refine ⟨2265793978681321845481745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24168469105934099685138613 2265793978681321845481745)
                      ·
                        rfl

theorem cell23_4412618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 2, 1, 2, 1, 2, 5].length) (baseStart_4412618 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412618 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412618 prefixEnd_4412618 := by exact prefixLift 4412618
  have htrace : WordTrace (prefixWord ++ tailWord_4412618) baseStart_4412618 baseEnd_4412618 := by
    simpa [prefixWord, tailWord_4412618, baseEnd_4412618] using wordTrace_append hprefix tailTrace_4412618
  have hstable : (prefixWord ++ tailWord_4412618).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412618).length < 2 ^ (prefixWord ++ tailWord_4412618).sum := by decide
  have hdescent : baseEnd_4412618 < baseStart_4412618 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412629 : List Nat := [1, 3, 2, 4, 1, 3, 2, 2, 5]
def baseStart_4412629 : Nat := 118140960795 + 4412629 * 2 ^ 59
def prefixEnd_4412629 : Nat := 4983230072969 + 3 ^ 40 * 4412629 * 2
def baseEnd_4412629 : Nat := 251755514107613478049355

theorem tailTrace_4412629 : CollatzResearch.WordTrace tailWord_4412629 prefixEnd_4412629 251755514107613478049355 := by
  unfold tailWord_4412629
  simp only [CollatzResearch.WordTrace]
  refine ⟨160941801530806224879792941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107294534353870816586528627 160941801530806224879792941)
  ·
    refine ⟨60353175574052334329922353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160941801530806224879792941 60353175574052334329922353)
    ·
      refine ⟨45264881680539250747441765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60353175574052334329922353 45264881680539250747441765)
      ·
        refine ⟨8487165315101109515145331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45264881680539250747441765 8487165315101109515145331)
        ·
          refine ⟨12730747972651664272717997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8487165315101109515145331 12730747972651664272717997)
          ·
            refine ⟨4774030489744374102269249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12730747972651664272717997 4774030489744374102269249)
            ·
              refine ⟨3580522867308280576701937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4774030489744374102269249 3580522867308280576701937)
              ·
                refine ⟨2685392150481210432526453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580522867308280576701937 2685392150481210432526453)
                ·
                  refine ⟨251755514107613478049355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2685392150481210432526453 251755514107613478049355)
                  ·
                    rfl

theorem cell23_4412629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 3, 2, 2, 5].length) (baseStart_4412629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412629 prefixEnd_4412629 := by exact prefixLift 4412629
  have htrace : WordTrace (prefixWord ++ tailWord_4412629) baseStart_4412629 baseEnd_4412629 := by
    simpa [prefixWord, tailWord_4412629, baseEnd_4412629] using wordTrace_append hprefix tailTrace_4412629
  have hstable : (prefixWord ++ tailWord_4412629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412629).length < 2 ^ (prefixWord ++ tailWord_4412629).sum := by decide
  have hdescent : baseEnd_4412629 < baseStart_4412629 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412722 : List Nat := [3, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2]
def baseStart_4412722 : Nat := 118140960795 + 4412722 * 2 ^ 59
def prefixEnd_4412722 : Nat := 4983230072969 + 3 ^ 40 * 4412722 * 2
def baseEnd_4412722 : Nat := 2265847380669389438581267

theorem tailTrace_4412722 : CollatzResearch.WordTrace tailWord_4412722 prefixEnd_4412722 2265847380669389438581267 := by
  unfold tailWord_4412722
  simp only [CollatzResearch.WordTrace]
  refine ⟨40236298379867325440732105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107296795679646201175285613 40236298379867325440732105)
  ·
    refine ⟨30177223784900494080549079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40236298379867325440732105 30177223784900494080549079)
    ·
      refine ⟨45265835677350741120823619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30177223784900494080549079 45265835677350741120823619)
      ·
        refine ⟨67898753516026111681235429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45265835677350741120823619 67898753516026111681235429)
        ·
          refine ⟨12731016284254895940231643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 67898753516026111681235429 12731016284254895940231643)
          ·
            refine ⟨19096524426382343910347465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12731016284254895940231643 19096524426382343910347465)
            ·
              refine ⟨14322393319786757932760599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19096524426382343910347465 14322393319786757932760599)
              ·
                refine ⟨21483589979680136899140899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14322393319786757932760599 21483589979680136899140899)
                ·
                  refine ⟨32225384969520205348711349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21483589979680136899140899 32225384969520205348711349)
                  ·
                    refine ⟨3021129840892519251441689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32225384969520205348711349 3021129840892519251441689)
                    ·
                      refine ⟨2265847380669389438581267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021129840892519251441689 2265847380669389438581267)
                      ·
                        rfl

theorem cell23_4412722_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 1, 1, 5, 2].length) (baseStart_4412722 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412722 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412722 prefixEnd_4412722 := by exact prefixLift 4412722
  have htrace : WordTrace (prefixWord ++ tailWord_4412722) baseStart_4412722 baseEnd_4412722 := by
    simpa [prefixWord, tailWord_4412722, baseEnd_4412722] using wordTrace_append hprefix tailTrace_4412722
  have hstable : (prefixWord ++ tailWord_4412722).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412722).length < 2 ^ (prefixWord ++ tailWord_4412722).sum := by decide
  have hdescent : baseEnd_4412722 < baseStart_4412722 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412722) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412728 : List Nat := [2, 1, 2, 1, 3, 1, 1, 3, 3, 6]
def baseStart_4412728 : Nat := 118140960795 + 4412728 * 2 ^ 59
def prefixEnd_4412728 : Nat := 4983230072969 + 3 ^ 40 * 4412728 * 2
def baseEnd_4412728 : Nat := 755283487184438805035413

theorem tailTrace_4412728 : CollatzResearch.WordTrace tailWord_4412728 prefixEnd_4412728 755283487184438805035413 := by
  unfold tailWord_4412728
  simp only [CollatzResearch.WordTrace]
  refine ⟨80472706178723782393823419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107296941571631709858431225 80472706178723782393823419)
  ·
    refine ⟨120709059268085673590735129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80472706178723782393823419 120709059268085673590735129)
    ·
      refine ⟨90531794451064255193051347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120709059268085673590735129 90531794451064255193051347)
      ·
        refine ⟨135797691676596382789577021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90531794451064255193051347 135797691676596382789577021)
        ·
          refine ⟨50924134378723643546091383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135797691676596382789577021 50924134378723643546091383)
          ·
            refine ⟨76386201568085465319137075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50924134378723643546091383 76386201568085465319137075)
            ·
              refine ⟨114579302352128197978705613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76386201568085465319137075 114579302352128197978705613)
              ·
                refine ⟨42967238382048074242014605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114579302352128197978705613 42967238382048074242014605)
                ·
                  refine ⟨16112714393268027840755477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42967238382048074242014605 16112714393268027840755477)
                  ·
                    refine ⟨755283487184438805035413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16112714393268027840755477 755283487184438805035413)
                    ·
                      rfl

theorem cell23_4412728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 1, 3, 3, 6].length) (baseStart_4412728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412728 prefixEnd_4412728 := by exact prefixLift 4412728
  have htrace : WordTrace (prefixWord ++ tailWord_4412728) baseStart_4412728 baseEnd_4412728 := by
    simpa [prefixWord, tailWord_4412728, baseEnd_4412728] using wordTrace_append hprefix tailTrace_4412728
  have hstable : (prefixWord ++ tailWord_4412728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412728).length < 2 ^ (prefixWord ++ tailWord_4412728).sum := by decide
  have hdescent : baseEnd_4412728 < baseStart_4412728 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412745 : List Nat := [1, 2, 1, 1, 2, 3, 4, 1, 4, 4]
def baseStart_4412745 : Nat := 118140960795 + 4412745 * 2 ^ 59
def prefixEnd_4412745 : Nat := 4983230072969 + 3 ^ 40 * 4412745 * 2
def baseEnd_4412745 : Nat := 755286396908147616197887

theorem tailTrace_4412745 : CollatzResearch.WordTrace tailWord_4412745 prefixEnd_4412745 755286396908147616197887 := by
  unfold tailWord_4412745
  simp only [CollatzResearch.WordTrace]
  refine ⟨160946032398385976691015689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107297354932257317794010459 160946032398385976691015689)
  ·
    refine ⟨120709524298789482518261767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160946032398385976691015689 120709524298789482518261767)
    ·
      refine ⟨181064286448184223777392651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120709524298789482518261767 181064286448184223777392651)
      ·
        refine ⟨271596429672276335666088977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181064286448184223777392651 271596429672276335666088977)
        ·
          refine ⟨203697322254207251749566733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271596429672276335666088977 203697322254207251749566733)
          ·
            refine ⟨76386495845327719406087525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203697322254207251749566733 76386495845327719406087525)
            ·
              refine ⟨14322467970998947388641411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76386495845327719406087525 14322467970998947388641411)
              ·
                refine ⟨21483701956498421082962117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14322467970998947388641411 21483701956498421082962117)
                ·
                  refine ⟨4028194116843453953055397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21483701956498421082962117 4028194116843453953055397)
                  ·
                    refine ⟨755286396908147616197887, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4028194116843453953055397 755286396908147616197887)
                    ·
                      rfl

theorem cell23_4412745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 1, 4, 4].length) (baseStart_4412745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412745 prefixEnd_4412745 := by exact prefixLift 4412745
  have htrace : WordTrace (prefixWord ++ tailWord_4412745) baseStart_4412745 baseEnd_4412745 := by
    simpa [prefixWord, tailWord_4412745, baseEnd_4412745] using wordTrace_append hprefix tailTrace_4412745
  have hstable : (prefixWord ++ tailWord_4412745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412745).length < 2 ^ (prefixWord ++ tailWord_4412745).sum := by decide
  have hdescent : baseEnd_4412745 < baseStart_4412745 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412755 : List Nat := [1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 3]
def baseStart_4412755 : Nat := 118140960795 + 4412755 * 2 ^ 59
def prefixEnd_4412755 : Nat := 4983230072969 + 3 ^ 40 * 4412755 * 2
def baseEnd_4412755 : Nat := 2265864325530987809468615

theorem tailTrace_4412755 : CollatzResearch.WordTrace tailWord_4412755 prefixEnd_4412755 2265864325530987809468615 := by
  unfold tailWord_4412755
  simp only [CollatzResearch.WordTrace]
  refine ⟨160946397128349748398879719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107297598085566498932586479 160946397128349748398879719)
  ·
    refine ⟨241419595692524622598319579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160946397128349748398879719 241419595692524622598319579)
    ·
      refine ⟨362129393538786933897479369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241419595692524622598319579 362129393538786933897479369)
      ·
        refine ⟨271597045154090200423109527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362129393538786933897479369 271597045154090200423109527)
        ·
          refine ⟨407395567731135300634664291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271597045154090200423109527 407395567731135300634664291)
          ·
            refine ⟨611093351596702950951996437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407395567731135300634664291 611093351596702950951996437)
            ·
              refine ⟨28645000856095450825874833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 611093351596702950951996437 28645000856095450825874833)
              ·
                refine ⟨21483750642071588119406125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28645000856095450825874833 21483750642071588119406125)
                ·
                  refine ⟨8056406490776845544777297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21483750642071588119406125 8056406490776845544777297)
                  ·
                    refine ⟨6042304868082634158582973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8056406490776845544777297 6042304868082634158582973)
                    ·
                      refine ⟨2265864325530987809468615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6042304868082634158582973 2265864325530987809468615)
                      ·
                        rfl

theorem cell23_4412755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 2, 3, 2, 3].length) (baseStart_4412755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412755 prefixEnd_4412755 := by exact prefixLift 4412755
  have htrace : WordTrace (prefixWord ++ tailWord_4412755) baseStart_4412755 baseEnd_4412755 := by
    simpa [prefixWord, tailWord_4412755, baseEnd_4412755] using wordTrace_append hprefix tailTrace_4412755
  have hstable : (prefixWord ++ tailWord_4412755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412755).length < 2 ^ (prefixWord ++ tailWord_4412755).sum := by decide
  have hdescent : baseEnd_4412755 < baseStart_4412755 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412772 : List Nat := [2, 3, 1, 1, 3, 3, 1, 1, 3, 2, 3]
def baseStart_4412772 : Nat := 118140960795 + 4412772 * 2 ^ 59
def prefixEnd_4412772 : Nat := 4983230072969 + 3 ^ 40 * 4412772 * 2
def baseEnd_4412772 : Nat := 2265873054702114242956037

theorem tailTrace_4412772 : CollatzResearch.WordTrace tailWord_4412772 prefixEnd_4412772 2265873054702114242956037 := by
  unfold tailWord_4412772
  simp only [CollatzResearch.WordTrace]
  refine ⟨80473508584644080151124285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107298011446192106868165713 80473508584644080151124285)
  ·
    refine ⟨30177565719241530056671607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80473508584644080151124285 30177565719241530056671607)
    ·
      refine ⟨45266348578862295085007411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30177565719241530056671607 45266348578862295085007411)
      ·
        refine ⟨67899522868293442627511117, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45266348578862295085007411 67899522868293442627511117)
        ·
          refine ⟨25462321075610040985316669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67899522868293442627511117 25462321075610040985316669)
          ·
            refine ⟨9548370403353765369493751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25462321075610040985316669 9548370403353765369493751)
            ·
              refine ⟨14322555605030648054240627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9548370403353765369493751 14322555605030648054240627)
              ·
                refine ⟨21483833407545972081360941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14322555605030648054240627 21483833407545972081360941)
                ·
                  refine ⟨8056437527829739530510353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21483833407545972081360941 8056437527829739530510353)
                  ·
                    refine ⟨6042328145872304647882765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8056437527829739530510353 6042328145872304647882765)
                    ·
                      refine ⟨2265873054702114242956037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6042328145872304647882765 2265873054702114242956037)
                      ·
                        rfl

theorem cell23_4412772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 1, 3, 2, 3].length) (baseStart_4412772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412772 prefixEnd_4412772 := by exact prefixLift 4412772
  have htrace : WordTrace (prefixWord ++ tailWord_4412772) baseStart_4412772 baseEnd_4412772 := by
    simpa [prefixWord, tailWord_4412772, baseEnd_4412772] using wordTrace_append hprefix tailTrace_4412772
  have hstable : (prefixWord ++ tailWord_4412772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412772).length < 2 ^ (prefixWord ++ tailWord_4412772).sum := by decide
  have hdescent : baseEnd_4412772 < baseStart_4412772 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412785 : List Nat := [1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 3]
def baseStart_4412785 : Nat := 118140960795 + 4412785 * 2 ^ 59
def prefixEnd_4412785 : Nat := 4983230072969 + 3 ^ 40 * 4412785 * 2
def baseEnd_4412785 : Nat := 2265879729950622692093477

theorem tailTrace_4412785 : CollatzResearch.WordTrace tailWord_4412785 prefixEnd_4412785 2265879729950622692093477 := by
  unfold tailWord_4412785
  simp only [CollatzResearch.WordTrace]
  refine ⟨160947491318241063522471809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107298327545494042348314539 160947491318241063522471809)
  ·
    refine ⟨120710618488680797641853857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160947491318241063522471809 120710618488680797641853857)
    ·
      refine ⟨90532963866510598231390393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120710618488680797641853857 90532963866510598231390393)
      ·
        refine ⟨67899722899882948673542795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90532963866510598231390393 67899722899882948673542795)
        ·
          refine ⟨101849584349824423010314193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67899722899882948673542795 101849584349824423010314193)
          ·
            refine ⟨76387188262368317257735645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101849584349824423010314193 76387188262368317257735645)
            ·
              refine ⟨28645195598388118971650867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76387188262368317257735645 28645195598388118971650867)
              ·
                refine ⟨42967793397582178457476301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28645195598388118971650867 42967793397582178457476301)
                ·
                  refine ⟨16112922524093316921553613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42967793397582178457476301 16112922524093316921553613)
                  ·
                    refine ⟨6042345946534993845582605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16112922524093316921553613 6042345946534993845582605)
                    ·
                      refine ⟨2265879729950622692093477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6042345946534993845582605 2265879729950622692093477)
                      ·
                        rfl

theorem cell23_4412785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_4412785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412785 prefixEnd_4412785 := by exact prefixLift 4412785
  have htrace : WordTrace (prefixWord ++ tailWord_4412785) baseStart_4412785 baseEnd_4412785 := by
    simpa [prefixWord, tailWord_4412785, baseEnd_4412785] using wordTrace_append hprefix tailTrace_4412785
  have hstable : (prefixWord ++ tailWord_4412785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412785).length < 2 ^ (prefixWord ++ tailWord_4412785).sum := by decide
  have hdescent : baseEnd_4412785 < baseStart_4412785 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412786 : List Nat := [3, 2, 1, 2, 1, 2, 2, 5, 1, 2, 2]
def baseStart_4412786 : Nat := 118140960795 + 4412786 * 2 ^ 59
def prefixEnd_4412786 : Nat := 4983230072969 + 3 ^ 40 * 4412786 * 2
def baseEnd_4412786 : Nat := 2265880243431277188180973

theorem tailTrace_4412786 : CollatzResearch.WordTrace tailWord_4412786 prefixEnd_4412786 2265880243431277188180973 := by
  unfold tailWord_4412786
  simp only [CollatzResearch.WordTrace]
  refine ⟨40236881947809360173314553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107298351860824960462172141 40236881947809360173314553)
  ·
    refine ⟨30177661460857020129985915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40236881947809360173314553 30177661460857020129985915)
    ·
      refine ⟨45266492191285530194978873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30177661460857020129985915 45266492191285530194978873)
      ·
        refine ⟨33949869143464147646234155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45266492191285530194978873 33949869143464147646234155)
        ·
          refine ⟨50924803715196221469351233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33949869143464147646234155 50924803715196221469351233)
          ·
            refine ⟨38193602786397166102013425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50924803715196221469351233 38193602786397166102013425)
            ·
              refine ⟨28645202089797874576510069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38193602786397166102013425 28645202089797874576510069)
              ·
                refine ⟨2685487695918550741547819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28645202089797874576510069 2685487695918550741547819)
                ·
                  refine ⟨4028231543877826112321729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685487695918550741547819 4028231543877826112321729)
                  ·
                    refine ⟨3021173657908369584241297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028231543877826112321729 3021173657908369584241297)
                    ·
                      refine ⟨2265880243431277188180973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021173657908369584241297 2265880243431277188180973)
                      ·
                        rfl

theorem cell23_4412786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 2, 2, 5, 1, 2, 2].length) (baseStart_4412786 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412786 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412786 prefixEnd_4412786 := by exact prefixLift 4412786
  have htrace : WordTrace (prefixWord ++ tailWord_4412786) baseStart_4412786 baseEnd_4412786 := by
    simpa [prefixWord, tailWord_4412786, baseEnd_4412786] using wordTrace_append hprefix tailTrace_4412786
  have hstable : (prefixWord ++ tailWord_4412786).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412786).length < 2 ^ (prefixWord ++ tailWord_4412786).sum := by decide
  have hdescent : baseEnd_4412786 < baseStart_4412786 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412789 : List Nat := [1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 5]
def baseStart_4412789 : Nat := 118140960795 + 4412789 * 2 ^ 59
def prefixEnd_4412789 : Nat := 4983230072969 + 3 ^ 40 * 4412789 * 2
def baseEnd_4412789 : Nat := 2265881783873240676443459

theorem tailTrace_4412789 : CollatzResearch.WordTrace tailWord_4412789 prefixEnd_4412789 2265881783873240676443459 := by
  unfold tailWord_4412789
  simp only [CollatzResearch.WordTrace]
  refine ⟨160947637210226572205617421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107298424806817714803744947 160947637210226572205617421)
  ·
    refine ⟨60355363953834964577106533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160947637210226572205617421 60355363953834964577106533)
    ·
      refine ⟨11316630741344055858207475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 60355363953834964577106533 11316630741344055858207475)
      ·
        refine ⟨16974946112016083787311213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11316630741344055858207475 16974946112016083787311213)
        ·
          refine ⟨6365604792006031420241705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16974946112016083787311213 6365604792006031420241705)
          ·
            refine ⟨4774203594004523565181279, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6365604792006031420241705 4774203594004523565181279)
            ·
              refine ⟨7161305391006785347771919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774203594004523565181279 7161305391006785347771919)
              ·
                refine ⟨10741958086510178021657879, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7161305391006785347771919 10741958086510178021657879)
                ·
                  refine ⟨16112937129765267032486819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10741958086510178021657879 16112937129765267032486819)
                  ·
                    refine ⟨24169405694647900548730229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16112937129765267032486819 24169405694647900548730229)
                    ·
                      refine ⟨2265881783873240676443459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24169405694647900548730229 2265881783873240676443459)
                      ·
                        rfl

theorem cell23_4412789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 3, 2, 1, 1, 1, 1, 5].length) (baseStart_4412789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412789 prefixEnd_4412789 := by exact prefixLift 4412789
  have htrace : WordTrace (prefixWord ++ tailWord_4412789) baseStart_4412789 baseEnd_4412789 := by
    simpa [prefixWord, tailWord_4412789, baseEnd_4412789] using wordTrace_append hprefix tailTrace_4412789
  have hstable : (prefixWord ++ tailWord_4412789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412789).length < 2 ^ (prefixWord ++ tailWord_4412789).sum := by decide
  have hdescent : baseEnd_4412789 < baseStart_4412789 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412803 : List Nat := [1, 1, 1, 3, 5, 1, 4, 2, 1, 2, 2]
def baseStart_4412803 : Nat := 118140960795 + 4412803 * 2 ^ 59
def prefixEnd_4412803 : Nat := 4983230072969 + 3 ^ 40 * 4412803 * 2
def baseEnd_4412803 : Nat := 2265888972602403621668395

theorem tailTrace_4412803 : CollatzResearch.WordTrace tailWord_4412803 prefixEnd_4412803 2265888972602403621668395 := by
  unfold tailWord_4412803
  simp only [CollatzResearch.WordTrace]
  refine ⟨160948147832175852596627063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107298765221450568397751375 160948147832175852596627063)
  ·
    refine ⟨241422221748263778894940595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160948147832175852596627063 241422221748263778894940595)
    ·
      refine ⟨362133332622395668342410893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241422221748263778894940595 362133332622395668342410893)
      ·
        refine ⟨135799999733398375628404085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362133332622395668342410893 135799999733398375628404085)
        ·
          refine ⟨12731249975006097715162883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135799999733398375628404085 12731249975006097715162883)
          ·
            refine ⟨19096874962509146572744325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12731249975006097715162883 19096874962509146572744325)
            ·
              refine ⟨3580664055470464982389561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19096874962509146572744325 3580664055470464982389561)
              ·
                refine ⟨2685498041602848736792171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3580664055470464982389561 2685498041602848736792171)
                ·
                  refine ⟨4028247062404273105188257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685498041602848736792171 4028247062404273105188257)
                  ·
                    refine ⟨3021185296803204828891193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028247062404273105188257 3021185296803204828891193)
                    ·
                      refine ⟨2265888972602403621668395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021185296803204828891193 2265888972602403621668395)
                      ·
                        rfl

theorem cell23_4412803_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 4, 2, 1, 2, 2].length) (baseStart_4412803 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412803 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412803 prefixEnd_4412803 := by exact prefixLift 4412803
  have htrace : WordTrace (prefixWord ++ tailWord_4412803) baseStart_4412803 baseEnd_4412803 := by
    simpa [prefixWord, tailWord_4412803, baseEnd_4412803] using wordTrace_append hprefix tailTrace_4412803
  have hstable : (prefixWord ++ tailWord_4412803).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412803).length < 2 ^ (prefixWord ++ tailWord_4412803).sum := by decide
  have hdescent : baseEnd_4412803 < baseStart_4412803 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412803) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412812 : List Nat := [2, 2, 1, 2, 1, 3, 1, 1, 5, 3, 2]
def baseStart_4412812 : Nat := 118140960795 + 4412812 * 2 ^ 59
def prefixEnd_4412812 : Nat := 4983230072969 + 3 ^ 40 * 4412812 * 2
def baseEnd_4412812 : Nat := 2265893593928294086455853

theorem tailTrace_4412812 : CollatzResearch.WordTrace tailWord_4412812 prefixEnd_4412812 2265893593928294086455853 := by
  unfold tailWord_4412812
  simp only [CollatzResearch.WordTrace]
  refine ⟨80474238044571623566852345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107298984059428831422469793 80474238044571623566852345)
  ·
    refine ⟨60355678533428717675139259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80474238044571623566852345 60355678533428717675139259)
    ·
      refine ⟨90533517800143076512708889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60355678533428717675139259 90533517800143076512708889)
      ·
        refine ⟨67900138350107307384531667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90533517800143076512708889 67900138350107307384531667)
        ·
          refine ⟨101850207525160961076797501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67900138350107307384531667 101850207525160961076797501)
          ·
            refine ⟨38193827821935360403799063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101850207525160961076797501 38193827821935360403799063)
            ·
              refine ⟨57290741732903040605698595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38193827821935360403799063 57290741732903040605698595)
              ·
                refine ⟨85936112599354560908547893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57290741732903040605698595 85936112599354560908547893)
                ·
                  refine ⟨8056510556189490085176365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 85936112599354560908547893 8056510556189490085176365)
                  ·
                    refine ⟨3021191458571058781941137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8056510556189490085176365 3021191458571058781941137)
                    ·
                      refine ⟨2265893593928294086455853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021191458571058781941137 2265893593928294086455853)
                      ·
                        rfl

theorem cell23_4412812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 3, 1, 1, 5, 3, 2].length) (baseStart_4412812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412812 prefixEnd_4412812 := by exact prefixLift 4412812
  have htrace : WordTrace (prefixWord ++ tailWord_4412812) baseStart_4412812 baseEnd_4412812 := by
    simpa [prefixWord, tailWord_4412812, baseEnd_4412812] using wordTrace_append hprefix tailTrace_4412812
  have hstable : (prefixWord ++ tailWord_4412812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412812).length < 2 ^ (prefixWord ++ tailWord_4412812).sum := by decide
  have hdescent : baseEnd_4412812 < baseStart_4412812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412829 : List Nat := [1, 4, 2, 1, 3, 1, 2, 1, 3, 3, 2]
def baseStart_4412829 : Nat := 118140960795 + 4412829 * 2 ^ 59
def prefixEnd_4412829 : Nat := 4983230072969 + 3 ^ 40 * 4412829 * 2
def baseEnd_4412829 : Nat := 2265902323099420519943275

theorem tailTrace_4412829 : CollatzResearch.WordTrace tailWord_4412829 prefixEnd_4412829 2265902323099420519943275 := by
  unfold tailWord_4412829
  simp only [CollatzResearch.WordTrace]
  refine ⟨160949096130081659037073541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107299397420054439358049027 160949096130081659037073541)
  ·
    refine ⟨30177955524390311069451289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 160949096130081659037073541 30177955524390311069451289)
    ·
      refine ⟨22633466643292733302088467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30177955524390311069451289 22633466643292733302088467)
      ·
        refine ⟨33950199964939099953132701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22633466643292733302088467 33950199964939099953132701)
        ·
          refine ⟨12731324986852162482424763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33950199964939099953132701 12731324986852162482424763)
          ·
            refine ⟨19096987480278243723637145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12731324986852162482424763 19096987480278243723637145)
            ·
              refine ⟨14322740610208682792727859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19096987480278243723637145 14322740610208682792727859)
              ·
                refine ⟨21484110915313024189091789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14322740610208682792727859 21484110915313024189091789)
                ·
                  refine ⟨8056541593242384070909421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21484110915313024189091789 8056541593242384070909421)
                  ·
                    refine ⟨3021203097465894026591033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8056541593242384070909421 3021203097465894026591033)
                    ·
                      refine ⟨2265902323099420519943275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021203097465894026591033 2265902323099420519943275)
                      ·
                        rfl

theorem cell23_4412829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 1, 3, 3, 2].length) (baseStart_4412829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412829 prefixEnd_4412829 := by exact prefixLift 4412829
  have htrace : WordTrace (prefixWord ++ tailWord_4412829) baseStart_4412829 baseEnd_4412829 := by
    simpa [prefixWord, tailWord_4412829, baseEnd_4412829] using wordTrace_append hprefix tailTrace_4412829
  have hstable : (prefixWord ++ tailWord_4412829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412829).length < 2 ^ (prefixWord ++ tailWord_4412829).sum := by decide
  have hdescent : baseEnd_4412829 < baseStart_4412829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412840 : List Nat := [2, 1, 6, 1, 3, 1, 2, 1, 1, 2, 3]
def baseStart_4412840 : Nat := 118140960795 + 4412840 * 2 ^ 59
def prefixEnd_4412840 : Nat := 4983230072969 + 3 ^ 40 * 4412840 * 2
def baseEnd_4412840 : Nat := 2265907971386619976905725

theorem tailTrace_4412840 : CollatzResearch.WordTrace tailWord_4412840 prefixEnd_4412840 2265907971386619976905725 := by
  unfold tailWord_4412840
  simp only [CollatzResearch.WordTrace]
  refine ⟨80474748666520903957861987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107299664888694538610482649 80474748666520903957861987)
  ·
    refine ⟨120712122999781355936792981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80474748666520903957861987 120712122999781355936792981)
    ·
      refine ⟨5658380765614751059537171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120712122999781355936792981 5658380765614751059537171)
      ·
        refine ⟨8487571148422126589305757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658380765614751059537171 8487571148422126589305757)
        ·
          refine ⟨3182839180658297470989659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8487571148422126589305757 3182839180658297470989659)
          ·
            refine ⟨4774258770987446206484489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3182839180658297470989659 4774258770987446206484489)
            ·
              refine ⟨3580694078240584654863367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4774258770987446206484489 3580694078240584654863367)
              ·
                refine ⟨5371041117360876982295051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3580694078240584654863367 5371041117360876982295051)
                ·
                  refine ⟨8056561676041315473442577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5371041117360876982295051 8056561676041315473442577)
                  ·
                    refine ⟨6042421257030986605081933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8056561676041315473442577 6042421257030986605081933)
                    ·
                      refine ⟨2265907971386619976905725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6042421257030986605081933 2265907971386619976905725)
                      ·
                        rfl

theorem cell23_4412840_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 2, 1, 1, 2, 3].length) (baseStart_4412840 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412840 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412840 prefixEnd_4412840 := by exact prefixLift 4412840
  have htrace : WordTrace (prefixWord ++ tailWord_4412840) baseStart_4412840 baseEnd_4412840 := by
    simpa [prefixWord, tailWord_4412840, baseEnd_4412840] using wordTrace_append hprefix tailTrace_4412840
  have hstable : (prefixWord ++ tailWord_4412840).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412840).length < 2 ^ (prefixWord ++ tailWord_4412840).sum := by decide
  have hdescent : baseEnd_4412840 < baseStart_4412840 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412840) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412855 : List Nat := [1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 4]
def baseStart_4412855 : Nat := 118140960795 + 4412855 * 2 ^ 59
def prefixEnd_4412855 : Nat := 4983230072969 + 3 ^ 40 * 4412855 * 2
def baseEnd_4412855 : Nat := 2265915673596437418218155

theorem tailTrace_4412855 : CollatzResearch.WordTrace tailWord_4412855 prefixEnd_4412855 2265915673596437418218155 := by
  unfold tailWord_4412855
  simp only [CollatzResearch.WordTrace]
  refine ⟨160950044427987465477520019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107300029618658310318346679 160950044427987465477520019)
  ·
    refine ⟨241425066641981198216280029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160950044427987465477520019 241425066641981198216280029)
    ·
      refine ⟨90534399990742949331105011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241425066641981198216280029 90534399990742949331105011)
      ·
        refine ⟨135801599986114423996657517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90534399990742949331105011 135801599986114423996657517)
        ·
          refine ⟨50925599994792908998746569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135801599986114423996657517 50925599994792908998746569)
          ·
            refine ⟨38194199996094681749059927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50925599994792908998746569 38194199996094681749059927)
            ·
              refine ⟨57291299994142022623589891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38194199996094681749059927 57291299994142022623589891)
              ·
                refine ⟨85936949991213033935384837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57291299994142022623589891 85936949991213033935384837)
                ·
                  refine ⟨16113178123352443862884657, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85936949991213033935384837 16113178123352443862884657)
                  ·
                    refine ⟨12084883592514332897163493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16113178123352443862884657 12084883592514332897163493)
                    ·
                      refine ⟨2265915673596437418218155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12084883592514332897163493 2265915673596437418218155)
                      ·
                        rfl

theorem cell23_4412855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 1, 4, 2, 4].length) (baseStart_4412855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412855 prefixEnd_4412855 := by exact prefixLift 4412855
  have htrace : WordTrace (prefixWord ++ tailWord_4412855) baseStart_4412855 baseEnd_4412855 := by
    simpa [prefixWord, tailWord_4412855, baseEnd_4412855] using wordTrace_append hprefix tailTrace_4412855
  have hstable : (prefixWord ++ tailWord_4412855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412855).length < 2 ^ (prefixWord ++ tailWord_4412855).sum := by decide
  have hdescent : baseEnd_4412855 < baseStart_4412855 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412876 : List Nat := [2, 2, 1, 4, 2, 3, 1, 1, 1, 4, 2]
def baseStart_4412876 : Nat := 118140960795 + 4412876 * 2 ^ 59
def prefixEnd_4412876 : Nat := 4983230072969 + 3 ^ 40 * 4412876 * 2
def baseEnd_4412876 : Nat := 2265926456690181836055559

theorem tailTrace_4412876 : CollatzResearch.WordTrace tailWord_4412876 prefixEnd_4412876 2265926456690181836055559 := by
  unfold tailWord_4412876
  simp only [CollatzResearch.WordTrace]
  refine ⟨80475405180455693032017241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107300540240607590709356321 80475405180455693032017241)
  ·
    refine ⟨60356553885341769774012931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80475405180455693032017241 60356553885341769774012931)
    ·
      refine ⟨90534830828012654661019397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60356553885341769774012931 90534830828012654661019397)
      ·
        refine ⟨16975280780252372748941137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90534830828012654661019397 16975280780252372748941137)
        ·
          refine ⟨12731460585189279561705853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16975280780252372748941137 12731460585189279561705853)
          ·
            refine ⟨4774297719445979835639695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12731460585189279561705853 4774297719445979835639695)
            ·
              refine ⟨7161446579168969753459543, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774297719445979835639695 7161446579168969753459543)
              ·
                refine ⟨10742169868753454630189315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7161446579168969753459543 10742169868753454630189315)
                ·
                  refine ⟨16113254803130181945283973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10742169868753454630189315 16113254803130181945283973)
                  ·
                    refine ⟨3021235275586909114740745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16113254803130181945283973 3021235275586909114740745)
                    ·
                      refine ⟨2265926456690181836055559, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021235275586909114740745 2265926456690181836055559)
                      ·
                        rfl

theorem cell23_4412876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 2, 3, 1, 1, 1, 4, 2].length) (baseStart_4412876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412876 prefixEnd_4412876 := by exact prefixLift 4412876
  have htrace : WordTrace (prefixWord ++ tailWord_4412876) baseStart_4412876 baseEnd_4412876 := by
    simpa [prefixWord, tailWord_4412876, baseEnd_4412876] using wordTrace_append hprefix tailTrace_4412876
  have hstable : (prefixWord ++ tailWord_4412876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412876).length < 2 ^ (prefixWord ++ tailWord_4412876).sum := by decide
  have hdescent : baseEnd_4412876 < baseStart_4412876 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412895 : List Nat := [1, 1, 2, 3, 3, 1, 1, 3, 1, 7]
def baseStart_4412895 : Nat := 118140960795 + 4412895 * 2 ^ 59
def prefixEnd_4412895 : Nat := 4983230072969 + 3 ^ 40 * 4412895 * 2
def baseEnd_4412895 : Nat := 755312070940872420572657

theorem tailTrace_4412895 : CollatzResearch.WordTrace tailWord_4412895 prefixEnd_4412895 755312070940872420572657 := by
  unfold tailWord_4412895
  simp only [CollatzResearch.WordTrace]
  refine ⟨160951503347842552308976139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107301002231895034872650759 160951503347842552308976139)
  ·
    refine ⟨241427255021763828463464209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160951503347842552308976139 241427255021763828463464209)
    ·
      refine ⟨181070441266322871347598157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241427255021763828463464209 181070441266322871347598157)
      ·
        refine ⟨67901415474871076755349309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181070441266322871347598157 67901415474871076755349309)
        ·
          refine ⟨25463030803076653783255991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67901415474871076755349309 25463030803076653783255991)
          ·
            refine ⟨38194546204614980674883987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25463030803076653783255991 38194546204614980674883987)
            ·
              refine ⟨57291819306922471012325981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38194546204614980674883987 57291819306922471012325981)
              ·
                refine ⟨21484432240095926629622243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57291819306922471012325981 21484432240095926629622243)
                ·
                  refine ⟨32226648360143889944433365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21484432240095926629622243 32226648360143889944433365)
                  ·
                    refine ⟨755312070940872420572657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32226648360143889944433365 755312070940872420572657)
                    ·
                      rfl

theorem cell23_4412895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 3, 1, 7].length) (baseStart_4412895 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412895 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412895 prefixEnd_4412895 := by exact prefixLift 4412895
  have htrace : WordTrace (prefixWord ++ tailWord_4412895) baseStart_4412895 baseEnd_4412895 := by
    simpa [prefixWord, tailWord_4412895, baseEnd_4412895] using wordTrace_append hprefix tailTrace_4412895
  have hstable : (prefixWord ++ tailWord_4412895).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412895).length < 2 ^ (prefixWord ++ tailWord_4412895).sum := by decide
  have hdescent : baseEnd_4412895 < baseStart_4412895 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412899 : List Nat := [1, 1, 1, 6, 2, 1, 3, 3, 5]
def baseStart_4412899 : Nat := 118140960795 + 4412899 * 2 ^ 59
def prefixEnd_4412899 : Nat := 4983230072969 + 3 ^ 40 * 4412899 * 2
def baseEnd_4412899 : Nat := 251770918527248360674217

theorem tailTrace_4412899 : CollatzResearch.WordTrace tailWord_4412899 prefixEnd_4412899 251770918527248360674217 := by
  unfold tailWord_4412899
  simp only [CollatzResearch.WordTrace]
  refine ⟨160951649239828060992121751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107301099493218707328081167 160951649239828060992121751)
  ·
    refine ⟨241427473859742091488182627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160951649239828060992121751 241427473859742091488182627)
    ·
      refine ⟨362141210789613137232273941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241427473859742091488182627 362141210789613137232273941)
      ·
        refine ⟨16975369255763115807762841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 362141210789613137232273941 16975369255763115807762841)
        ·
          refine ⟨12731526941822336855822131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16975369255763115807762841 12731526941822336855822131)
          ·
            refine ⟨19097290412733505283733197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12731526941822336855822131 19097290412733505283733197)
            ·
              refine ⟨7161483904775064481399949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19097290412733505283733197 7161483904775064481399949)
              ·
                refine ⟨2685556464290649180524981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7161483904775064481399949 2685556464290649180524981)
                ·
                  refine ⟨251770918527248360674217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2685556464290649180524981 251770918527248360674217)
                  ·
                    rfl

theorem cell23_4412899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 3, 3, 5].length) (baseStart_4412899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412899 prefixEnd_4412899 := by exact prefixLift 4412899
  have htrace : WordTrace (prefixWord ++ tailWord_4412899) baseStart_4412899 baseEnd_4412899 := by
    simpa [prefixWord, tailWord_4412899, baseEnd_4412899] using wordTrace_append hprefix tailTrace_4412899
  have hstable : (prefixWord ++ tailWord_4412899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412899).length < 2 ^ (prefixWord ++ tailWord_4412899).sum := by decide
  have hdescent : baseEnd_4412899 < baseStart_4412899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412912 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 2, 5]
def baseStart_4412912 : Nat := 118140960795 + 4412912 * 2 ^ 59
def prefixEnd_4412912 : Nat := 4983230072969 + 3 ^ 40 * 4412912 * 2
def baseEnd_4412912 : Nat := 755314980664581231735131

theorem tailTrace_4412912 : CollatzResearch.WordTrace tailWord_4412912 prefixEnd_4412912 755314980664581231735131 := by
  unfold tailWord_4412912
  simp only [CollatzResearch.WordTrace]
  refine ⟨80476061694390482106172495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107301415592520642808229993 80476061694390482106172495)
  ·
    refine ⟨120714092541585723159258743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80476061694390482106172495 120714092541585723159258743)
    ·
      refine ⟨181071138812378584738888115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120714092541585723159258743 181071138812378584738888115)
      ·
        refine ⟨271606708218567877108332173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181071138812378584738888115 271606708218567877108332173)
        ·
          refine ⟨101852515581962953915624565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271606708218567877108332173 101852515581962953915624565)
          ·
            refine ⟨9548673335809026929589803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 101852515581962953915624565 9548673335809026929589803)
            ·
              refine ⟨14323010003713540394384705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9548673335809026929589803 14323010003713540394384705)
              ·
                refine ⟨10742257502785155295788529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14323010003713540394384705 10742257502785155295788529)
                ·
                  refine ⟨8056693127088866471841397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10742257502785155295788529 8056693127088866471841397)
                  ·
                    refine ⟨755314980664581231735131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8056693127088866471841397 755314980664581231735131)
                    ·
                      rfl

theorem cell23_4412912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 2, 5].length) (baseStart_4412912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412912 prefixEnd_4412912 := by exact prefixLift 4412912
  have htrace : WordTrace (prefixWord ++ tailWord_4412912) baseStart_4412912 baseEnd_4412912 := by
    simpa [prefixWord, tailWord_4412912, baseEnd_4412912] using wordTrace_append hprefix tailTrace_4412912
  have hstable : (prefixWord ++ tailWord_4412912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412912).length < 2 ^ (prefixWord ++ tailWord_4412912).sum := by decide
  have hdescent : baseEnd_4412912 < baseStart_4412912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412915 : List Nat := [1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4]
def baseStart_4412915 : Nat := 118140960795 + 4412915 * 2 ^ 59
def prefixEnd_4412915 : Nat := 4983230072969 + 3 ^ 40 * 4412915 * 2
def baseEnd_4412915 : Nat := 2265946482435707183467879

theorem tailTrace_4412915 : CollatzResearch.WordTrace tailWord_4412915 prefixEnd_4412915 2265946482435707183467879 := by
  unfold tailWord_4412915
  simp only [CollatzResearch.WordTrace]
  refine ⟨160952232807770095724704199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107301488538513397149802799 160952232807770095724704199)
  ·
    refine ⟨241428349211655143587056299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160952232807770095724704199 241428349211655143587056299)
    ·
      refine ⟨362142523817482715380584449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241428349211655143587056299 362142523817482715380584449)
      ·
        refine ⟨271606892863112036535438337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362142523817482715380584449 271606892863112036535438337)
        ·
          refine ⟨203705169647334027401578753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271606892863112036535438337 203705169647334027401578753)
          ·
            refine ⟨152778877235500520551184065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203705169647334027401578753 152778877235500520551184065)
            ·
              refine ⟨114584157926625390413388049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152778877235500520551184065 114584157926625390413388049)
              ·
                refine ⟨85938118444969042810041037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114584157926625390413388049 85938118444969042810041037)
                ·
                  refine ⟨32226794416863391053765389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85938118444969042810041037 32226794416863391053765389)
                  ·
                    refine ⟨12085047906323771645162021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32226794416863391053765389 12085047906323771645162021)
                    ·
                      refine ⟨2265946482435707183467879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12085047906323771645162021 2265946482435707183467879)
                      ·
                        rfl

theorem cell23_4412915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 2, 3, 3, 4].length) (baseStart_4412915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412915 prefixEnd_4412915 := by exact prefixLift 4412915
  have htrace : WordTrace (prefixWord ++ tailWord_4412915) baseStart_4412915 baseEnd_4412915 := by
    simpa [prefixWord, tailWord_4412915, baseEnd_4412915] using wordTrace_append hprefix tailTrace_4412915
  have hstable : (prefixWord ++ tailWord_4412915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412915).length < 2 ^ (prefixWord ++ tailWord_4412915).sum := by decide
  have hdescent : baseEnd_4412915 < baseStart_4412915 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4412949 : List Nat := [1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 4]
def baseStart_4412949 : Nat := 118140960795 + 4412949 * 2 ^ 59
def prefixEnd_4412949 : Nat := 4983230072969 + 3 ^ 40 * 4412949 * 2
def baseEnd_4412949 : Nat := 2265963940777960050442723

theorem tailTrace_4412949 : CollatzResearch.WordTrace tailWord_4412949 prefixEnd_4412949 2265963940777960050442723 := by
  unfold tailWord_4412949
  simp only [CollatzResearch.WordTrace]
  refine ⟨160953472889646919531441901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107302315259764613020961267 160953472889646919531441901)
  ·
    refine ⟨60357552333617594824290713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160953472889646919531441901 60357552333617594824290713)
    ·
      refine ⟨45268164250213196118218035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60357552333617594824290713 45268164250213196118218035)
      ·
        refine ⟨67902246375319794177327053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45268164250213196118218035 67902246375319794177327053)
        ·
          refine ⟨25463342390744922816497645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67902246375319794177327053 25463342390744922816497645)
          ·
            refine ⟨9548753396529346056186617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25463342390744922816497645 9548753396529346056186617)
            ·
              refine ⟨7161565047397009542139963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9548753396529346056186617 7161565047397009542139963)
              ·
                refine ⟨10742347571095514313209945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7161565047397009542139963 10742347571095514313209945)
                ·
                  refine ⟨8056760678321635734907459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10742347571095514313209945 8056760678321635734907459)
                  ·
                    refine ⟨12085141017482453602361189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8056760678321635734907459 12085141017482453602361189)
                    ·
                      refine ⟨2265963940777960050442723, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12085141017482453602361189 2265963940777960050442723)
                      ·
                        rfl

theorem cell23_4412949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 3, 2, 1, 2, 1, 4].length) (baseStart_4412949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4412949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4412949 prefixEnd_4412949 := by exact prefixLift 4412949
  have htrace : WordTrace (prefixWord ++ tailWord_4412949) baseStart_4412949 baseEnd_4412949 := by
    simpa [prefixWord, tailWord_4412949, baseEnd_4412949] using wordTrace_append hprefix tailTrace_4412949
  have hstable : (prefixWord ++ tailWord_4412949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4412949).length < 2 ^ (prefixWord ++ tailWord_4412949).sum := by decide
  have hdescent : baseEnd_4412949 < baseStart_4412949 := by decide
  rcases family_descends (prefixWord ++ tailWord_4412949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413002 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 3, 5]
def baseStart_4413002 : Nat := 118140960795 + 4413002 * 2 ^ 59
def prefixEnd_4413002 : Nat := 4983230072969 + 3 ^ 40 * 4413002 * 2
def baseEnd_4413002 : Nat := 755330385084216114359993

theorem tailTrace_4413002 : CollatzResearch.WordTrace tailWord_4413002 prefixEnd_4413002 755330385084216114359993 := by
  unfold tailWord_4413002
  simp only [CollatzResearch.WordTrace]
  refine ⟨40238851489613727395780315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107303603972303273055414173 40238851489613727395780315)
  ·
    refine ⟨60358277234420591093670473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40238851489613727395780315 60358277234420591093670473)
    ·
      refine ⟨45268707925815443320252855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60358277234420591093670473 45268707925815443320252855)
      ·
        refine ⟨67903061888723164980379283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45268707925815443320252855 67903061888723164980379283)
        ·
          refine ⟨101854592833084747470568925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67903061888723164980379283 101854592833084747470568925)
          ·
            refine ⟨38195472312406780301463347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101854592833084747470568925 38195472312406780301463347)
            ·
              refine ⟨57293208468610170452195021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38195472312406780301463347 57293208468610170452195021)
              ·
                refine ⟨21484953175728813919573133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57293208468610170452195021 21484953175728813919573133)
                ·
                  refine ⟨8056857440898305219839925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21484953175728813919573133 8056857440898305219839925)
                  ·
                    refine ⟨755330385084216114359993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8056857440898305219839925 755330385084216114359993)
                    ·
                      rfl

theorem cell23_4413002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 3, 5].length) (baseStart_4413002 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413002 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413002 prefixEnd_4413002 := by exact prefixLift 4413002
  have htrace : WordTrace (prefixWord ++ tailWord_4413002) baseStart_4413002 baseEnd_4413002 := by
    simpa [prefixWord, tailWord_4413002, baseEnd_4413002] using wordTrace_append hprefix tailTrace_4413002
  have hstable : (prefixWord ++ tailWord_4413002).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413002).length < 2 ^ (prefixWord ++ tailWord_4413002).sum := by decide
  have hdescent : baseEnd_4413002 < baseStart_4413002 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413009 : List Nat := [1, 2, 2, 1, 3, 2, 3, 1, 1, 5, 2]
def baseStart_4413009 : Nat := 118140960795 + 4413009 * 2 ^ 59
def prefixEnd_4413009 : Nat := 4983230072969 + 3 ^ 40 * 4413009 * 2
def baseEnd_4413009 : Nat := 2265994749617229815692447

theorem tailTrace_4413009 : CollatzResearch.WordTrace tailWord_4413009 prefixEnd_4413009 2265994749617229815692447 := by
  unfold tailWord_4413009
  simp only [CollatzResearch.WordTrace]
  refine ⟨160955661269429549778626081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107303774179619699852417387 160955661269429549778626081)
  ·
    refine ⟨120716745952072162333969561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160955661269429549778626081 120716745952072162333969561)
    ·
      refine ⟨90537559464054121750477171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120716745952072162333969561 90537559464054121750477171)
      ·
        refine ⟨135806339196081182625715757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90537559464054121750477171 135806339196081182625715757)
        ·
          refine ⟨50927377198530443484643409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135806339196081182625715757 50927377198530443484643409)
          ·
            refine ⟨38195532898897832613482557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50927377198530443484643409 38195532898897832613482557)
            ·
              refine ⟨14323324837086687230055959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38195532898897832613482557 14323324837086687230055959)
              ·
                refine ⟨21484987255630030845083939, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14323324837086687230055959 21484987255630030845083939)
                ·
                  refine ⟨32227480883445046267625909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21484987255630030845083939 32227480883445046267625909)
                  ·
                    refine ⟨3021326332822973087589929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32227480883445046267625909 3021326332822973087589929)
                    ·
                      refine ⟨2265994749617229815692447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021326332822973087589929 2265994749617229815692447)
                      ·
                        rfl

theorem cell23_4413009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 1, 1, 5, 2].length) (baseStart_4413009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413009 prefixEnd_4413009 := by exact prefixLift 4413009
  have htrace : WordTrace (prefixWord ++ tailWord_4413009) baseStart_4413009 baseEnd_4413009 := by
    simpa [prefixWord, tailWord_4413009, baseEnd_4413009] using wordTrace_append hprefix tailTrace_4413009
  have hstable : (prefixWord ++ tailWord_4413009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413009).length < 2 ^ (prefixWord ++ tailWord_4413009).sum := by decide
  have hdescent : baseEnd_4413009 < baseStart_4413009 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413056 : List Nat := [2, 1, 1, 2, 1, 4, 1, 4, 3, 2, 2]
def baseStart_4413056 : Nat := 118140960795 + 4413056 * 2 ^ 59
def prefixEnd_4413056 : Nat := 4983230072969 + 3 ^ 40 * 4413056 * 2
def baseEnd_4413056 : Nat := 2266018883207991131804731

theorem tailTrace_4413056 : CollatzResearch.WordTrace tailWord_4413056 prefixEnd_4413056 2266018883207991131804731 := by
  unfold tailWord_4413056
  simp only [CollatzResearch.WordTrace]
  refine ⟨80478687750129638402793511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107304917000172851203724681 80478687750129638402793511)
  ·
    refine ⟨120718031625194457604190267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80478687750129638402793511 120718031625194457604190267)
    ·
      refine ⟨181077047437791686406285401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120718031625194457604190267 181077047437791686406285401)
      ·
        refine ⟨135807785578343764804714051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181077047437791686406285401 135807785578343764804714051)
        ·
          refine ⟨203711678367515647207071077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135807785578343764804714051 203711678367515647207071077)
          ·
            refine ⟨38195939693909183851325827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203711678367515647207071077 38195939693909183851325827)
            ·
              refine ⟨57293909540863775776988741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38195939693909183851325827 57293909540863775776988741)
              ·
                refine ⟨10742608038911957958185389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57293909540863775776988741 10742608038911957958185389)
                ·
                  refine ⟨4028478014591984234319521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10742608038911957958185389 4028478014591984234319521)
                  ·
                    refine ⟨3021358510943988175739641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028478014591984234319521 3021358510943988175739641)
                    ·
                      refine ⟨2266018883207991131804731, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021358510943988175739641 2266018883207991131804731)
                      ·
                        rfl

theorem cell23_4413056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 4, 3, 2, 2].length) (baseStart_4413056 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413056 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413056 prefixEnd_4413056 := by exact prefixLift 4413056
  have htrace : WordTrace (prefixWord ++ tailWord_4413056) baseStart_4413056 baseEnd_4413056 := by
    simpa [prefixWord, tailWord_4413056, baseEnd_4413056] using wordTrace_append hprefix tailTrace_4413056
  have hstable : (prefixWord ++ tailWord_4413056).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413056).length < 2 ^ (prefixWord ++ tailWord_4413056).sum := by decide
  have hdescent : baseEnd_4413056 < baseStart_4413056 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413073 : List Nat := [1, 2, 2, 1, 1, 1, 1, 9, 1, 2, 2]
def baseStart_4413073 : Nat := 118140960795 + 4413073 * 2 ^ 59
def prefixEnd_4413073 : Nat := 4983230072969 + 3 ^ 40 * 4413073 * 2
def baseEnd_4413073 : Nat := 2266027612379117565292153

theorem tailTrace_4413073 : CollatzResearch.WordTrace tailWord_4413073 prefixEnd_4413073 2266027612379117565292153 := by
  unfold tailWord_4413073
  simp only [CollatzResearch.WordTrace]
  refine ⟨160957995541197688708955873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107305330360798459139303915 160957995541197688708955873)
  ·
    refine ⟨120718496655898266531716905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160957995541197688708955873 120718496655898266531716905)
    ·
      refine ⟨90538872491923699898787679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120718496655898266531716905 90538872491923699898787679)
      ·
        refine ⟨135808308737885549848181519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90538872491923699898787679 135808308737885549848181519)
        ·
          refine ⟨203712463106828324772272279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135808308737885549848181519 203712463106828324772272279)
          ·
            refine ⟨305568694660242487158408419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203712463106828324772272279 305568694660242487158408419)
            ·
              refine ⟨458353041990363730737612629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305568694660242487158408419 458353041990363730737612629)
              ·
                refine ⟨2685662355412287484790699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 458353041990363730737612629 2685662355412287484790699)
                ·
                  refine ⟨4028493533118431227186049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2685662355412287484790699 4028493533118431227186049)
                  ·
                    refine ⟨3021370149838823420389537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028493533118431227186049 3021370149838823420389537)
                    ·
                      refine ⟨2266027612379117565292153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021370149838823420389537 2266027612379117565292153)
                      ·
                        rfl

theorem cell23_4413073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 9, 1, 2, 2].length) (baseStart_4413073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413073 prefixEnd_4413073 := by exact prefixLift 4413073
  have htrace : WordTrace (prefixWord ++ tailWord_4413073) baseStart_4413073 baseEnd_4413073 := by
    simpa [prefixWord, tailWord_4413073, baseEnd_4413073] using wordTrace_append hprefix tailTrace_4413073
  have hstable : (prefixWord ++ tailWord_4413073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413073).length < 2 ^ (prefixWord ++ tailWord_4413073).sum := by decide
  have hdescent : baseEnd_4413073 < baseStart_4413073 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413110 : List Nat := [5, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3]
def baseStart_4413110 : Nat := 118140960795 + 4413110 * 2 ^ 59
def prefixEnd_4413110 : Nat := 4983230072969 + 3 ^ 40 * 4413110 * 2
def baseEnd_4413110 : Nat := 2266046611163333920529483

theorem tailTrace_4413110 : CollatzResearch.WordTrace tailWord_4413110 prefixEnd_4413110 2266046611163333920529483 := by
  unfold tailWord_4413110
  simp only [CollatzResearch.WordTrace]
  refine ⟨10059959065128977751753299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107306230028042429352035189 10059959065128977751753299)
  ·
    refine ⟨15089938597693466627629949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10059959065128977751753299 15089938597693466627629949)
    ·
      refine ⟨5658726974135049985361231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15089938597693466627629949 5658726974135049985361231)
      ·
        refine ⟨8488090461202574978041847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658726974135049985361231 8488090461202574978041847)
        ·
          refine ⟨12732135691803862467062771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488090461202574978041847 12732135691803862467062771)
          ·
            refine ⟨19098203537705793700594157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12732135691803862467062771 19098203537705793700594157)
            ·
              refine ⟨7161826326639672637722809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19098203537705793700594157 7161826326639672637722809)
              ·
                refine ⟨5371369744979754478292107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7161826326639672637722809 5371369744979754478292107)
                ·
                  refine ⟨8057054617469631717438161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5371369744979754478292107 8057054617469631717438161)
                  ·
                    refine ⟨6042790963102223788078621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8057054617469631717438161 6042790963102223788078621)
                    ·
                      refine ⟨2266046611163333920529483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6042790963102223788078621 2266046611163333920529483)
                      ·
                        rfl

theorem cell23_4413110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 3, 2, 1, 2, 3].length) (baseStart_4413110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413110 prefixEnd_4413110 := by exact prefixLift 4413110
  have htrace : WordTrace (prefixWord ++ tailWord_4413110) baseStart_4413110 baseEnd_4413110 := by
    simpa [prefixWord, tailWord_4413110, baseEnd_4413110] using wordTrace_append hprefix tailTrace_4413110
  have hstable : (prefixWord ++ tailWord_4413110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413110).length < 2 ^ (prefixWord ++ tailWord_4413110).sum := by decide
  have hdescent : baseEnd_4413110 < baseStart_4413110 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413140 : List Nat := [2, 4, 1, 3, 1, 2, 2, 2, 2, 1, 3]
def baseStart_4413140 : Nat := 118140960795 + 4413140 * 2 ^ 59
def prefixEnd_4413140 : Nat := 4983230072969 + 3 ^ 40 * 4413140 * 2
def baseEnd_4413140 : Nat := 2266062015582968803154345

theorem tailTrace_4413140 : CollatzResearch.WordTrace tailWord_4413140 prefixEnd_4413140 2266062015582968803154345 := by
  unfold tailWord_4413140
  simp only [CollatzResearch.WordTrace]
  refine ⟨80480219615977479575822437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107306959487969972767763249 80480219615977479575822437)
  ·
    refine ⟨15090041177995777420466707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80480219615977479575822437 15090041177995777420466707)
    ·
      refine ⟨22635061766993666130700061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15090041177995777420466707 22635061766993666130700061)
      ·
        refine ⟨8488148162622624799012523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22635061766993666130700061 8488148162622624799012523)
        ·
          refine ⟨12732222243933937198518785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488148162622624799012523 12732222243933937198518785)
          ·
            refine ⟨9549166682950452898889089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12732222243933937198518785 9549166682950452898889089)
            ·
              refine ⟨7161875012212839674166817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9549166682950452898889089 7161875012212839674166817)
              ·
                refine ⟨5371406259159629755625113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7161875012212839674166817 5371406259159629755625113)
                ·
                  refine ⟨4028554694369722316718835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5371406259159629755625113 4028554694369722316718835)
                  ·
                    refine ⟨6042832041554583475078253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4028554694369722316718835 6042832041554583475078253)
                    ·
                      refine ⟨2266062015582968803154345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6042832041554583475078253 2266062015582968803154345)
                      ·
                        rfl

theorem cell23_4413140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 2, 2, 2, 1, 3].length) (baseStart_4413140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413140 prefixEnd_4413140 := by exact prefixLift 4413140
  have htrace : WordTrace (prefixWord ++ tailWord_4413140) baseStart_4413140 baseEnd_4413140 := by
    simpa [prefixWord, tailWord_4413140, baseEnd_4413140] using wordTrace_append hprefix tailTrace_4413140
  have hstable : (prefixWord ++ tailWord_4413140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413140).length < 2 ^ (prefixWord ++ tailWord_4413140).sum := by decide
  have hdescent : baseEnd_4413140 < baseStart_4413140 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413163 : List Nat := [1, 1, 1, 1, 2, 4, 4, 3, 2, 2, 2]
def baseStart_4413163 : Nat := 118140960795 + 4413163 * 2 ^ 59
def prefixEnd_4413163 : Nat := 4983230072969 + 3 ^ 40 * 4413163 * 2
def baseEnd_4413163 : Nat := 2266073825638022213166739

theorem tailTrace_4413163 : CollatzResearch.WordTrace tailWord_4413163 prefixEnd_4413163 2266073825638022213166739 := by
  unfold tailWord_4413163
  simp only [CollatzResearch.WordTrace]
  refine ⟨160961278110871634079732143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107307518740581089386488095 160961278110871634079732143)
  ·
    refine ⟨241441917166307451119598215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160961278110871634079732143 241441917166307451119598215)
    ·
      refine ⟨362162875749461176679397323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241441917166307451119598215 362162875749461176679397323)
      ·
        refine ⟨543244313624191765019095985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362162875749461176679397323 543244313624191765019095985)
        ·
          refine ⟨407433235218143823764321989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543244313624191765019095985 407433235218143823764321989)
          ·
            refine ⟨76393731603401966955810373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 407433235218143823764321989 76393731603401966955810373)
            ·
              refine ⟨14323824675637868804214445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76393731603401966955810373 14323824675637868804214445)
              ·
                refine ⟨5371434253364200801580417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14323824675637868804214445 5371434253364200801580417)
                ·
                  refine ⟨4028575690023150601185313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5371434253364200801580417 4028575690023150601185313)
                  ·
                    refine ⟨3021431767517362950888985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4028575690023150601185313 3021431767517362950888985)
                    ·
                      refine ⟨2266073825638022213166739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021431767517362950888985 2266073825638022213166739)
                      ·
                        rfl

theorem cell23_4413163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 3, 2, 2, 2].length) (baseStart_4413163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413163 prefixEnd_4413163 := by exact prefixLift 4413163
  have htrace : WordTrace (prefixWord ++ tailWord_4413163) baseStart_4413163 baseEnd_4413163 := by
    simpa [prefixWord, tailWord_4413163, baseEnd_4413163] using wordTrace_append hprefix tailTrace_4413163
  have hstable : (prefixWord ++ tailWord_4413163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413163).length < 2 ^ (prefixWord ++ tailWord_4413163).sum := by decide
  have hdescent : baseEnd_4413163 < baseStart_4413163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413169 : List Nat := [1, 2, 2, 2, 2, 4, 1, 2, 7]
def baseStart_4413169 : Nat := 118140960795 + 4413169 * 2 ^ 59
def prefixEnd_4413169 : Nat := 4983230072969 + 3 ^ 40 * 4413169 * 2
def baseEnd_4413169 : Nat := 251786322946883243299079

theorem tailTrace_4413169 : CollatzResearch.WordTrace tailWord_4413169 prefixEnd_4413169 251786322946883243299079 := by
  unfold tailWord_4413169
  simp only [CollatzResearch.WordTrace]
  refine ⟨160961496948849897104450561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107307664632566598069633707 160961496948849897104450561)
  ·
    refine ⟨120721122711637422828337921, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160961496948849897104450561 120721122711637422828337921)
    ·
      refine ⟨90540842033728067121253441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120721122711637422828337921 90540842033728067121253441)
      ·
        refine ⟨67905631525296050340940081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90540842033728067121253441 67905631525296050340940081)
        ·
          refine ⟨50929223643972037755705061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67905631525296050340940081 50929223643972037755705061)
          ·
            refine ⟨9549229433244757079194699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50929223643972037755705061 9549229433244757079194699)
            ·
              refine ⟨14323844149867135618792049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9549229433244757079194699 14323844149867135618792049)
              ·
                refine ⟨10742883112400351714094037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14323844149867135618792049 10742883112400351714094037)
                ·
                  refine ⟨251786322946883243299079, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10742883112400351714094037 251786322946883243299079)
                  ·
                    rfl

theorem cell23_4413169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 4, 1, 2, 7].length) (baseStart_4413169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413169 prefixEnd_4413169 := by exact prefixLift 4413169
  have htrace : WordTrace (prefixWord ++ tailWord_4413169) baseStart_4413169 baseEnd_4413169 := by
    simpa [prefixWord, tailWord_4413169, baseEnd_4413169] using wordTrace_append hprefix tailTrace_4413169
  have hstable : (prefixWord ++ tailWord_4413169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413169).length < 2 ^ (prefixWord ++ tailWord_4413169).sum := by decide
  have hdescent : baseEnd_4413169 < baseStart_4413169 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413214 : List Nat := [4, 3, 2, 2, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4413214 : Nat := 118140960795 + 4413214 * 2 ^ 59
def prefixEnd_4413214 : Nat := 4983230072969 + 3 ^ 40 * 4413214 * 2
def baseEnd_4413214 : Nat := 2266100013151401513629005

theorem tailTrace_4413214 : CollatzResearch.WordTrace tailWord_4413214 prefixEnd_4413214 2266100013151401513629005 := by
  unfold tailWord_4413214
  simp only [CollatzResearch.WordTrace]
  refine ⟨20120392279210858723729837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107308758822457913193225797 20120392279210858723729837)
  ·
    refine ⟨7545147104704072021398689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 20120392279210858723729837 7545147104704072021398689)
    ·
      refine ⟨5658860328528054016049017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7545147104704072021398689 5658860328528054016049017)
      ·
        refine ⟨4244145246396040512036763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5658860328528054016049017 4244145246396040512036763)
        ·
          refine ⟨6366217869594060768055145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244145246396040512036763 6366217869594060768055145)
          ·
            refine ⟨4774663402195545576041359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6366217869594060768055145 4774663402195545576041359)
            ·
              refine ⟨7161995103293318364062039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4774663402195545576041359 7161995103293318364062039)
              ·
                refine ⟨10742992654939977546093059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7161995103293318364062039 10742992654939977546093059)
                ·
                  refine ⟨16114488982409966319139589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10742992654939977546093059 16114488982409966319139589)
                  ·
                    refine ⟨3021466684201868684838673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16114488982409966319139589 3021466684201868684838673)
                    ·
                      refine ⟨2266100013151401513629005, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021466684201868684838673 2266100013151401513629005)
                      ·
                        rfl

theorem cell23_4413214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 2, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4413214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413214 prefixEnd_4413214 := by exact prefixLift 4413214
  have htrace : WordTrace (prefixWord ++ tailWord_4413214) baseStart_4413214 baseEnd_4413214 := by
    simpa [prefixWord, tailWord_4413214, baseEnd_4413214] using wordTrace_append hprefix tailTrace_4413214
  have hstable : (prefixWord ++ tailWord_4413214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413214).length < 2 ^ (prefixWord ++ tailWord_4413214).sum := by decide
  have hdescent : baseEnd_4413214 < baseStart_4413214 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413219 : List Nat := [1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4]
def baseStart_4413219 : Nat := 118140960795 + 4413219 * 2 ^ 59
def prefixEnd_4413219 : Nat := 4983230072969 + 3 ^ 40 * 4413219 * 2
def baseEnd_4413219 : Nat := 2266102580554673994066481

theorem tailTrace_4413219 : CollatzResearch.WordTrace tailWord_4413219 prefixEnd_4413219 2266102580554673994066481 := by
  unfold tailWord_4413219
  simp only [CollatzResearch.WordTrace]
  refine ⟨160963320598668755643770711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107308880399112503762513807 160963320598668755643770711)
  ·
    refine ⟨241444980898003133465656067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160963320598668755643770711 241444980898003133465656067)
    ·
      refine ⟨362167471347004700198484101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241444980898003133465656067 362167471347004700198484101)
      ·
        refine ⟨67906400877563381287215769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 362167471347004700198484101 67906400877563381287215769)
        ·
          refine ⟨50929800658172535965411827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67906400877563381287215769 50929800658172535965411827)
          ·
            refine ⟨76394700987258803948117741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50929800658172535965411827 76394700987258803948117741)
            ·
              refine ⟨28648012870222051480544153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76394700987258803948117741 28648012870222051480544153)
              ·
                refine ⟨21486009652666538610408115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28648012870222051480544153 21486009652666538610408115)
                ·
                  refine ⟨32229014478999807915612173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21486009652666538610408115 32229014478999807915612173)
                  ·
                    refine ⟨12085880429624927968354565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32229014478999807915612173 12085880429624927968354565)
                    ·
                      refine ⟨2266102580554673994066481, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12085880429624927968354565 2266102580554673994066481)
                      ·
                        rfl

theorem cell23_4413219_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 2, 1, 3, 4].length) (baseStart_4413219 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413219 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413219 prefixEnd_4413219 := by exact prefixLift 4413219
  have htrace : WordTrace (prefixWord ++ tailWord_4413219) baseStart_4413219 baseEnd_4413219 := by
    simpa [prefixWord, tailWord_4413219, baseEnd_4413219] using wordTrace_append hprefix tailTrace_4413219
  have hstable : (prefixWord ++ tailWord_4413219).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413219).length < 2 ^ (prefixWord ++ tailWord_4413219).sum := by decide
  have hdescent : baseEnd_4413219 < baseStart_4413219 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413219) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413256 : List Nat := [2, 1, 3, 1, 1, 4, 1, 1, 4, 2, 3]
def baseStart_4413256 : Nat := 118140960795 + 4413256 * 2 ^ 59
def prefixEnd_4413256 : Nat := 4983230072969 + 3 ^ 40 * 4413256 * 2
def baseEnd_4413256 : Nat := 2266121579338890349303811

theorem tailTrace_4413256 : CollatzResearch.WordTrace tailWord_4413256 prefixEnd_4413256 2266121579338890349303811 := by
  unfold tailWord_4413256
  simp only [CollatzResearch.WordTrace]
  refine ⟨80482335049767355481433811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107309780066356473975245081 80482335049767355481433811)
  ·
    refine ⟨120723502574651033222150717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80482335049767355481433811 120723502574651033222150717)
    ·
      refine ⟨45271313465494137458306519, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120723502574651033222150717 45271313465494137458306519)
      ·
        refine ⟨67906970198241206187459779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45271313465494137458306519 67906970198241206187459779)
        ·
          refine ⟨101860455297361809281189669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67906970198241206187459779 101860455297361809281189669)
          ·
            refine ⟨19098835368255339240223063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101860455297361809281189669 19098835368255339240223063)
            ·
              refine ⟨28648253052383008860334595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19098835368255339240223063 28648253052383008860334595)
              ·
                refine ⟨42972379578574513290501893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28648253052383008860334595 42972379578574513290501893)
                ·
                  refine ⟨8057321170982721241969105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42972379578574513290501893 8057321170982721241969105)
                  ·
                    refine ⟨6042990878237040931476829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8057321170982721241969105 6042990878237040931476829)
                    ·
                      refine ⟨2266121579338890349303811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6042990878237040931476829 2266121579338890349303811)
                      ·
                        rfl

theorem cell23_4413256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 1, 1, 4, 2, 3].length) (baseStart_4413256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413256 prefixEnd_4413256 := by exact prefixLift 4413256
  have htrace : WordTrace (prefixWord ++ tailWord_4413256) baseStart_4413256 baseEnd_4413256 := by
    simpa [prefixWord, tailWord_4413256, baseEnd_4413256] using wordTrace_append hprefix tailTrace_4413256
  have hstable : (prefixWord ++ tailWord_4413256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413256).length < 2 ^ (prefixWord ++ tailWord_4413256).sum := by decide
  have hdescent : baseEnd_4413256 < baseStart_4413256 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413306 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 1, 5]
def baseStart_4413306 : Nat := 118140960795 + 4413306 * 2 ^ 59
def prefixEnd_4413306 : Nat := 4983230072969 + 3 ^ 40 * 4413306 * 2
def baseEnd_4413306 : Nat := 755382417790538384559527

theorem tailTrace_4413306 : CollatzResearch.WordTrace tailWord_4413306 prefixEnd_4413306 755382417790538384559527 := by
  unfold tailWord_4413306
  simp only [CollatzResearch.WordTrace]
  refine ⟨40241623437338392375546943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107310995832902379668125181 40241623437338392375546943)
  ·
    refine ⟨60362435156007588563320415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40241623437338392375546943 60362435156007588563320415)
    ·
      refine ⟨90543652734011382844980623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60362435156007588563320415 90543652734011382844980623)
      ·
        refine ⟨135815479101017074267470935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90543652734011382844980623 135815479101017074267470935)
        ·
          refine ⟨203723218651525611401206403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135815479101017074267470935 203723218651525611401206403)
          ·
            refine ⟨305584827977288417101809605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203723218651525611401206403 305584827977288417101809605)
            ·
              refine ⟨57297155245741578206589301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305584827977288417101809605 57297155245741578206589301)
              ·
                refine ⟨5371608304288272956867747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57297155245741578206589301 5371608304288272956867747)
                ·
                  refine ⟨8057412456432409435301621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5371608304288272956867747 8057412456432409435301621)
                  ·
                    refine ⟨755382417790538384559527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8057412456432409435301621 755382417790538384559527)
                    ·
                      rfl

theorem cell23_4413306_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 1, 5].length) (baseStart_4413306 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413306 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413306 prefixEnd_4413306 := by exact prefixLift 4413306
  have htrace : WordTrace (prefixWord ++ tailWord_4413306) baseStart_4413306 baseEnd_4413306 := by
    simpa [prefixWord, tailWord_4413306, baseEnd_4413306] using wordTrace_append hprefix tailTrace_4413306
  have hstable : (prefixWord ++ tailWord_4413306).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413306).length < 2 ^ (prefixWord ++ tailWord_4413306).sum := by decide
  have hdescent : baseEnd_4413306 < baseStart_4413306 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413306) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413310 : List Nat := [4, 2, 3, 1, 1, 2, 2, 2, 6]
def baseStart_4413310 : Nat := 118140960795 + 4413310 * 2 ^ 59
def prefixEnd_4413310 : Nat := 4983230072969 + 3 ^ 40 * 4413310 * 2
def baseEnd_4413310 : Nat := 251794367477137015336507

theorem tailTrace_4413310 : CollatzResearch.WordTrace tailWord_4413310 prefixEnd_4413310 251794367477137015336507 := by
  unfold tailWord_4413310
  simp only [CollatzResearch.WordTrace]
  refine ⟨20120829955167384773166673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107311093094226052123555589 20120829955167384773166673)
  ·
    refine ⟨15090622466375538579875005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20120829955167384773166673 15090622466375538579875005)
    ·
      refine ⟨5658983424890826967453127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15090622466375538579875005 5658983424890826967453127)
      ·
        refine ⟨8488475137336240451179691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5658983424890826967453127 8488475137336240451179691)
        ·
          refine ⟨12732712706004360676769537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8488475137336240451179691 12732712706004360676769537)
          ·
            refine ⟨9549534529503270507577153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12732712706004360676769537 9549534529503270507577153)
            ·
              refine ⟨7162150897127452880682865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9549534529503270507577153 7162150897127452880682865)
              ·
                refine ⟨5371613172845589660512149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7162150897127452880682865 5371613172845589660512149)
                ·
                  refine ⟨251794367477137015336507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5371613172845589660512149 251794367477137015336507)
                  ·
                    rfl

theorem cell23_4413310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 2, 2, 6].length) (baseStart_4413310 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413310 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413310 prefixEnd_4413310 := by exact prefixLift 4413310
  have htrace : WordTrace (prefixWord ++ tailWord_4413310) baseStart_4413310 baseEnd_4413310 := by
    simpa [prefixWord, tailWord_4413310, baseEnd_4413310] using wordTrace_append hprefix tailTrace_4413310
  have hstable : (prefixWord ++ tailWord_4413310).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413310).length < 2 ^ (prefixWord ++ tailWord_4413310).sum := by decide
  have hdescent : baseEnd_4413310 < baseStart_4413310 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413349 : List Nat := [1, 3, 1, 2, 1, 1, 1, 13]
def baseStart_4413349 : Nat := 118140960795 + 4413349 * 2 ^ 59
def prefixEnd_4413349 : Nat := 4983230072969 + 3 ^ 40 * 4413349 * 2
def baseEnd_4413349 : Nat := 83932197519991055016329

theorem tailTrace_4413349 : CollatzResearch.WordTrace tailWord_4413349 prefixEnd_4413349 83932197519991055016329 := by
  unfold tailWord_4413349
  simp only [CollatzResearch.WordTrace]
  refine ⟨160968062088197787846003101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107312041392131858564002067 160968062088197787846003101)
  ·
    refine ⟨60363023283074170442251163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160968062088197787846003101 60363023283074170442251163)
    ·
      refine ⟨90544534924611255663376745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60363023283074170442251163 90544534924611255663376745)
      ·
        refine ⟨67908401193458441747532559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90544534924611255663376745 67908401193458441747532559)
        ·
          refine ⟨101862601790187662621298839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67908401193458441747532559 101862601790187662621298839)
          ·
            refine ⟨152793902685281493931948259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101862601790187662621298839 152793902685281493931948259)
            ·
              refine ⟨229190854027922240897922389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152793902685281493931948259 229190854027922240897922389)
              ·
                refine ⟨83932197519991055016329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 13 229190854027922240897922389 83932197519991055016329)
                ·
                  rfl

theorem cell23_4413349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 13].length) (baseStart_4413349 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413349 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413349 prefixEnd_4413349 := by exact prefixLift 4413349
  have htrace : WordTrace (prefixWord ++ tailWord_4413349) baseStart_4413349 baseEnd_4413349 := by
    simpa [prefixWord, tailWord_4413349, baseEnd_4413349] using wordTrace_append hprefix tailTrace_4413349
  have hstable : (prefixWord ++ tailWord_4413349).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413349).length < 2 ^ (prefixWord ++ tailWord_4413349).sum := by decide
  have hdescent : baseEnd_4413349 < baseStart_4413349 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413363 : List Nat := [1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 3]
def baseStart_4413363 : Nat := 118140960795 + 4413363 * 2 ^ 59
def prefixEnd_4413363 : Nat := 4983230072969 + 3 ^ 40 * 4413363 * 2
def baseEnd_4413363 : Nat := 2266176521768921430665819

theorem tailTrace_4413363 : CollatzResearch.WordTrace tailWord_4413363 prefixEnd_4413363 2266176521768921430665819 := by
  unfold tailWord_4413363
  simp only [CollatzResearch.WordTrace]
  refine ⟨160968572710147068237012743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107312381806764712158008495 160968572710147068237012743)
  ·
    refine ⟨241452859065220602355519115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160968572710147068237012743 241452859065220602355519115)
    ·
      refine ⟨362179288597830903533278673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241452859065220602355519115 362179288597830903533278673)
      ·
        refine ⟨271634466448373177649959005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362179288597830903533278673 271634466448373177649959005)
        ·
          refine ⟨101862924918139941618734627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271634466448373177649959005 101862924918139941618734627)
          ·
            refine ⟨152794387377209912428101941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101862924918139941618734627 152794387377209912428101941)
            ·
              refine ⟨14324473816613429290134557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 152794387377209912428101941 14324473816613429290134557)
              ·
                refine ⟨5371677681230035983800459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14324473816613429290134557 5371677681230035983800459)
                ·
                  refine ⟨8057516521845053975700689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5371677681230035983800459 8057516521845053975700689)
                  ·
                    refine ⟨6043137391383790481775517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8057516521845053975700689 6043137391383790481775517)
                    ·
                      refine ⟨2266176521768921430665819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6043137391383790481775517 2266176521768921430665819)
                      ·
                        rfl

theorem cell23_4413363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 5, 3, 1, 2, 3].length) (baseStart_4413363 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413363 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413363 prefixEnd_4413363 := by exact prefixLift 4413363
  have htrace : WordTrace (prefixWord ++ tailWord_4413363) baseStart_4413363 baseEnd_4413363 := by
    simpa [prefixWord, tailWord_4413363, baseEnd_4413363] using wordTrace_append hprefix tailTrace_4413363
  have hstable : (prefixWord ++ tailWord_4413363).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413363).length < 2 ^ (prefixWord ++ tailWord_4413363).sum := by decide
  have hdescent : baseEnd_4413363 < baseStart_4413363 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413416 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 1, 5, 4]
def baseStart_4413416 : Nat := 118140960795 + 4413416 * 2 ^ 59
def prefixEnd_4413416 : Nat := 4983230072969 + 3 ^ 40 * 4413416 * 2
def baseEnd_4413416 : Nat := 2266203736243609723303075

theorem tailTrace_4413416 : CollatzResearch.WordTrace tailWord_4413416 prefixEnd_4413416 2266203736243609723303075 := by
  unfold tailWord_4413416
  simp only [CollatzResearch.WordTrace]
  refine ⟨80485252889477529144346051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107313670519303372192461401 80485252889477529144346051)
  ·
    refine ⟨120727879334216293716519077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80485252889477529144346051 120727879334216293716519077)
    ·
      refine ⟨22636477375165555071847327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120727879334216293716519077 22636477375165555071847327)
      ·
        refine ⟨33954716062748332607770991, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22636477375165555071847327 33954716062748332607770991)
        ·
          refine ⟨50932074094122498911656487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33954716062748332607770991 50932074094122498911656487)
          ·
            refine ⟨76398111141183748367484731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50932074094122498911656487 76398111141183748367484731)
            ·
              refine ⟨114597166711775622551227097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76398111141183748367484731 114597166711775622551227097)
              ·
                refine ⟨85947875033831716913420323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114597166711775622551227097 85947875033831716913420323)
                ·
                  refine ⟨128921812550747575370130485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85947875033831716913420323 128921812550747575370130485)
                  ·
                    refine ⟨12086419926632585190949733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128921812550747575370130485 12086419926632585190949733)
                    ·
                      refine ⟨2266203736243609723303075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12086419926632585190949733 2266203736243609723303075)
                      ·
                        rfl

theorem cell23_4413416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 1, 5, 4].length) (baseStart_4413416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413416 prefixEnd_4413416 := by exact prefixLift 4413416
  have htrace : WordTrace (prefixWord ++ tailWord_4413416) baseStart_4413416 baseEnd_4413416 := by
    simpa [prefixWord, tailWord_4413416, baseEnd_4413416] using wordTrace_append hprefix tailTrace_4413416
  have hstable : (prefixWord ++ tailWord_4413416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413416).length < 2 ^ (prefixWord ++ tailWord_4413416).sum := by decide
  have hdescent : baseEnd_4413416 < baseStart_4413416 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413436 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 1, 3, 5]
def baseStart_4413436 : Nat := 118140960795 + 4413436 * 2 ^ 59
def prefixEnd_4413436 : Nat := 4983230072969 + 3 ^ 40 * 4413436 * 2
def baseEnd_4413436 : Nat := 2266214005856699645052983

theorem tailTrace_4413436 : CollatzResearch.WordTrace tailWord_4413436 prefixEnd_4413436 2266214005856699645052983 := by
  unfold tailWord_4413436
  simp only [CollatzResearch.WordTrace]
  refine ⟨80485617619441300852210081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107314156825921734469613441 80485617619441300852210081)
  ·
    refine ⟨60364213214580975639157561, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80485617619441300852210081 60364213214580975639157561)
    ·
      refine ⟨45273159910935731729368171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60364213214580975639157561 45273159910935731729368171)
      ·
        refine ⟨67909739866403597594052257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45273159910935731729368171 67909739866403597594052257)
        ·
          refine ⟨50932304899802698195539193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67909739866403597594052257 50932304899802698195539193)
          ·
            refine ⟨38199228674852023646654395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50932304899802698195539193 38199228674852023646654395)
            ·
              refine ⟨57298843012278035469981593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38199228674852023646654395 57298843012278035469981593)
              ·
                refine ⟨42974132259208526602486195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57298843012278035469981593 42974132259208526602486195)
                ·
                  refine ⟨64461198388812789903729293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 42974132259208526602486195 64461198388812789903729293)
                  ·
                    refine ⟨24172949395804796213898485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 64461198388812789903729293 24172949395804796213898485)
                    ·
                      refine ⟨2266214005856699645052983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24172949395804796213898485 2266214005856699645052983)
                      ·
                        rfl

theorem cell23_4413436_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 1, 3, 5].length) (baseStart_4413436 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413436 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413436 prefixEnd_4413436 := by exact prefixLift 4413436
  have htrace : WordTrace (prefixWord ++ tailWord_4413436) baseStart_4413436 baseEnd_4413436 := by
    simpa [prefixWord, tailWord_4413436, baseEnd_4413436] using wordTrace_append hprefix tailTrace_4413436
  have hstable : (prefixWord ++ tailWord_4413436).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413436).length < 2 ^ (prefixWord ++ tailWord_4413436).sum := by decide
  have hdescent : baseEnd_4413436 < baseStart_4413436 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413436) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413444 : List Nat := [2, 3, 2, 4, 1, 1, 1, 3, 2, 1, 3]
def baseStart_4413444 : Nat := 118140960795 + 4413444 * 2 ^ 59
def prefixEnd_4413444 : Nat := 4983230072969 + 3 ^ 40 * 4413444 * 2
def baseEnd_4413444 : Nat := 2266218113701935613752947

theorem tailTrace_4413444 : CollatzResearch.WordTrace tailWord_4413444 prefixEnd_4413444 2266218113701935613752947 := by
  unfold tailWord_4413444
  simp only [CollatzResearch.WordTrace]
  refine ⟨80485763511426809535355693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107314351348569079380474257 80485763511426809535355693)
  ·
    refine ⟨30182161316785053575758385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80485763511426809535355693 30182161316785053575758385)
    ·
      refine ⟨22636620987588790181818789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30182161316785053575758385 22636620987588790181818789)
      ·
        refine ⟨4244366435172898159091023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22636620987588790181818789 4244366435172898159091023)
        ·
          refine ⟨6366549652759347238636535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244366435172898159091023 6366549652759347238636535)
          ·
            refine ⟨9549824479139020857954803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6366549652759347238636535 9549824479139020857954803)
            ·
              refine ⟨14324736718708531286932205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9549824479139020857954803 14324736718708531286932205)
              ·
                refine ⟨5371776269515699232599577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14324736718708531286932205 5371776269515699232599577)
                ·
                  refine ⟨4028832202136774424449683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5371776269515699232599577 4028832202136774424449683)
                  ·
                    refine ⟨6043248303205161636674525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4028832202136774424449683 6043248303205161636674525)
                    ·
                      refine ⟨2266218113701935613752947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6043248303205161636674525 2266218113701935613752947)
                      ·
                        rfl

theorem cell23_4413444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 3, 2, 1, 3].length) (baseStart_4413444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413444 prefixEnd_4413444 := by exact prefixLift 4413444
  have htrace : WordTrace (prefixWord ++ tailWord_4413444) baseStart_4413444 baseEnd_4413444 := by
    simpa [prefixWord, tailWord_4413444, baseEnd_4413444] using wordTrace_append hprefix tailTrace_4413444
  have hstable : (prefixWord ++ tailWord_4413444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413444).length < 2 ^ (prefixWord ++ tailWord_4413444).sum := by decide
  have hdescent : baseEnd_4413444 < baseStart_4413444 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413490 : List Nat := [3, 2, 1, 1, 2, 4, 1, 4, 5]
def baseStart_4413490 : Nat := 118140960795 + 4413490 * 2 ^ 59
def prefixEnd_4413490 : Nat := 4983230072969 + 3 ^ 40 * 4413490 * 2
def baseEnd_4413490 : Nat := 251804637090226937086415

theorem tailTrace_4413490 : CollatzResearch.WordTrace tailWord_4413490 prefixEnd_4413490 251804637090226937086415 := by
  unfold tailWord_4413490
  simp only [CollatzResearch.WordTrace]
  refine ⟨40243301195171742231721481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107315469853791312617923949 40243301195171742231721481)
  ·
    refine ⟨30182475896378806673791111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40243301195171742231721481 30182475896378806673791111)
    ·
      refine ⟨45273713844568210010686667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30182475896378806673791111 45273713844568210010686667)
      ·
        refine ⟨67910570766852315016030001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45273713844568210010686667 67910570766852315016030001)
        ·
          refine ⟨50932928075139236262022501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67910570766852315016030001 50932928075139236262022501)
          ·
            refine ⟨9549924014088606799129219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50932928075139236262022501 9549924014088606799129219)
            ·
              refine ⟨14324886021132910198693829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9549924014088606799129219 14324886021132910198693829)
              ·
                refine ⟨2685916128962420662255093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14324886021132910198693829 2685916128962420662255093)
                ·
                  refine ⟨251804637090226937086415, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2685916128962420662255093 251804637090226937086415)
                  ·
                    rfl

theorem cell23_4413490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 4, 1, 4, 5].length) (baseStart_4413490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413490 prefixEnd_4413490 := by exact prefixLift 4413490
  have htrace : WordTrace (prefixWord ++ tailWord_4413490) baseStart_4413490 baseEnd_4413490 := by
    simpa [prefixWord, tailWord_4413490, baseEnd_4413490] using wordTrace_append hprefix tailTrace_4413490
  have hstable : (prefixWord ++ tailWord_4413490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413490).length < 2 ^ (prefixWord ++ tailWord_4413490).sum := by decide
  have hdescent : baseEnd_4413490 < baseStart_4413490 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413540 : List Nat := [2, 3, 1, 1, 2, 1, 3, 2, 2, 4, 2]
def baseStart_4413540 : Nat := 118140960795 + 4413540 * 2 ^ 59
def prefixEnd_4413540 : Nat := 4983230072969 + 3 ^ 40 * 4413540 * 2
def baseEnd_4413540 : Nat := 2266267407844767238152505

theorem tailTrace_4413540 : CollatzResearch.WordTrace tailWord_4413540 prefixEnd_4413540 2266267407844767238152505 := by
  unfold tailWord_4413540
  simp only [CollatzResearch.WordTrace]
  refine ⟨80487514215252913733103037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107316685620337218310804049 80487514215252913733103037)
  ·
    refine ⟨30182817830719842649913639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80487514215252913733103037 30182817830719842649913639)
    ·
      refine ⟨45274226746079763974870459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30182817830719842649913639 45274226746079763974870459)
      ·
        refine ⟨67911340119119645962305689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45274226746079763974870459 67911340119119645962305689)
        ·
          refine ⟨50933505089339734471729267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67911340119119645962305689 50933505089339734471729267)
          ·
            refine ⟨76400257634009601707593901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50933505089339734471729267 76400257634009601707593901)
            ·
              refine ⟨28650096612753600640347713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76400257634009601707593901 28650096612753600640347713)
              ·
                refine ⟨21487572459565200480260785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28650096612753600640347713 21487572459565200480260785)
                ·
                  refine ⟨16115679344673900360195589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21487572459565200480260785 16115679344673900360195589)
                  ·
                    refine ⟨3021689877126356317536673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16115679344673900360195589 3021689877126356317536673)
                    ·
                      refine ⟨2266267407844767238152505, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021689877126356317536673 2266267407844767238152505)
                      ·
                        rfl

theorem cell23_4413540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 3, 2, 2, 4, 2].length) (baseStart_4413540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413540 prefixEnd_4413540 := by exact prefixLift 4413540
  have htrace : WordTrace (prefixWord ++ tailWord_4413540) baseStart_4413540 baseEnd_4413540 := by
    simpa [prefixWord, tailWord_4413540, baseEnd_4413540] using wordTrace_append hprefix tailTrace_4413540
  have hstable : (prefixWord ++ tailWord_4413540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413540).length < 2 ^ (prefixWord ++ tailWord_4413540).sum := by decide
  have hdescent : baseEnd_4413540 < baseStart_4413540 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413614 : List Nat := [4, 1, 4, 2, 1, 1, 1, 3, 6]
def baseStart_4413614 : Nat := 118140960795 + 4413614 * 2 ^ 59
def prefixEnd_4413614 : Nat := 4983230072969 + 3 ^ 40 * 4413614 * 2
def baseEnd_4413614 : Nat := 251811711712577772069685

theorem tailTrace_4413614 : CollatzResearch.WordTrace tailWord_4413614 prefixEnd_4413614 251811711712577772069685 := by
  unfold tailWord_4413614
  simp only [CollatzResearch.WordTrace]
  refine ⟨20122215929029717263049987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107318484954825158736266597 20122215929029717263049987)
  ·
    refine ⟨30183323893544575894574981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20122215929029717263049987 30183323893544575894574981)
    ·
      refine ⟨5659373230039607980232809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 30183323893544575894574981 5659373230039607980232809)
      ·
        refine ⟨4244529922529705985174607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5659373230039607980232809 4244529922529705985174607)
        ·
          refine ⟨6366794883794558977761911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244529922529705985174607 6366794883794558977761911)
          ·
            refine ⟨9550192325691838466642867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6366794883794558977761911 9550192325691838466642867)
            ·
              refine ⟨14325288488537757699964301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9550192325691838466642867 14325288488537757699964301)
              ·
                refine ⟨5371983183201659137486613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14325288488537757699964301 5371983183201659137486613)
                ·
                  refine ⟨251811711712577772069685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5371983183201659137486613 251811711712577772069685)
                  ·
                    rfl

theorem cell23_4413614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 2, 1, 1, 1, 3, 6].length) (baseStart_4413614 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413614 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413614 prefixEnd_4413614 := by exact prefixLift 4413614
  have htrace : WordTrace (prefixWord ++ tailWord_4413614) baseStart_4413614 baseEnd_4413614 := by
    simpa [prefixWord, tailWord_4413614, baseEnd_4413614] using wordTrace_append hprefix tailTrace_4413614
  have hstable : (prefixWord ++ tailWord_4413614).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413614).length < 2 ^ (prefixWord ++ tailWord_4413614).sum := by decide
  have hdescent : baseEnd_4413614 < baseStart_4413614 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413647 : List Nat := [1, 1, 2, 1, 1, 3, 7, 1, 1, 1, 4]
def baseStart_4413647 : Nat := 118140960795 + 4413647 * 2 ^ 59
def prefixEnd_4413647 : Nat := 4983230072969 + 3 ^ 40 * 4413647 * 2
def baseEnd_4413647 : Nat := 2266322350274798319514513

theorem tailTrace_4413647 : CollatzResearch.WordTrace tailWord_4413647 prefixEnd_4413647 2266322350274798319514513 := by
  unfold tailWord_4413647
  simp only [CollatzResearch.WordTrace]
  refine ⟨160978931041118184740351195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107319287360745456493567463 160978931041118184740351195)
  ·
    refine ⟨241468396561677277110526793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160978931041118184740351195 241468396561677277110526793)
    ·
      refine ⟨181101297421257957832895095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241468396561677277110526793 181101297421257957832895095)
      ·
        refine ⟨271651946131886936749342643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181101297421257957832895095 271651946131886936749342643)
        ·
          refine ⟨407477919197830405124013965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271651946131886936749342643 407477919197830405124013965)
          ·
            refine ⟨152804219699186401921505237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 407477919197830405124013965 152804219699186401921505237)
            ·
              refine ⟨3581348899199681295035279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 152804219699186401921505237 3581348899199681295035279)
              ·
                refine ⟨5372023348799521942552919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3581348899199681295035279 5372023348799521942552919)
                ·
                  refine ⟨8058035023199282913829379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5372023348799521942552919 8058035023199282913829379)
                  ·
                    refine ⟨12087052534798924370744069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8058035023199282913829379 12087052534798924370744069)
                    ·
                      refine ⟨2266322350274798319514513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12087052534798924370744069 2266322350274798319514513)
                      ·
                        rfl

theorem cell23_4413647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 7, 1, 1, 1, 4].length) (baseStart_4413647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413647 prefixEnd_4413647 := by exact prefixLift 4413647
  have htrace : WordTrace (prefixWord ++ tailWord_4413647) baseStart_4413647 baseEnd_4413647 := by
    simpa [prefixWord, tailWord_4413647, baseEnd_4413647] using wordTrace_append hprefix tailTrace_4413647
  have hstable : (prefixWord ++ tailWord_4413647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413647).length < 2 ^ (prefixWord ++ tailWord_4413647).sum := by decide
  have hdescent : baseEnd_4413647 < baseStart_4413647 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413653 : List Nat := [1, 3, 2, 4, 13]
def baseStart_4413653 : Nat := 118140960795 + 4413653 * 2 ^ 59
def prefixEnd_4413653 : Nat := 4983230072969 + 3 ^ 40 * 4413653 * 2
def baseEnd_4413653 : Nat := 3108814034511282984965

theorem tailTrace_4413653 : CollatzResearch.WordTrace tailWord_4413653 prefixEnd_4413653 3108814034511282984965 := by
  unfold tailWord_4413653
  simp only [CollatzResearch.WordTrace]
  refine ⟨160979149879096447765069613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107319433252730965176713075 160979149879096447765069613)
  ·
    refine ⟨60367181204661167911901105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 160979149879096447765069613 60367181204661167911901105)
    ·
      refine ⟨45275385903495875933925829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60367181204661167911901105 45275385903495875933925829)
      ·
        refine ⟨8489134856905476737611093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45275385903495875933925829 8489134856905476737611093)
        ·
          refine ⟨3108814034511282984965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 8489134856905476737611093 3108814034511282984965)
          ·
            rfl

theorem cell23_4413653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 13].length) (baseStart_4413653 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413653 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413653 prefixEnd_4413653 := by exact prefixLift 4413653
  have htrace : WordTrace (prefixWord ++ tailWord_4413653) baseStart_4413653 baseEnd_4413653 := by
    simpa [prefixWord, tailWord_4413653, baseEnd_4413653] using wordTrace_append hprefix tailTrace_4413653
  have hstable : (prefixWord ++ tailWord_4413653).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413653).length < 2 ^ (prefixWord ++ tailWord_4413653).sum := by decide
  have hdescent : baseEnd_4413653 < baseStart_4413653 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413683 : List Nat := [1, 1, 1, 2, 2, 4, 1, 2, 2, 7]
def baseStart_4413683 : Nat := 118140960795 + 4413683 * 2 ^ 59
def prefixEnd_4413683 : Nat := 4983230072969 + 3 ^ 40 * 4413683 * 2
def baseEnd_4413683 : Nat := 755446945192786726221449

theorem tailTrace_4413683 : CollatzResearch.WordTrace tailWord_4413683 prefixEnd_4413683 755446945192786726221449 := by
  unfold tailWord_4413683
  simp only [CollatzResearch.WordTrace]
  refine ⟨160980244068987762888661703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107320162712658508592441135 160980244068987762888661703)
  ·
    refine ⟨241470366103481644332992555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160980244068987762888661703 241470366103481644332992555)
    ·
      refine ⟨362205549155222466499488833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241470366103481644332992555 362205549155222466499488833)
      ·
        refine ⟨271654161866416849874616625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362205549155222466499488833 271654161866416849874616625)
        ·
          refine ⟨203740621399812637405962469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271654161866416849874616625 203740621399812637405962469)
          ·
            refine ⟨38201366512464869513617963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203740621399812637405962469 38201366512464869513617963)
            ·
              refine ⟨57302049768697304270426945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38201366512464869513617963 57302049768697304270426945)
              ·
                refine ⟨42976537326522978202820209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57302049768697304270426945 42976537326522978202820209)
                ·
                  refine ⟨32232402994892233652115157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42976537326522978202820209 32232402994892233652115157)
                  ·
                    refine ⟨755446945192786726221449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32232402994892233652115157 755446945192786726221449)
                    ·
                      rfl

theorem cell23_4413683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 2, 2, 7].length) (baseStart_4413683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413683 prefixEnd_4413683 := by exact prefixLift 4413683
  have htrace : WordTrace (prefixWord ++ tailWord_4413683) baseStart_4413683 baseEnd_4413683 := by
    simpa [prefixWord, tailWord_4413683, baseEnd_4413683] using wordTrace_append hprefix tailTrace_4413683
  have hstable : (prefixWord ++ tailWord_4413683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413683).length < 2 ^ (prefixWord ++ tailWord_4413683).sum := by decide
  have hdescent : baseEnd_4413683 < baseStart_4413683 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413697 : List Nat := [1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 3]
def baseStart_4413697 : Nat := 118140960795 + 4413697 * 2 ^ 59
def prefixEnd_4413697 : Nat := 4983230072969 + 3 ^ 40 * 4413697 * 2
def baseEnd_4413697 : Nat := 2266348024307523123889283

theorem tailTrace_4413697 : CollatzResearch.WordTrace tailWord_4413697 prefixEnd_4413697 2266348024307523123889283 := by
  unfold tailWord_4413697
  simp only [CollatzResearch.WordTrace]
  refine ⟨160980754690937043279671345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107320503127291362186447563 160980754690937043279671345)
  ·
    refine ⟨120735566018202782459753509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160980754690937043279671345 120735566018202782459753509)
    ·
      refine ⟨22637918628413021711203783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120735566018202782459753509 22637918628413021711203783)
      ·
        refine ⟨33956877942619532566805675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22637918628413021711203783 33956877942619532566805675)
        ·
          refine ⟨50935316913929298850208513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33956877942619532566805675 50935316913929298850208513)
          ·
            refine ⟨38201487685446974137656385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50935316913929298850208513 38201487685446974137656385)
            ·
              refine ⟨28651115764085230603242289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38201487685446974137656385 28651115764085230603242289)
              ·
                refine ⟨21488336823063922952431717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28651115764085230603242289 21488336823063922952431717)
                ·
                  refine ⟨4029063154324485553580947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21488336823063922952431717 4029063154324485553580947)
                  ·
                    refine ⟨6043594731486728330371421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029063154324485553580947 6043594731486728330371421)
                    ·
                      refine ⟨2266348024307523123889283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6043594731486728330371421 2266348024307523123889283)
                      ·
                        rfl

theorem cell23_4413697_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 2, 4, 1, 3].length) (baseStart_4413697 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413697 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413697 prefixEnd_4413697 := by exact prefixLift 4413697
  have htrace : WordTrace (prefixWord ++ tailWord_4413697) baseStart_4413697 baseEnd_4413697 := by
    simpa [prefixWord, tailWord_4413697, baseEnd_4413697] using wordTrace_append hprefix tailTrace_4413697
  have hstable : (prefixWord ++ tailWord_4413697).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413697).length < 2 ^ (prefixWord ++ tailWord_4413697).sum := by decide
  have hdescent : baseEnd_4413697 < baseStart_4413697 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413697) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413698 : List Nat := [3, 4, 1, 1, 2, 1, 1, 5, 1, 2, 2]
def baseStart_4413698 : Nat := 118140960795 + 4413698 * 2 ^ 59
def prefixEnd_4413698 : Nat := 4983230072969 + 3 ^ 40 * 4413698 * 2
def baseEnd_4413698 : Nat := 2266348537788177619976779

theorem tailTrace_4413698 : CollatzResearch.WordTrace tailWord_4413698 prefixEnd_4413698 2266348537788177619976779 := by
  unfold tailWord_4413698
  simp only [CollatzResearch.WordTrace]
  refine ⟨40245197790983355112614437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107320527442622280300305165 40245197790983355112614437)
  ·
    refine ⟨7545974585809379083615207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40245197790983355112614437 7545974585809379083615207)
    ·
      refine ⟨11318961878714068625422811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7545974585809379083615207 11318961878714068625422811)
      ·
        refine ⟨16978442818071102938134217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11318961878714068625422811 16978442818071102938134217)
        ·
          refine ⟨12733832113553327203600663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16978442818071102938134217 12733832113553327203600663)
          ·
            refine ⟨19100748170329990805400995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12733832113553327203600663 19100748170329990805400995)
            ·
              refine ⟨28651122255494986208101493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19100748170329990805400995 28651122255494986208101493)
              ·
                refine ⟨2686042711452654957009515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 28651122255494986208101493 2686042711452654957009515)
                ·
                  refine ⟨4029064067178982435514273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686042711452654957009515 4029064067178982435514273)
                  ·
                    refine ⟨3021798050384236826635705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4029064067178982435514273 3021798050384236826635705)
                    ·
                      refine ⟨2266348537788177619976779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021798050384236826635705 2266348537788177619976779)
                      ·
                        rfl

theorem cell23_4413698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 2, 1, 1, 5, 1, 2, 2].length) (baseStart_4413698 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413698 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413698 prefixEnd_4413698 := by exact prefixLift 4413698
  have htrace : WordTrace (prefixWord ++ tailWord_4413698) baseStart_4413698 baseEnd_4413698 := by
    simpa [prefixWord, tailWord_4413698, baseEnd_4413698] using wordTrace_append hprefix tailTrace_4413698
  have hstable : (prefixWord ++ tailWord_4413698).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413698).length < 2 ^ (prefixWord ++ tailWord_4413698).sum := by decide
  have hdescent : baseEnd_4413698 < baseStart_4413698 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413740 : List Nat := [2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 3]
def baseStart_4413740 : Nat := 118140960795 + 4413740 * 2 ^ 59
def prefixEnd_4413740 : Nat := 4983230072969 + 3 ^ 40 * 4413740 * 2
def baseEnd_4413740 : Nat := 2266370103975666455651585

theorem tailTrace_4413740 : CollatzResearch.WordTrace tailWord_4413740 prefixEnd_4413740 2266370103975666455651585 := by
  unfold tailWord_4413740
  simp only [CollatzResearch.WordTrace]
  refine ⟨80491161514890630811743337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107321548686520841082324449 80491161514890630811743337)
  ·
    refine ⟨60368371136167973108807503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80491161514890630811743337 60368371136167973108807503)
    ·
      refine ⟨90552556704251959663211255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60368371136167973108807503 90552556704251959663211255)
      ·
        refine ⟨135828835056377939494816883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90552556704251959663211255 135828835056377939494816883)
        ·
          refine ⟨203743252584566909242225325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135828835056377939494816883 203743252584566909242225325)
          ·
            refine ⟨76403719719212590965834497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203743252584566909242225325 76403719719212590965834497)
            ·
              refine ⟨57302789789409443224375873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76403719719212590965834497 57302789789409443224375873)
              ·
                refine ⟨42977092342057082418281905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57302789789409443224375873 42977092342057082418281905)
                ·
                  refine ⟨32232819256542811813711429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42977092342057082418281905 32232819256542811813711429)
                  ·
                    refine ⟨6043653610601777215070893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32232819256542811813711429 6043653610601777215070893)
                    ·
                      refine ⟨2266370103975666455651585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6043653610601777215070893 2266370103975666455651585)
                      ·
                        rfl

theorem cell23_4413740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 4, 3].length) (baseStart_4413740 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413740 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413740 prefixEnd_4413740 := by exact prefixLift 4413740
  have htrace : WordTrace (prefixWord ++ tailWord_4413740) baseStart_4413740 baseEnd_4413740 := by
    simpa [prefixWord, tailWord_4413740, baseEnd_4413740] using wordTrace_append hprefix tailTrace_4413740
  have hstable : (prefixWord ++ tailWord_4413740).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413740).length < 2 ^ (prefixWord ++ tailWord_4413740).sum := by decide
  have hdescent : baseEnd_4413740 < baseStart_4413740 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413754 : List Nat := [3, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2]
def baseStart_4413754 : Nat := 118140960795 + 4413754 * 2 ^ 59
def prefixEnd_4413754 : Nat := 4983230072969 + 3 ^ 40 * 4413754 * 2
def baseEnd_4413754 : Nat := 2266377292704829400876521

theorem tailTrace_4413754 : CollatzResearch.WordTrace tailWord_4413754 prefixEnd_4413754 2266377292704829400876521 := by
  unfold tailWord_4413754
  simp only [CollatzResearch.WordTrace]
  refine ⟨40245708412932635503624079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107321889101153694676330877 40245708412932635503624079)
  ·
    refine ⟨60368562619398953255436119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40245708412932635503624079 60368562619398953255436119)
    ·
      refine ⟨90552843929098429883154179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60368562619398953255436119 90552843929098429883154179)
      ·
        refine ⟨135829265893647644824731269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90552843929098429883154179 135829265893647644824731269)
        ·
          refine ⟨25467987355058933404637113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135829265893647644824731269 25467987355058933404637113)
          ·
            refine ⟨19100990516294200053477835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25467987355058933404637113 19100990516294200053477835)
            ·
              refine ⟨28651485774441300080216753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19100990516294200053477835 28651485774441300080216753)
              ·
                refine ⟨21488614330830975060162565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28651485774441300080216753 21488614330830975060162565)
                ·
                  refine ⟨4029115187030807823780481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21488614330830975060162565 4029115187030807823780481)
                  ·
                    refine ⟨3021836390273105867835361, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4029115187030807823780481 3021836390273105867835361)
                    ·
                      refine ⟨2266377292704829400876521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021836390273105867835361 2266377292704829400876521)
                      ·
                        rfl

theorem cell23_4413754_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 2, 4, 2, 2].length) (baseStart_4413754 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413754 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413754 prefixEnd_4413754 := by exact prefixLift 4413754
  have htrace : WordTrace (prefixWord ++ tailWord_4413754) baseStart_4413754 baseEnd_4413754 := by
    simpa [prefixWord, tailWord_4413754, baseEnd_4413754] using wordTrace_append hprefix tailTrace_4413754
  have hstable : (prefixWord ++ tailWord_4413754).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413754).length < 2 ^ (prefixWord ++ tailWord_4413754).sum := by decide
  have hdescent : baseEnd_4413754 < baseStart_4413754 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413754) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413777 : List Nat := [1, 2, 2, 1, 4, 4, 1, 1, 7]
def baseStart_4413777 : Nat := 118140960795 + 4413777 * 2 ^ 59
def prefixEnd_4413777 : Nat := 4983230072969 + 3 ^ 40 * 4413777 * 2
def baseEnd_4413777 : Nat := 251821011417764756765435

theorem tailTrace_4413777 : CollatzResearch.WordTrace tailWord_4413777 prefixEnd_4413777 251821011417764756765435 := by
  unfold tailWord_4413777
  simp only [CollatzResearch.WordTrace]
  refine ⟨160983672530647216942583585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107322448353764811295055723 160983672530647216942583585)
  ·
    refine ⟨120737754397985412706937689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160983672530647216942583585 120737754397985412706937689)
    ·
      refine ⟨90553315798489059530203267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120737754397985412706937689 90553315798489059530203267)
      ·
        refine ⟨135829973697733589295304901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90553315798489059530203267 135829973697733589295304901)
        ·
          refine ⟨25468120068325047992869669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135829973697733589295304901 25468120068325047992869669)
          ·
            refine ⟨4775272512810946498663063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25468120068325047992869669 4775272512810946498663063)
            ·
              refine ⟨7162908769216419747994595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775272512810946498663063 7162908769216419747994595)
              ·
                refine ⟨10744363153824629621991893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7162908769216419747994595 10744363153824629621991893)
                ·
                  refine ⟨251821011417764756765435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10744363153824629621991893 251821011417764756765435)
                  ·
                    rfl

theorem cell23_4413777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 4, 1, 1, 7].length) (baseStart_4413777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413777 prefixEnd_4413777 := by exact prefixLift 4413777
  have htrace : WordTrace (prefixWord ++ tailWord_4413777) baseStart_4413777 baseEnd_4413777 := by
    simpa [prefixWord, tailWord_4413777, baseEnd_4413777] using wordTrace_append hprefix tailTrace_4413777
  have hstable : (prefixWord ++ tailWord_4413777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413777).length < 2 ^ (prefixWord ++ tailWord_4413777).sum := by decide
  have hdescent : baseEnd_4413777 < baseStart_4413777 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413847 : List Nat := [1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 3]
def baseStart_4413847 : Nat := 118140960795 + 4413847 * 2 ^ 59
def prefixEnd_4413847 : Nat := 4983230072969 + 3 ^ 40 * 4413847 * 2
def baseEnd_4413847 : Nat := 2266425046405697537013593

theorem tailTrace_4413847 : CollatzResearch.WordTrace tailWord_4413847 prefixEnd_4413847 2266425046405697537013593 := by
  unfold tailWord_4413847
  simp only [CollatzResearch.WordTrace]
  refine ⟨160986225640393618897631795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107324150426929079265087863 160986225640393618897631795)
  ·
    refine ⟨241479338460590428346447693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160986225640393618897631795 241479338460590428346447693)
    ·
      refine ⟨90554751922721410629917885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241479338460590428346447693 90554751922721410629917885)
      ·
        refine ⟨33958031971020528986219207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90554751922721410629917885 33958031971020528986219207)
        ·
          refine ⟨50937047956530793479328811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33958031971020528986219207 50937047956530793479328811)
          ·
            refine ⟨76405571934796190218993217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50937047956530793479328811 76405571934796190218993217)
            ·
              refine ⟨57304178951097142664244913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76405571934796190218993217 57304178951097142664244913)
              ·
                refine ⟨42978134213322856998183685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 57304178951097142664244913 42978134213322856998183685)
                ·
                  refine ⟨8058400164998035687159441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42978134213322856998183685 8058400164998035687159441)
                  ·
                    refine ⟨6043800123748526765369581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8058400164998035687159441 6043800123748526765369581)
                    ·
                      refine ⟨2266425046405697537013593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6043800123748526765369581 2266425046405697537013593)
                      ·
                        rfl

theorem cell23_4413847_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 2, 2, 4, 2, 3].length) (baseStart_4413847 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413847 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413847 prefixEnd_4413847 := by exact prefixLift 4413847
  have htrace : WordTrace (prefixWord ++ tailWord_4413847) baseStart_4413847 baseEnd_4413847 := by
    simpa [prefixWord, tailWord_4413847, baseEnd_4413847] using wordTrace_append hprefix tailTrace_4413847
  have hstable : (prefixWord ++ tailWord_4413847).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413847).length < 2 ^ (prefixWord ++ tailWord_4413847).sum := by decide
  have hdescent : baseEnd_4413847 < baseStart_4413847 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413847) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413884 : List Nat := [2, 2, 2, 4, 1, 1, 3, 2, 6]
def baseStart_4413884 : Nat := 118140960795 + 4413884 * 2 ^ 59
def prefixEnd_4413884 : Nat := 4983230072969 + 3 ^ 40 * 4413884 * 2
def baseEnd_4413884 : Nat := 251827116132212654694547

theorem tailTrace_4413884 : CollatzResearch.WordTrace tailWord_4413884 prefixEnd_4413884 251827116132212654694547 := by
  unfold tailWord_4413884
  simp only [CollatzResearch.WordTrace]
  refine ⟨80493787570629787108364353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107325050094173049477819137 80493787570629787108364353)
  ·
    refine ⟨60370340677972340331273265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80493787570629787108364353 60370340677972340331273265)
    ·
      refine ⟨45277755508479255248454949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60370340677972340331273265 45277755508479255248454949)
      ·
        refine ⟨8489579157839860359085303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45277755508479255248454949 8489579157839860359085303)
        ·
          refine ⟨12734368736759790538627955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8489579157839860359085303 12734368736759790538627955)
          ·
            refine ⟨19101553105139685807941933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12734368736759790538627955 19101553105139685807941933)
            ·
              refine ⟨7163082414427382177978225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19101553105139685807941933 7163082414427382177978225)
              ·
                refine ⟨5372311810820536633483669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163082414427382177978225 5372311810820536633483669)
                ·
                  refine ⟨251827116132212654694547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5372311810820536633483669 251827116132212654694547)
                  ·
                    rfl

theorem cell23_4413884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 3, 2, 6].length) (baseStart_4413884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413884 prefixEnd_4413884 := by exact prefixLift 4413884
  have htrace : WordTrace (prefixWord ++ tailWord_4413884) baseStart_4413884 baseEnd_4413884 := by
    simpa [prefixWord, tailWord_4413884, baseEnd_4413884] using wordTrace_append hprefix tailTrace_4413884
  have hstable : (prefixWord ++ tailWord_4413884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413884).length < 2 ^ (prefixWord ++ tailWord_4413884).sum := by decide
  have hdescent : baseEnd_4413884 < baseStart_4413884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413914 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 1, 5]
def baseStart_4413914 : Nat := 118140960795 + 4413914 * 2 ^ 59
def prefixEnd_4413914 : Nat := 4983230072969 + 3 ^ 40 * 4413914 * 2
def baseEnd_4413914 : Nat := 755486483203182924958595

theorem tailTrace_4413914 : CollatzResearch.WordTrace tailWord_4413914 prefixEnd_4413914 755486483203182924958595 := by
  unfold tailWord_4413914
  simp only [CollatzResearch.WordTrace]
  refine ⟨40247167332787722335080199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107325779554100592893547197 40247167332787722335080199)
  ·
    refine ⟨60370750999181583502620299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40247167332787722335080199 60370750999181583502620299)
    ·
      refine ⟨90556126498772375253930449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60370750999181583502620299 90556126498772375253930449)
      ·
        refine ⟨67917094874079281440447837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90556126498772375253930449 67917094874079281440447837)
        ·
          refine ⟨25468910577779730540167939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67917094874079281440447837 25468910577779730540167939)
          ·
            refine ⟨38203365866669595810251909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25468910577779730540167939 38203365866669595810251909)
            ·
              refine ⟨7163131100000549214422233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38203365866669595810251909 7163131100000549214422233)
              ·
                refine ⟨5372348325000411910816675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163131100000549214422233 5372348325000411910816675)
                ·
                  refine ⟨8058522487500617866225013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5372348325000411910816675 8058522487500617866225013)
                  ·
                    refine ⟨755486483203182924958595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8058522487500617866225013 755486483203182924958595)
                    ·
                      rfl

theorem cell23_4413914_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 1, 5].length) (baseStart_4413914 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413914 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413914 prefixEnd_4413914 := by exact prefixLift 4413914
  have htrace : WordTrace (prefixWord ++ tailWord_4413914) baseStart_4413914 baseEnd_4413914 := by
    simpa [prefixWord, tailWord_4413914, baseEnd_4413914] using wordTrace_append hprefix tailTrace_4413914
  have hstable : (prefixWord ++ tailWord_4413914).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413914).length < 2 ^ (prefixWord ++ tailWord_4413914).sum := by decide
  have hdescent : baseEnd_4413914 < baseStart_4413914 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413914) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413922 : List Nat := [3, 3, 3, 2, 1, 2, 1, 3, 1, 4]
def baseStart_4413922 : Nat := 118140960795 + 4413922 * 2 ^ 59
def prefixEnd_4413922 : Nat := 4983230072969 + 3 ^ 40 * 4413922 * 2
def baseEnd_4413922 : Nat := 755487852484928247858583

theorem tailTrace_4413922 : CollatzResearch.WordTrace tailWord_4413922 prefixEnd_4413922 755487852484928247858583 := by
  unfold tailWord_4413922
  simp only [CollatzResearch.WordTrace]
  refine ⟨40247240278780476676653005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107325974076747937804408013 40247240278780476676653005)
  ·
    refine ⟨15092715104542678753744877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 40247240278780476676653005 15092715104542678753744877)
    ·
      refine ⟨5659768164203504532654329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15092715104542678753744877 5659768164203504532654329)
      ·
        refine ⟨4244826123152628399490747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5659768164203504532654329 4244826123152628399490747)
        ·
          refine ⟨6367239184728942599236121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244826123152628399490747 6367239184728942599236121)
          ·
            refine ⟨4775429388546706949427091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6367239184728942599236121 4775429388546706949427091)
            ·
              refine ⟨7163144082820060424140637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775429388546706949427091 7163144082820060424140637)
              ·
                refine ⟨2686179031057522659052739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7163144082820060424140637 2686179031057522659052739)
                ·
                  refine ⟨4029268546586283988579109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686179031057522659052739 4029268546586283988579109)
                  ·
                    refine ⟨755487852484928247858583, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029268546586283988579109 755487852484928247858583)
                    ·
                      rfl

theorem cell23_4413922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 1, 3, 1, 4].length) (baseStart_4413922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413922 prefixEnd_4413922 := by exact prefixLift 4413922
  have htrace : WordTrace (prefixWord ++ tailWord_4413922) baseStart_4413922 baseEnd_4413922 := by
    simpa [prefixWord, tailWord_4413922, baseEnd_4413922] using wordTrace_append hprefix tailTrace_4413922
  have hstable : (prefixWord ++ tailWord_4413922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413922).length < 2 ^ (prefixWord ++ tailWord_4413922).sum := by decide
  have hdescent : baseEnd_4413922 < baseStart_4413922 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413927 : List Nat := [1, 1, 5, 2, 1, 1, 2, 1, 3, 6]
def baseStart_4413927 : Nat := 118140960795 + 4413927 * 2 ^ 59
def prefixEnd_4413927 : Nat := 4983230072969 + 3 ^ 40 * 4413927 * 2
def baseEnd_4413927 : Nat := 755488708286019074671075

theorem tailTrace_4413927 : CollatzResearch.WordTrace tailWord_4413927 prefixEnd_4413927 755488708286019074671075 := by
  unfold tailWord_4413927
  simp only [CollatzResearch.WordTrace]
  refine ⟨160989143480103792560544035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107326095653402528373696023 160989143480103792560544035)
  ·
    refine ⟨241483715220155688840816053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160989143480103792560544035 241483715220155688840816053)
    ·
      refine ⟨22639098301889595828826505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241483715220155688840816053 22639098301889595828826505)
      ·
        refine ⟨16979323726417196871619879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22639098301889595828826505 16979323726417196871619879)
        ·
          refine ⟨25468985589625795307429819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16979323726417196871619879 25468985589625795307429819)
          ·
            refine ⟨38203478384438692961144729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25468985589625795307429819 38203478384438692961144729)
            ·
              refine ⟨28652608788329019720858547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38203478384438692961144729 28652608788329019720858547)
              ·
                refine ⟨42978913182493529581287821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28652608788329019720858547 42978913182493529581287821)
                ·
                  refine ⟨16117092443435073592982933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42978913182493529581287821 16117092443435073592982933)
                  ·
                    refine ⟨755488708286019074671075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16117092443435073592982933 755488708286019074671075)
                    ·
                      rfl

theorem cell23_4413927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 1, 2, 1, 3, 6].length) (baseStart_4413927 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413927 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413927 prefixEnd_4413927 := by exact prefixLift 4413927
  have htrace : WordTrace (prefixWord ++ tailWord_4413927) baseStart_4413927 baseEnd_4413927 := by
    simpa [prefixWord, tailWord_4413927, baseEnd_4413927] using wordTrace_append hprefix tailTrace_4413927
  have hstable : (prefixWord ++ tailWord_4413927).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413927).length < 2 ^ (prefixWord ++ tailWord_4413927).sum := by decide
  have hdescent : baseEnd_4413927 < baseStart_4413927 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413928 : List Nat := [2, 1, 4, 1, 1, 3, 3, 3, 1, 1, 3]
def baseStart_4413928 : Nat := 118140960795 + 4413928 * 2 ^ 59
def prefixEnd_4413928 : Nat := 4983230072969 + 3 ^ 40 * 4413928 * 2
def baseEnd_4413928 : Nat := 2266466638338711720100721

theorem tailTrace_4413928 : CollatzResearch.WordTrace tailWord_4413928 prefixEnd_4413928 2266466638338711720100721 := by
  unfold tailWord_4413928
  simp only [CollatzResearch.WordTrace]
  refine ⟨80494589976550084865665219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107326119968733446487553625 80494589976550084865665219)
  ·
    refine ⟨120741884964825127298497829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80494589976550084865665219 120741884964825127298497829)
    ·
      refine ⟨22639103430904711368468343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120741884964825127298497829 22639103430904711368468343)
      ·
        refine ⟨33958655146357067052702515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22639103430904711368468343 33958655146357067052702515)
        ·
          refine ⟨50937982719535600579053773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33958655146357067052702515 50937982719535600579053773)
          ·
            refine ⟨19101743519825850217145165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50937982719535600579053773 19101743519825850217145165)
            ·
              refine ⟨7163153819934693831429437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19101743519825850217145165 7163153819934693831429437)
              ·
                refine ⟨2686182682475510186786039, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7163153819934693831429437 2686182682475510186786039)
                ·
                  refine ⟨4029274023713265280179059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686182682475510186786039 4029274023713265280179059)
                  ·
                    refine ⟨6043911035569897920268589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029274023713265280179059 6043911035569897920268589)
                    ·
                      refine ⟨2266466638338711720100721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6043911035569897920268589 2266466638338711720100721)
                      ·
                        rfl

theorem cell23_4413928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 3, 1, 1, 3].length) (baseStart_4413928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413928 prefixEnd_4413928 := by exact prefixLift 4413928
  have htrace : WordTrace (prefixWord ++ tailWord_4413928) baseStart_4413928 baseEnd_4413928 := by
    simpa [prefixWord, tailWord_4413928, baseEnd_4413928] using wordTrace_append hprefix tailTrace_4413928
  have hstable : (prefixWord ++ tailWord_4413928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413928).length < 2 ^ (prefixWord ++ tailWord_4413928).sum := by decide
  have hdescent : baseEnd_4413928 < baseStart_4413928 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413938 : List Nat := [3, 2, 1, 4, 2, 1, 1, 2, 2, 3, 2]
def baseStart_4413938 : Nat := 118140960795 + 4413938 * 2 ^ 59
def prefixEnd_4413938 : Nat := 4983230072969 + 3 ^ 40 * 4413938 * 2
def baseEnd_4413938 : Nat := 2266471773145256680975675

theorem tailTrace_4413938 : CollatzResearch.WordTrace tailWord_4413938 prefixEnd_4413938 2266471773145256680975675 := by
  unfold tailWord_4413938
  simp only [CollatzResearch.WordTrace]
  refine ⟨40247386170765985359798617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107326363122042627626129645 40247386170765985359798617)
  ·
    refine ⟨30185539628074489019848963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40247386170765985359798617 30185539628074489019848963)
    ·
      refine ⟨45278309442111733529773445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30185539628074489019848963 45278309442111733529773445)
      ·
        refine ⟨8489683020395950036832521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45278309442111733529773445 8489683020395950036832521)
        ·
          refine ⟨6367262265296962527624391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8489683020395950036832521 6367262265296962527624391)
          ·
            refine ⟨9550893397945443791436587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367262265296962527624391 9550893397945443791436587)
            ·
              refine ⟨14326340096918165687154881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9550893397945443791436587 14326340096918165687154881)
              ·
                refine ⟨10744755072688624265366161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14326340096918165687154881 10744755072688624265366161)
                ·
                  refine ⟨8058566304516468199024621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10744755072688624265366161 8058566304516468199024621)
                  ·
                    refine ⟨3021962364193675574634233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8058566304516468199024621 3021962364193675574634233)
                    ·
                      refine ⟨2266471773145256680975675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3021962364193675574634233 2266471773145256680975675)
                      ·
                        rfl

theorem cell23_4413938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 1, 2, 2, 3, 2].length) (baseStart_4413938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413938 prefixEnd_4413938 := by exact prefixLift 4413938
  have htrace : WordTrace (prefixWord ++ tailWord_4413938) baseStart_4413938 baseEnd_4413938 := by
    simpa [prefixWord, tailWord_4413938, baseEnd_4413938] using wordTrace_append hprefix tailTrace_4413938
  have hstable : (prefixWord ++ tailWord_4413938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413938).length < 2 ^ (prefixWord ++ tailWord_4413938).sum := by decide
  have hdescent : baseEnd_4413938 < baseStart_4413938 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413944 : List Nat := [2, 1, 2, 1, 1, 4, 2, 4, 2, 4]
def baseStart_4413944 : Nat := 118140960795 + 4413944 * 2 ^ 59
def prefixEnd_4413944 : Nat := 4983230072969 + 3 ^ 40 * 4413944 * 2
def baseEnd_4413944 : Nat := 755491618009727885833549

theorem tailTrace_4413944 : CollatzResearch.WordTrace tailWord_4413944 prefixEnd_4413944 755491618009727885833549 := by
  unfold tailWord_4413944
  simp only [CollatzResearch.WordTrace]
  refine ⟨80494881760521102231956443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107326509014028136309275257 80494881760521102231956443)
  ·
    refine ⟨120742322640781653347934665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80494881760521102231956443 120742322640781653347934665)
    ·
      refine ⟨90556741980586240010950999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120742322640781653347934665 90556741980586240010950999)
      ·
        refine ⟨135835112970879360016426499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90556741980586240010950999 135835112970879360016426499)
        ·
          refine ⟨203752669456319040024639749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135835112970879360016426499 203752669456319040024639749)
          ·
            refine ⟨38203625523059820004619953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203752669456319040024639749 38203625523059820004619953)
            ·
              refine ⟨28652719142294865003464965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38203625523059820004619953 28652719142294865003464965)
              ·
                refine ⟨5372384839180287188149681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28652719142294865003464965 5372384839180287188149681)
                ·
                  refine ⟨4029288629385215391112261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5372384839180287188149681 4029288629385215391112261)
                  ·
                    refine ⟨755491618009727885833549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029288629385215391112261 755491618009727885833549)
                    ·
                      rfl

theorem cell23_4413944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 4, 2, 4, 2, 4].length) (baseStart_4413944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413944 prefixEnd_4413944 := by exact prefixLift 4413944
  have htrace : WordTrace (prefixWord ++ tailWord_4413944) baseStart_4413944 baseEnd_4413944 := by
    simpa [prefixWord, tailWord_4413944, baseEnd_4413944] using wordTrace_append hprefix tailTrace_4413944
  have hstable : (prefixWord ++ tailWord_4413944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413944).length < 2 ^ (prefixWord ++ tailWord_4413944).sum := by decide
  have hdescent : baseEnd_4413944 < baseStart_4413944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413965 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 1, 5]
def baseStart_4413965 : Nat := 118140960795 + 4413965 * 2 ^ 59
def prefixEnd_4413965 : Nat := 4983230072969 + 3 ^ 40 * 4413965 * 2
def baseEnd_4413965 : Nat := 755495212374309358446017

theorem tailTrace_4413965 : CollatzResearch.WordTrace tailWord_4413965 prefixEnd_4413965 755495212374309358446017 := by
  unfold tailWord_4413965
  simp only [CollatzResearch.WordTrace]
  refine ⟨160990529453966125050427349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107327019635977416700284899 160990529453966125050427349)
  ·
    refine ⟨3773215534077331055869391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 160990529453966125050427349 3773215534077331055869391)
    ·
      refine ⟨5659823301115996583804087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3773215534077331055869391 5659823301115996583804087)
      ·
        refine ⟨8489734951673994875706131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5659823301115996583804087 8489734951673994875706131)
        ·
          refine ⟨12734602427510992313559197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8489734951673994875706131 12734602427510992313559197)
          ·
            refine ⟨4775475910316622117584699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12734602427510992313559197 4775475910316622117584699)
            ·
              refine ⟨7163213865474933176377049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775475910316622117584699 7163213865474933176377049)
              ·
                refine ⟨5372410399106199882282787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163213865474933176377049 5372410399106199882282787)
                ·
                  refine ⟨8058615598659299823424181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5372410399106199882282787 8058615598659299823424181)
                  ·
                    refine ⟨755495212374309358446017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8058615598659299823424181 755495212374309358446017)
                    ·
                      rfl

theorem cell23_4413965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 1, 5].length) (baseStart_4413965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413965 prefixEnd_4413965 := by exact prefixLift 4413965
  have htrace : WordTrace (prefixWord ++ tailWord_4413965) baseStart_4413965 baseEnd_4413965 := by
    simpa [prefixWord, tailWord_4413965, baseEnd_4413965] using wordTrace_append hprefix tailTrace_4413965
  have hstable : (prefixWord ++ tailWord_4413965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413965).length < 2 ^ (prefixWord ++ tailWord_4413965).sum := by decide
  have hdescent : baseEnd_4413965 < baseStart_4413965 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413988 : List Nat := [2, 3, 1, 5, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4413988 : Nat := 118140960795 + 4413988 * 2 ^ 59
def prefixEnd_4413988 : Nat := 4983230072969 + 3 ^ 40 * 4413988 * 2
def baseEnd_4413988 : Nat := 2266497447177981485350445

theorem tailTrace_4413988 : CollatzResearch.WordTrace tailWord_4413988 prefixEnd_4413988 2266497447177981485350445 := by
  unfold tailWord_4413988
  simp only [CollatzResearch.WordTrace]
  refine ⟨80495684166441399989257309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107327578888588533319009745 80495684166441399989257309)
  ·
    refine ⟨30185881562415524995971491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80495684166441399989257309 30185881562415524995971491)
    ·
      refine ⟨45278822343623287493957237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30185881562415524995971491 45278822343623287493957237)
      ·
        refine ⟨4244889594714683202558491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45278822343623287493957237 4244889594714683202558491)
        ·
          refine ⟨6367334392072024803837737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4244889594714683202558491 6367334392072024803837737)
          ·
            refine ⟨4775500794054018602878303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6367334392072024803837737 4775500794054018602878303)
            ·
              refine ⟨7163251191081027904317455, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775500794054018602878303 7163251191081027904317455)
              ·
                refine ⟨10744876786621541856476183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7163251191081027904317455 10744876786621541856476183)
                ·
                  refine ⟨16117315179932312784714275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10744876786621541856476183 16117315179932312784714275)
                  ·
                    refine ⟨24175972769898469177071413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16117315179932312784714275 24175972769898469177071413)
                    ·
                      refine ⟨2266497447177981485350445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24175972769898469177071413 2266497447177981485350445)
                      ·
                        rfl

theorem cell23_4413988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 5, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4413988 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413988 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413988 prefixEnd_4413988 := by exact prefixLift 4413988
  have htrace : WordTrace (prefixWord ++ tailWord_4413988) baseStart_4413988 baseEnd_4413988 := by
    simpa [prefixWord, tailWord_4413988, baseEnd_4413988] using wordTrace_append hprefix tailTrace_4413988
  have hstable : (prefixWord ++ tailWord_4413988).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413988).length < 2 ^ (prefixWord ++ tailWord_4413988).sum := by decide
  have hdescent : baseEnd_4413988 < baseStart_4413988 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4413991 : List Nat := [1, 1, 7, 2, 2, 10]
def baseStart_4413991 : Nat := 118140960795 + 4413991 * 2 ^ 59
def prefixEnd_4413991 : Nat := 4983230072969 + 3 ^ 40 * 4413991 * 2
def baseEnd_4413991 : Nat := 9327156327654094541617

theorem tailTrace_4413991 : CollatzResearch.WordTrace tailWord_4413991 prefixEnd_4413991 9327156327654094541617 := by
  unfold tailWord_4413991
  simp only [CollatzResearch.WordTrace]
  refine ⟨160991477751871931490873827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107327651834581287660582551 160991477751871931490873827)
  ·
    refine ⟨241487216627807897236310741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160991477751871931490873827 241487216627807897236310741)
    ·
      refine ⟨5659856639714247591476033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 241487216627807897236310741 5659856639714247591476033)
      ·
        refine ⟨4244892479785685693607025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5659856639714247591476033 4244892479785685693607025)
        ·
          refine ⟨3183669359839264270205269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4244892479785685693607025 3183669359839264270205269)
          ·
            refine ⟨9327156327654094541617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3183669359839264270205269 9327156327654094541617)
            ·
              rfl

theorem cell23_4413991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 2, 10].length) (baseStart_4413991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4413991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4413991 prefixEnd_4413991 := by exact prefixLift 4413991
  have htrace : WordTrace (prefixWord ++ tailWord_4413991) baseStart_4413991 baseEnd_4413991 := by
    simpa [prefixWord, tailWord_4413991, baseEnd_4413991] using wordTrace_append hprefix tailTrace_4413991
  have hstable : (prefixWord ++ tailWord_4413991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4413991).length < 2 ^ (prefixWord ++ tailWord_4413991).sum := by decide
  have hdescent : baseEnd_4413991 < baseStart_4413991 := by decide
  rcases family_descends (prefixWord ++ tailWord_4413991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414001 : List Nat := [1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 3]
def baseStart_4414001 : Nat := 118140960795 + 4414001 * 2 ^ 59
def prefixEnd_4414001 : Nat := 4983230072969 + 3 ^ 40 * 4414001 * 2
def baseEnd_4414001 : Nat := 2266504122426489934487885

theorem tailTrace_4414001 : CollatzResearch.WordTrace tailWord_4414001 prefixEnd_4414001 2266504122426489934487885 := by
  unfold tailWord_4414001
  simp only [CollatzResearch.WordTrace]
  refine ⟨160991842481835703198737857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107327894987890468799158571 160991842481835703198737857)
  ·
    refine ⟨120743881861376777399053393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160991842481835703198737857 120743881861376777399053393)
    ·
      refine ⟨90557911396032583049290045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120743881861376777399053393 90557911396032583049290045)
      ·
        refine ⟨33959216773512218643483767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90557911396032583049290045 33959216773512218643483767)
        ·
          refine ⟨50938825160268327965225651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33959216773512218643483767 50938825160268327965225651)
          ·
            refine ⟨76408237740402491947838477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50938825160268327965225651 76408237740402491947838477)
            ·
              refine ⟨28653089152650934480439429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76408237740402491947838477 28653089152650934480439429)
              ·
                refine ⟨5372454216122050215082393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 28653089152650934480439429 5372454216122050215082393)
                ·
                  refine ⟨4029340662091537661311795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5372454216122050215082393 4029340662091537661311795)
                  ·
                    refine ⟨6044010993137306491967693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029340662091537661311795 6044010993137306491967693)
                    ·
                      refine ⟨2266504122426489934487885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6044010993137306491967693 2266504122426489934487885)
                      ·
                        rfl

theorem cell23_4414001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 4, 2, 1, 3].length) (baseStart_4414001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414001 prefixEnd_4414001 := by exact prefixLift 4414001
  have htrace : WordTrace (prefixWord ++ tailWord_4414001) baseStart_4414001 baseEnd_4414001 := by
    simpa [prefixWord, tailWord_4414001, baseEnd_4414001] using wordTrace_append hprefix tailTrace_4414001
  have hstable : (prefixWord ++ tailWord_4414001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414001).length < 2 ^ (prefixWord ++ tailWord_4414001).sum := by decide
  have hdescent : baseEnd_4414001 < baseStart_4414001 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414007 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 4]
def baseStart_4414007 : Nat := 118140960795 + 4414007 * 2 ^ 59
def prefixEnd_4414007 : Nat := 4983230072969 + 3 ^ 40 * 4414007 * 2
def baseEnd_4414007 : Nat := 2266507203310416911012857

theorem tailTrace_4414007 : CollatzResearch.WordTrace tailWord_4414007 prefixEnd_4414007 2266507203310416911012857 := by
  unfold tailWord_4414007
  simp only [CollatzResearch.WordTrace]
  refine ⟨160992061319813966223456275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107328040879875977482304183 160992061319813966223456275)
  ·
    refine ⟨241488091979720949335184413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160992061319813966223456275 241488091979720949335184413)
    ·
      refine ⟨90558034492395356000694155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241488091979720949335184413 90558034492395356000694155)
      ·
        refine ⟨135837051738593034001041233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90558034492395356000694155 135837051738593034001041233)
        ·
          refine ⟨101877788803944775500780925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135837051738593034001041233 101877788803944775500780925)
          ·
            refine ⟨38204170801479290812792847, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101877788803944775500780925 38204170801479290812792847)
            ·
              refine ⟨57306256202218936219189271, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38204170801479290812792847 57306256202218936219189271)
              ·
                refine ⟨85959384303328404328783907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57306256202218936219189271 85959384303328404328783907)
                ·
                  refine ⟨128939076454992606493175861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85959384303328404328783907 128939076454992606493175861)
                  ·
                    refine ⟨12088038417655556858735237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 128939076454992606493175861 12088038417655556858735237)
                    ·
                      refine ⟨2266507203310416911012857, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12088038417655556858735237 2266507203310416911012857)
                      ·
                        rfl

theorem cell23_4414007_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 1, 5, 4].length) (baseStart_4414007 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414007 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414007 prefixEnd_4414007 := by exact prefixLift 4414007
  have htrace : WordTrace (prefixWord ++ tailWord_4414007) baseStart_4414007 baseEnd_4414007 := by
    simpa [prefixWord, tailWord_4414007, baseEnd_4414007] using wordTrace_append hprefix tailTrace_4414007
  have hstable : (prefixWord ++ tailWord_4414007).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414007).length < 2 ^ (prefixWord ++ tailWord_4414007).sum := by decide
  have hdescent : baseEnd_4414007 < baseStart_4414007 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414007) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414027 : List Nat := [1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5]
def baseStart_4414027 : Nat := 118140960795 + 4414027 * 2 ^ 59
def prefixEnd_4414027 : Nat := 4983230072969 + 3 ^ 40 * 4414027 * 2
def baseEnd_4414027 : Nat := 2266517472923506832762765

theorem tailTrace_4414027 : CollatzResearch.WordTrace tailWord_4414027 prefixEnd_4414027 2266517472923506832762765 := by
  unfold tailWord_4414027
  simp only [CollatzResearch.WordTrace]
  refine ⟨160992790779741509639184335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107328527186494339759456223 160992790779741509639184335)
  ·
    refine ⟨241489186169612264458776503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160992790779741509639184335 241489186169612264458776503)
    ·
      refine ⟨362233779254418396688164755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241489186169612264458776503 362233779254418396688164755)
      ·
        refine ⟨543350668881627595032247133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362233779254418396688164755 543350668881627595032247133)
        ·
          refine ⟨203756500830610348137092675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543350668881627595032247133 203756500830610348137092675)
          ·
            refine ⟨305634751245915522205639013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203756500830610348137092675 305634751245915522205639013)
            ·
              refine ⟨57306515858609160413557315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 305634751245915522205639013 57306515858609160413557315)
              ·
                refine ⟨85959773787913740620335973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57306515858609160413557315 85959773787913740620335973)
                ·
                  refine ⟨16117457585233826366312995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85959773787913740620335973 16117457585233826366312995)
                  ·
                    refine ⟨24176186377850739549469493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16117457585233826366312995 24176186377850739549469493)
                    ·
                      refine ⟨2266517472923506832762765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24176186377850739549469493 2266517472923506832762765)
                      ·
                        rfl

theorem cell23_4414027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 4, 1, 4, 1, 5].length) (baseStart_4414027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414027 prefixEnd_4414027 := by exact prefixLift 4414027
  have htrace : WordTrace (prefixWord ++ tailWord_4414027) baseStart_4414027 baseEnd_4414027 := by
    simpa [prefixWord, tailWord_4414027, baseEnd_4414027] using wordTrace_append hprefix tailTrace_4414027
  have hstable : (prefixWord ++ tailWord_4414027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414027).length < 2 ^ (prefixWord ++ tailWord_4414027).sum := by decide
  have hdescent : baseEnd_4414027 < baseStart_4414027 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414058 : List Nat := [3, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2]
def baseStart_4414058 : Nat := 118140960795 + 4414058 * 2 ^ 59
def prefixEnd_4414058 : Nat := 4983230072969 + 3 ^ 40 * 4414058 * 2
def baseEnd_4414058 : Nat := 2266533390823796211475123

theorem tailTrace_4414058 : CollatzResearch.WordTrace tailWord_4414058 prefixEnd_4414058 2266533390823796211475123 := by
  unfold tailWord_4414058
  simp only [CollatzResearch.WordTrace]
  refine ⟨40248480360657300483390707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107329280961752801289041885 40248480360657300483390707)
  ·
    refine ⟨60372720540985950725086061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40248480360657300483390707 60372720540985950725086061)
    ·
      refine ⟨22639770202869731521907273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60372720540985950725086061 22639770202869731521907273)
      ·
        refine ⟨16979827652152298641430455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 22639770202869731521907273 16979827652152298641430455)
        ·
          refine ⟨25469741478228447962145683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16979827652152298641430455 25469741478228447962145683)
          ·
            refine ⟨38204612217342671943218525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25469741478228447962145683 38204612217342671943218525)
            ·
              refine ⟨14326729581503501978706947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38204612217342671943218525 14326729581503501978706947)
              ·
                refine ⟨21490094372255252968060421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14326729581503501978706947 21490094372255252968060421)
                ·
                  refine ⟨4029392694797859931511329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21490094372255252968060421 4029392694797859931511329)
                  ·
                    refine ⟨3022044521098394948633497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4029392694797859931511329 3022044521098394948633497)
                    ·
                      refine ⟨2266533390823796211475123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022044521098394948633497 2266533390823796211475123)
                      ·
                        rfl

theorem cell23_4414058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 1, 4, 2, 2].length) (baseStart_4414058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414058 prefixEnd_4414058 := by exact prefixLift 4414058
  have htrace : WordTrace (prefixWord ++ tailWord_4414058) baseStart_4414058 baseEnd_4414058 := by
    simpa [prefixWord, tailWord_4414058, baseEnd_4414058] using wordTrace_append hprefix tailTrace_4414058
  have hstable : (prefixWord ++ tailWord_4414058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414058).length < 2 ^ (prefixWord ++ tailWord_4414058).sum := by decide
  have hdescent : baseEnd_4414058 < baseStart_4414058 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414094 : List Nat := [4, 1, 1, 3, 1, 1, 1, 3, 1, 7]
def baseStart_4414094 : Nat := 118140960795 + 4414094 * 2 ^ 59
def prefixEnd_4414094 : Nat := 4983230072969 + 3 ^ 40 * 4414094 * 2
def baseEnd_4414094 : Nat := 755517292042452690208319

theorem tailTrace_4414094 : CollatzResearch.WordTrace tailWord_4414094 prefixEnd_4414094 755517292042452690208319 := by
  unfold tailWord_4414094
  simp only [CollatzResearch.WordTrace]
  refine ⟨20124404308812347510234167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107330156313665853387915557 20124404308812347510234167)
  ·
    refine ⟨30186606463218521265351251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20124404308812347510234167 30186606463218521265351251)
    ·
      refine ⟨45279909694827781898026877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30186606463218521265351251 45279909694827781898026877)
      ·
        refine ⟨16979966135560418211760079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45279909694827781898026877 16979966135560418211760079)
        ·
          refine ⟨25469949203340627317640119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16979966135560418211760079 25469949203340627317640119)
          ·
            refine ⟨38204923805010940976460179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25469949203340627317640119 38204923805010940976460179)
            ·
              refine ⟨57307385707516411464690269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38204923805010940976460179 57307385707516411464690269)
              ·
                refine ⟨21490269640318654299258851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57307385707516411464690269 21490269640318654299258851)
                ·
                  refine ⟨32235404460477981448888277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21490269640318654299258851 32235404460477981448888277)
                  ·
                    refine ⟨755517292042452690208319, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32235404460477981448888277 755517292042452690208319)
                    ·
                      rfl

theorem cell23_4414094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 3, 1, 7].length) (baseStart_4414094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414094 prefixEnd_4414094 := by exact prefixLift 4414094
  have htrace : WordTrace (prefixWord ++ tailWord_4414094) baseStart_4414094 baseEnd_4414094 := by
    simpa [prefixWord, tailWord_4414094, baseEnd_4414094] using wordTrace_append hprefix tailTrace_4414094
  have hstable : (prefixWord ++ tailWord_4414094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414094).length < 2 ^ (prefixWord ++ tailWord_4414094).sum := by decide
  have hdescent : baseEnd_4414094 < baseStart_4414094 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414097 : List Nat := [1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 8]
def baseStart_4414097 : Nat := 118140960795 + 4414097 * 2 ^ 59
def prefixEnd_4414097 : Nat := 4983230072969 + 3 ^ 40 * 4414097 * 2
def baseEnd_4414097 : Nat := 2266553416569321558887443

theorem tailTrace_4414097 : CollatzResearch.WordTrace tailWord_4414097 prefixEnd_4414097 2266553416569321558887443 := by
  unfold tailWord_4414097
  simp only [CollatzResearch.WordTrace]
  refine ⟨160995343889487911594232545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107330229259658607729488363 160995343889487911594232545)
  ·
    refine ⟨120746507917115933695674409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160995343889487911594232545 120746507917115933695674409)
    ·
      refine ⟨90559880937836950271755807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120746507917115933695674409 90559880937836950271755807)
      ·
        refine ⟨135839821406755425407633711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90559880937836950271755807 135839821406755425407633711)
        ·
          refine ⟨203759732110133138111450567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135839821406755425407633711 203759732110133138111450567)
          ·
            refine ⟨305639598165199707167175851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203759732110133138111450567 305639598165199707167175851)
            ·
              refine ⟨458459397247799560750763777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305639598165199707167175851 458459397247799560750763777)
              ·
                refine ⟨343844547935849670563072833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458459397247799560750763777 343844547935849670563072833)
                ·
                  refine ⟨257883410951887252922304625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 343844547935849670563072833 257883410951887252922304625)
                  ·
                    refine ⟨193412558213915439691728469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 257883410951887252922304625 193412558213915439691728469)
                    ·
                      refine ⟨2266553416569321558887443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 193412558213915439691728469 2266553416569321558887443)
                      ·
                        rfl

theorem cell23_4414097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 8].length) (baseStart_4414097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414097 prefixEnd_4414097 := by exact prefixLift 4414097
  have htrace : WordTrace (prefixWord ++ tailWord_4414097) baseStart_4414097 baseEnd_4414097 := by
    simpa [prefixWord, tailWord_4414097, baseEnd_4414097] using wordTrace_append hprefix tailTrace_4414097
  have hstable : (prefixWord ++ tailWord_4414097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414097).length < 2 ^ (prefixWord ++ tailWord_4414097).sum := by decide
  have hdescent : baseEnd_4414097 < baseStart_4414097 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414098 : List Nat := [3, 2, 3, 1, 2, 1, 3, 3, 5]
def baseStart_4414098 : Nat := 118140960795 + 4414098 * 2 ^ 59
def prefixEnd_4414098 : Nat := 4983230072969 + 3 ^ 40 * 4414098 * 2
def baseEnd_4414098 : Nat := 251839325561108450552771

theorem tailTrace_4414098 : CollatzResearch.WordTrace tailWord_4414098 prefixEnd_4414098 251839325561108450552771 := by
  unfold tailWord_4414098
  simp only [CollatzResearch.WordTrace]
  refine ⟨40248845090621072191254737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107330253574989525843345965 40248845090621072191254737)
  ·
    refine ⟨30186633817965804143441053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40248845090621072191254737 30186633817965804143441053)
    ·
      refine ⟨11319987681737176553790395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30186633817965804143441053 11319987681737176553790395)
      ·
        refine ⟨16979981522605764830685593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11319987681737176553790395 16979981522605764830685593)
        ·
          refine ⟨12734986141954323623014195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16979981522605764830685593 12734986141954323623014195)
          ·
            refine ⟨19102479212931485434521293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12734986141954323623014195 19102479212931485434521293)
            ·
              refine ⟨7163429704849307037945485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19102479212931485434521293 7163429704849307037945485)
              ·
                refine ⟨2686286139318490139229557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7163429704849307037945485 2686286139318490139229557)
                ·
                  refine ⟨251839325561108450552771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686286139318490139229557 251839325561108450552771)
                  ·
                    rfl

theorem cell23_4414098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 3, 3, 5].length) (baseStart_4414098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414098 prefixEnd_4414098 := by exact prefixLift 4414098
  have htrace : WordTrace (prefixWord ++ tailWord_4414098) baseStart_4414098 baseEnd_4414098 := by
    simpa [prefixWord, tailWord_4414098, baseEnd_4414098] using wordTrace_append hprefix tailTrace_4414098
  have hstable : (prefixWord ++ tailWord_4414098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414098).length < 2 ^ (prefixWord ++ tailWord_4414098).sum := by decide
  have hdescent : baseEnd_4414098 < baseStart_4414098 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414104 : List Nat := [2, 1, 2, 4, 1, 1, 2, 2, 1, 2, 5]
def baseStart_4414104 : Nat := 118140960795 + 4414104 * 2 ^ 59
def prefixEnd_4414104 : Nat := 4983230072969 + 3 ^ 40 * 4414104 * 2
def baseEnd_4414104 : Nat := 2266557010933903031499911

theorem tailTrace_4414104 : CollatzResearch.WordTrace tailWord_4414104 prefixEnd_4414104 2266557010933903031499911 := by
  unfold tailWord_4414104
  simp only [CollatzResearch.WordTrace]
  refine ⟨80497799600231275894868683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107330399466975034526491577 80497799600231275894868683)
  ·
    refine ⟨120746699400346913842303025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80497799600231275894868683 120746699400346913842303025)
    ·
      refine ⟨90560024550260185381727269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120746699400346913842303025 90560024550260185381727269)
      ·
        refine ⟨16980004603173784759073863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90560024550260185381727269 16980004603173784759073863)
        ·
          refine ⟨25470006904760677138610795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16980004603173784759073863 25470006904760677138610795)
          ·
            refine ⟨38205010357141015707916193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25470006904760677138610795 38205010357141015707916193)
            ·
              refine ⟨28653757767855761780937145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38205010357141015707916193 28653757767855761780937145)
              ·
                refine ⟨21490318325891821335702859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28653757767855761780937145 21490318325891821335702859)
                ·
                  refine ⟨32235477488837732003554289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21490318325891821335702859 32235477488837732003554289)
                  ·
                    refine ⟨24176608116628299002665717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32235477488837732003554289 24176608116628299002665717)
                    ·
                      refine ⟨2266557010933903031499911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24176608116628299002665717 2266557010933903031499911)
                      ·
                        rfl

theorem cell23_4414104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_4414104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414104 prefixEnd_4414104 := by exact prefixLift 4414104
  have htrace : WordTrace (prefixWord ++ tailWord_4414104) baseStart_4414104 baseEnd_4414104 := by
    simpa [prefixWord, tailWord_4414104, baseEnd_4414104] using wordTrace_append hprefix tailTrace_4414104
  have hstable : (prefixWord ++ tailWord_4414104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414104).length < 2 ^ (prefixWord ++ tailWord_4414104).sum := by decide
  have hdescent : baseEnd_4414104 < baseStart_4414104 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414145 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 2, 5]
def baseStart_4414145 : Nat := 118140960795 + 4414145 * 2 ^ 59
def prefixEnd_4414145 : Nat := 4983230072969 + 3 ^ 40 * 4414145 * 2
def baseEnd_4414145 : Nat := 755526021213579123695741

theorem tailTrace_4414145 : CollatzResearch.WordTrace tailWord_4414145 prefixEnd_4414145 755526021213579123695741 := by
  unfold tailWord_4414145
  simp only [CollatzResearch.WordTrace]
  refine ⟨160997094593314015791979889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107331396395542677194653259 160997094593314015791979889)
  ·
    refine ⟨120747820944985511843984917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 160997094593314015791979889 120747820944985511843984917)
    ·
      refine ⟨5660054106796195867686793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 120747820944985511843984917 5660054106796195867686793)
      ·
        refine ⟨4245040580097146900765095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5660054106796195867686793 4245040580097146900765095)
        ·
          refine ⟨6367560870145720351147643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245040580097146900765095 6367560870145720351147643)
          ·
            refine ⟨9551341305218580526721465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367560870145720351147643 9551341305218580526721465)
            ·
              refine ⟨7163505978913935395041099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9551341305218580526721465 7163505978913935395041099)
              ·
                refine ⟨10745258968370903092561649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7163505978913935395041099 10745258968370903092561649)
                ·
                  refine ⟨8058944226278177319421237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10745258968370903092561649 8058944226278177319421237)
                  ·
                    refine ⟨755526021213579123695741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8058944226278177319421237 755526021213579123695741)
                    ·
                      rfl

theorem cell23_4414145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 2, 5].length) (baseStart_4414145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414145 prefixEnd_4414145 := by exact prefixLift 4414145
  have htrace : WordTrace (prefixWord ++ tailWord_4414145) baseStart_4414145 baseEnd_4414145 := by
    simpa [prefixWord, tailWord_4414145, baseEnd_4414145] using wordTrace_append hprefix tailTrace_4414145
  have hstable : (prefixWord ++ tailWord_4414145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414145).length < 2 ^ (prefixWord ++ tailWord_4414145).sum := by decide
  have hdescent : baseEnd_4414145 < baseStart_4414145 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414148 : List Nat := [2, 3, 3, 1, 1, 3, 2, 1, 2, 1, 4]
def baseStart_4414148 : Nat := 118140960795 + 4414148 * 2 ^ 59
def prefixEnd_4414148 : Nat := 4983230072969 + 3 ^ 40 * 4414148 * 2
def baseEnd_4414148 : Nat := 2266579604082700859349709

theorem tailTrace_4414148 : CollatzResearch.WordTrace tailWord_4414148 prefixEnd_4414148 2266579604082700859349709 := by
  unfold tailWord_4414148
  simp only [CollatzResearch.WordTrace]
  refine ⟨80498602006151573652169549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107331469341535431536226065 80498602006151573652169549)
  ·
    refine ⟨30186975752306840119563581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80498602006151573652169549 30186975752306840119563581)
    ·
      refine ⟨11320115907115065044836343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30186975752306840119563581 11320115907115065044836343)
      ·
        refine ⟨16980173860672597567254515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11320115907115065044836343 16980173860672597567254515)
        ·
          refine ⟨25470260791008896350881773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16980173860672597567254515 25470260791008896350881773)
          ·
            refine ⟨9551347796628336131580665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25470260791008896350881773 9551347796628336131580665)
            ·
              refine ⟨7163510847471252098685499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9551347796628336131580665 7163510847471252098685499)
              ·
                refine ⟨10745266271206878148028249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7163510847471252098685499 10745266271206878148028249)
                ·
                  refine ⟨8058949703405158611021187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10745266271206878148028249 8058949703405158611021187)
                  ·
                    refine ⟨12088424555107737916531781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8058949703405158611021187 12088424555107737916531781)
                    ·
                      refine ⟨2266579604082700859349709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12088424555107737916531781 2266579604082700859349709)
                      ·
                        rfl

theorem cell23_4414148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 2, 1, 2, 1, 4].length) (baseStart_4414148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414148 prefixEnd_4414148 := by exact prefixLift 4414148
  have htrace : WordTrace (prefixWord ++ tailWord_4414148) baseStart_4414148 baseEnd_4414148 := by
    simpa [prefixWord, tailWord_4414148, baseEnd_4414148] using wordTrace_append hprefix tailTrace_4414148
  have hstable : (prefixWord ++ tailWord_4414148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414148).length < 2 ^ (prefixWord ++ tailWord_4414148).sum := by decide
  have hdescent : baseEnd_4414148 < baseStart_4414148 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414175 : List Nat := [1, 1, 2, 3, 2, 3, 4, 2, 1, 4]
def baseStart_4414175 : Nat := 118140960795 + 4414175 * 2 ^ 59
def prefixEnd_4414175 : Nat := 4983230072969 + 3 ^ 40 * 4414175 * 2
def baseEnd_4414175 : Nat := 755531156020124084570695

theorem tailTrace_4414175 : CollatzResearch.WordTrace tailWord_4414175 prefixEnd_4414175 755531156020124084570695 := by
  unfold tailWord_4414175
  simp only [CollatzResearch.WordTrace]
  refine ⟨160998188783205330915571979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107332125855470220610381319 160998188783205330915571979)
  ·
    refine ⟨241497283174807996373357969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 160998188783205330915571979 241497283174807996373357969)
    ·
      refine ⟨181122962381105997280018477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241497283174807996373357969 181122962381105997280018477)
      ·
        refine ⟨67921110892914748980006929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181122962381105997280018477 67921110892914748980006929)
        ·
          refine ⟨50940833169686061735005197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67921110892914748980006929 50940833169686061735005197)
          ·
            refine ⟨19102812438632273150626949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50940833169686061735005197 19102812438632273150626949)
            ·
              refine ⟨3581777332243551215742553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19102812438632273150626949 3581777332243551215742553)
              ·
                refine ⟨2686332999182663411806915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3581777332243551215742553 2686332999182663411806915)
                ·
                  refine ⟨4029499498773995117710373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686332999182663411806915 4029499498773995117710373)
                  ·
                    refine ⟨755531156020124084570695, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4029499498773995117710373 755531156020124084570695)
                    ·
                      rfl

theorem cell23_4414175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 4, 2, 1, 4].length) (baseStart_4414175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414175 prefixEnd_4414175 := by exact prefixLift 4414175
  have htrace : WordTrace (prefixWord ++ tailWord_4414175) baseStart_4414175 baseEnd_4414175 := by
    simpa [prefixWord, tailWord_4414175, baseEnd_4414175] using wordTrace_append hprefix tailTrace_4414175
  have hstable : (prefixWord ++ tailWord_4414175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414175).length < 2 ^ (prefixWord ++ tailWord_4414175).sum := by decide
  have hdescent : baseEnd_4414175 < baseStart_4414175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414241 : List Nat := [1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 5]
def baseStart_4414241 : Nat := 118140960795 + 4414241 * 2 ^ 59
def prefixEnd_4414241 : Nat := 4983230072969 + 3 ^ 40 * 4414241 * 2
def baseEnd_4414241 : Nat := 2266627357783568995486781

theorem tailTrace_4414241 : CollatzResearch.WordTrace tailWord_4414241 prefixEnd_4414241 2266627357783568995486781 := by
  unfold tailWord_4414241
  simp only [CollatzResearch.WordTrace]
  refine ⟨161000596000966224187474577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107333730667310816124983051 161000596000966224187474577)
  ·
    refine ⟨120750447000724668140605933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161000596000966224187474577 120750447000724668140605933)
    ·
      refine ⟨45281417625271750552727225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120750447000724668140605933 45281417625271750552727225)
      ·
        refine ⟨33961063218953812914545419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45281417625271750552727225 33961063218953812914545419)
        ·
          refine ⟨50941594828430719371818129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33961063218953812914545419 50941594828430719371818129)
          ·
            refine ⟨38206196121323039528863597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50941594828430719371818129 38206196121323039528863597)
            ·
              refine ⟨14327323545496139823323849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38206196121323039528863597 14327323545496139823323849)
              ·
                refine ⟨10745492659122104867492887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14327323545496139823323849 10745492659122104867492887)
                ·
                  refine ⟨16118238988683157301239331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10745492659122104867492887 16118238988683157301239331)
                  ·
                    refine ⟨24177358483024735951858997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16118238988683157301239331 24177358483024735951858997)
                    ·
                      refine ⟨2266627357783568995486781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24177358483024735951858997 2266627357783568995486781)
                      ·
                        rfl

theorem cell23_4414241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 2, 1, 1, 5].length) (baseStart_4414241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414241 prefixEnd_4414241 := by exact prefixLift 4414241
  have htrace : WordTrace (prefixWord ++ tailWord_4414241) baseStart_4414241 baseEnd_4414241 := by
    simpa [prefixWord, tailWord_4414241, baseEnd_4414241] using wordTrace_append hprefix tailTrace_4414241
  have hstable : (prefixWord ++ tailWord_4414241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414241).length < 2 ^ (prefixWord ++ tailWord_4414241).sum := by decide
  have hdescent : baseEnd_4414241 < baseStart_4414241 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414261 : List Nat := [1, 3, 3, 1, 3, 2, 1, 9]
def baseStart_4414261 : Nat := 118140960795 + 4414261 * 2 ^ 59
def prefixEnd_4414261 : Nat := 4983230072969 + 3 ^ 40 * 4414261 * 2
def baseEnd_4414261 : Nat := 83949541755431811749507

theorem tailTrace_4414261 : CollatzResearch.WordTrace tailWord_4414261 prefixEnd_4414261 83949541755431811749507 := by
  unfold tailWord_4414261
  simp only [CollatzResearch.WordTrace]
  refine ⟨161001325460893767603202637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107334216973929178402135091 161001325460893767603202637)
  ·
    refine ⟨60375497047835162851200989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161001325460893767603202637 60375497047835162851200989)
    ·
      refine ⟨22640811392938186069200371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60375497047835162851200989 22640811392938186069200371)
      ·
        refine ⟨33961217089407279103800557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22640811392938186069200371 33961217089407279103800557)
        ·
          refine ⟨12735456408527729663925209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33961217089407279103800557 12735456408527729663925209)
          ·
            refine ⟨9551592306395797247943907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12735456408527729663925209 9551592306395797247943907)
            ·
              refine ⟨14327388459593695871915861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9551592306395797247943907 14327388459593695871915861)
              ·
                refine ⟨83949541755431811749507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 14327388459593695871915861 83949541755431811749507)
                ·
                  rfl

theorem cell23_4414261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 9].length) (baseStart_4414261 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414261 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414261 prefixEnd_4414261 := by exact prefixLift 4414261
  have htrace : WordTrace (prefixWord ++ tailWord_4414261) baseStart_4414261 baseEnd_4414261 := by
    simpa [prefixWord, tailWord_4414261, baseEnd_4414261] using wordTrace_append hprefix tailTrace_4414261
  have hstable : (prefixWord ++ tailWord_4414261).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414261).length < 2 ^ (prefixWord ++ tailWord_4414261).sum := by decide
  have hdescent : baseEnd_4414261 < baseStart_4414261 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414288 : List Nat := [2, 1, 1, 1, 1, 4, 4, 1, 4, 1, 3]
def baseStart_4414288 : Nat := 118140960795 + 4414288 * 2 ^ 59
def prefixEnd_4414288 : Nat := 4983230072969 + 3 ^ 40 * 4414288 * 2
def baseEnd_4414288 : Nat := 2266651491374330311599065

theorem tailTrace_4414288 : CollatzResearch.WordTrace tailWord_4414288 prefixEnd_4414288 2266651491374330311599065 := by
  unfold tailWord_4414288
  simp only [CollatzResearch.WordTrace]
  refine ⟨80501155115897975607217759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107334873487863967476290345 80501155115897975607217759)
  ·
    refine ⟨120751732673846963410826639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80501155115897975607217759 120751732673846963410826639)
    ·
      refine ⟨181127599010770445116239959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120751732673846963410826639 181127599010770445116239959)
      ·
        refine ⟨271691398516155667674359939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181127599010770445116239959 271691398516155667674359939)
        ·
          refine ⟨407537097774233501511539909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271691398516155667674359939 407537097774233501511539909)
          ·
            refine ⟨76413205832668781533413733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 407537097774233501511539909 76413205832668781533413733)
            ·
              refine ⟨14327476093625396537515075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76413205832668781533413733 14327476093625396537515075)
              ·
                refine ⟨21491214140438094806272613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14327476093625396537515075 21491214140438094806272613)
                ·
                  refine ⟨4029602651332142776176115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21491214140438094806272613 4029602651332142776176115)
                  ·
                    refine ⟨6044403976998214164264173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029602651332142776176115 6044403976998214164264173)
                    ·
                      refine ⟨2266651491374330311599065, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6044403976998214164264173 2266651491374330311599065)
                      ·
                        rfl

theorem cell23_4414288_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 1, 4, 1, 3].length) (baseStart_4414288 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414288 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414288 prefixEnd_4414288 := by exact prefixLift 4414288
  have htrace : WordTrace (prefixWord ++ tailWord_4414288) baseStart_4414288 baseEnd_4414288 := by
    simpa [prefixWord, tailWord_4414288, baseEnd_4414288] using wordTrace_append hprefix tailTrace_4414288
  have hstable : (prefixWord ++ tailWord_4414288).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414288).length < 2 ^ (prefixWord ++ tailWord_4414288).sum := by decide
  have hdescent : baseEnd_4414288 < baseStart_4414288 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414288) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414289 : List Nat := [1, 2, 2, 1, 7, 1, 1, 1, 3, 2, 2]
def baseStart_4414289 : Nat := 118140960795 + 4414289 * 2 ^ 59
def prefixEnd_4414289 : Nat := 4983230072969 + 3 ^ 40 * 4414289 * 2
def baseEnd_4414289 : Nat := 2266652004854984807686561

theorem tailTrace_4414289 : CollatzResearch.WordTrace tailWord_4414289 prefixEnd_4414289 2266652004854984807686561 := by
  unfold tailWord_4414289
  simp only [CollatzResearch.WordTrace]
  refine ⟨161002346704792328385221921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107334897803194885590147947 161002346704792328385221921)
  ·
    refine ⟨120751760028594246288916441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161002346704792328385221921 120751760028594246288916441)
    ·
      refine ⟨90563820021445684716687331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120751760028594246288916441 90563820021445684716687331)
      ·
        refine ⟨135845730032168527075030997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90563820021445684716687331 135845730032168527075030997)
        ·
          refine ⟨3183884297628949853321039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 135845730032168527075030997 3183884297628949853321039)
          ·
            refine ⟨4775826446443424779981559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183884297628949853321039 4775826446443424779981559)
            ·
              refine ⟨7163739669665137169972339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775826446443424779981559 7163739669665137169972339)
              ·
                refine ⟨10745609504497705754958509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7163739669665137169972339 10745609504497705754958509)
                ·
                  refine ⟨4029603564186639658109441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10745609504497705754958509 4029603564186639658109441)
                  ·
                    refine ⟨3022202673139979743582081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4029603564186639658109441 3022202673139979743582081)
                    ·
                      refine ⟨2266652004854984807686561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022202673139979743582081 2266652004854984807686561)
                      ·
                        rfl

theorem cell23_4414289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 7, 1, 1, 1, 3, 2, 2].length) (baseStart_4414289 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414289 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414289 prefixEnd_4414289 := by exact prefixLift 4414289
  have htrace : WordTrace (prefixWord ++ tailWord_4414289) baseStart_4414289 baseEnd_4414289 := by
    simpa [prefixWord, tailWord_4414289, baseEnd_4414289] using wordTrace_append hprefix tailTrace_4414289
  have hstable : (prefixWord ++ tailWord_4414289).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414289).length < 2 ^ (prefixWord ++ tailWord_4414289).sum := by decide
  have hdescent : baseEnd_4414289 < baseStart_4414289 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414315 : List Nat := [1, 1, 1, 1, 2, 2, 7, 2, 1, 3, 2]
def baseStart_4414315 : Nat := 118140960795 + 4414315 * 2 ^ 59
def prefixEnd_4414315 : Nat := 4983230072969 + 3 ^ 40 * 4414315 * 2
def baseEnd_4414315 : Nat := 2266665355352001705961441

theorem tailTrace_4414315 : CollatzResearch.WordTrace tailWord_4414315 prefixEnd_4414315 2266665355352001705961441 := by
  unfold tailWord_4414315
  simp only [CollatzResearch.WordTrace]
  refine ⟨161003295002698134825668399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107335530001798756550445599 161003295002698134825668399)
  ·
    refine ⟨241504942504047202238502599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161003295002698134825668399 241504942504047202238502599)
    ·
      refine ⟨362257413756070803357753899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241504942504047202238502599 362257413756070803357753899)
      ·
        refine ⟨543386120634106205036630849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362257413756070803357753899 543386120634106205036630849)
        ·
          refine ⟨407539590475579653777473137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 543386120634106205036630849 407539590475579653777473137)
          ·
            refine ⟨305654692856684740333104853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 407539590475579653777473137 305654692856684740333104853)
            ·
              refine ⟨7163781863828548601557145, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 305654692856684740333104853 7163781863828548601557145)
              ·
                refine ⟨5372836397871411451167859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163781863828548601557145 5372836397871411451167859)
                ·
                  refine ⟨8059254596807117176751789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5372836397871411451167859 8059254596807117176751789)
                  ·
                    refine ⟨3022220473802668941281921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8059254596807117176751789 3022220473802668941281921)
                    ·
                      refine ⟨2266665355352001705961441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022220473802668941281921 2266665355352001705961441)
                      ·
                        rfl

theorem cell23_4414315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 7, 2, 1, 3, 2].length) (baseStart_4414315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414315 prefixEnd_4414315 := by exact prefixLift 4414315
  have htrace : WordTrace (prefixWord ++ tailWord_4414315) baseStart_4414315 baseEnd_4414315 := by
    simpa [prefixWord, tailWord_4414315, baseEnd_4414315] using wordTrace_append hprefix tailTrace_4414315
  have hstable : (prefixWord ++ tailWord_4414315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414315).length < 2 ^ (prefixWord ++ tailWord_4414315).sum := by decide
  have hdescent : baseEnd_4414315 < baseStart_4414315 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414331 : List Nat := [1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5]
def baseStart_4414331 : Nat := 118140960795 + 4414331 * 2 ^ 59
def prefixEnd_4414331 : Nat := 4983230072969 + 3 ^ 40 * 4414331 * 2
def baseEnd_4414331 : Nat := 2266673571042473643361367

theorem tailTrace_4414331 : CollatzResearch.WordTrace tailWord_4414331 prefixEnd_4414331 2266673571042473643361367 := by
  unfold tailWord_4414331
  simp only [CollatzResearch.WordTrace]
  refine ⟨161003878570640169558250847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107335919047093446372167231 161003878570640169558250847)
  ·
    refine ⟨241505817855960254337376271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161003878570640169558250847 241505817855960254337376271)
    ·
      refine ⟨362258726783940381506064407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241505817855960254337376271 362258726783940381506064407)
      ·
        refine ⟨543388090175910572259096611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362258726783940381506064407 543388090175910572259096611)
        ·
          refine ⟨815082135263865858388644917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 543388090175910572259096611 815082135263865858388644917)
          ·
            refine ⟨76413950180987424223935461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 815082135263865858388644917 76413950180987424223935461)
            ·
              refine ⟨14327615658935142041987899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76413950180987424223935461 14327615658935142041987899)
              ·
                refine ⟨21491423488402713062981849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14327615658935142041987899 21491423488402713062981849)
                ·
                  refine ⟨16118567616302034797236387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21491423488402713062981849 16118567616302034797236387)
                  ·
                    refine ⟨24177851424453052195854581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16118567616302034797236387 24177851424453052195854581)
                    ·
                      refine ⟨2266673571042473643361367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24177851424453052195854581 2266673571042473643361367)
                      ·
                        rfl

theorem cell23_4414331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 4, 1, 2, 1, 5].length) (baseStart_4414331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414331 prefixEnd_4414331 := by exact prefixLift 4414331
  have htrace : WordTrace (prefixWord ++ tailWord_4414331) baseStart_4414331 baseEnd_4414331 := by
    simpa [prefixWord, tailWord_4414331, baseEnd_4414331] using wordTrace_append hprefix tailTrace_4414331
  have hstable : (prefixWord ++ tailWord_4414331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414331).length < 2 ^ (prefixWord ++ tailWord_4414331).sum := by decide
  have hdescent : baseEnd_4414331 < baseStart_4414331 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414362 : List Nat := [3, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2]
def baseStart_4414362 : Nat := 118140960795 + 4414362 * 2 ^ 59
def prefixEnd_4414362 : Nat := 4983230072969 + 3 ^ 40 * 4414362 * 2
def baseEnd_4414362 : Nat := 2266689488942763022073725

theorem tailTrace_4414362 : CollatzResearch.WordTrace tailWord_4414362 prefixEnd_4414362 2266689488942763022073725 := by
  unfold tailWord_4414362
  simp only [CollatzResearch.WordTrace]
  refine ⟨40251252308381965463157335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107336672822351907901752893 40251252308381965463157335)
  ·
    refine ⟨60376878462572948194736003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40251252308381965463157335 60376878462572948194736003)
    ·
      refine ⟨90565317693859422292104005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60376878462572948194736003 90565317693859422292104005)
      ·
        refine ⟨16980997067598641679769501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90565317693859422292104005 16980997067598641679769501)
        ·
          refine ⟨6367873900349490629913563, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16980997067598641679769501 6367873900349490629913563)
          ·
            refine ⟨9551810850524235944870345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6367873900349490629913563 9551810850524235944870345)
            ·
              refine ⟨7163858137893176958652759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9551810850524235944870345 7163858137893176958652759)
              ·
                refine ⟨10745787206839765437979139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7163858137893176958652759 10745787206839765437979139)
                ·
                  refine ⟨16118680810259648156968709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10745787206839765437979139 16118680810259648156968709)
                  ·
                    refine ⟨3022252651923684029431633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16118680810259648156968709 3022252651923684029431633)
                    ·
                      refine ⟨2266689488942763022073725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022252651923684029431633 2266689488942763022073725)
                      ·
                        rfl

theorem cell23_4414362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 3, 1, 2, 1, 1, 4, 2].length) (baseStart_4414362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414362 prefixEnd_4414362 := by exact prefixLift 4414362
  have htrace : WordTrace (prefixWord ++ tailWord_4414362) baseStart_4414362 baseEnd_4414362 := by
    simpa [prefixWord, tailWord_4414362, baseEnd_4414362] using wordTrace_append hprefix tailTrace_4414362
  have hstable : (prefixWord ++ tailWord_4414362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414362).length < 2 ^ (prefixWord ++ tailWord_4414362).sum := by decide
  have hdescent : baseEnd_4414362 < baseStart_4414362 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414390 : List Nat := [5, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3]
def baseStart_4414390 : Nat := 118140960795 + 4414390 * 2 ^ 59
def prefixEnd_4414390 : Nat := 4983230072969 + 3 ^ 40 * 4414390 * 2
def baseEnd_4414390 : Nat := 2266703866401088912523597

theorem tailTrace_4414390 : CollatzResearch.WordTrace tailWord_4414390 prefixEnd_4414390 2266703866401088912523597 := by
  unfold tailWord_4414390
  simp only [CollatzResearch.WordTrace]
  refine ⟨10062876904839151414665539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107337353651617615089765749 10062876904839151414665539)
  ·
    refine ⟨15094315357258727121998309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 10062876904839151414665539 15094315357258727121998309)
    ·
      refine ⟨2830184129486011335374683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 15094315357258727121998309 2830184129486011335374683)
      ·
        refine ⟨4245276194229017003062025, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830184129486011335374683 4245276194229017003062025)
        ·
          refine ⟨3183957145671762752296519, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4245276194229017003062025 3183957145671762752296519)
          ·
            refine ⟨4775935718507644128444779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3183957145671762752296519 4775935718507644128444779)
            ·
              refine ⟨7163903577761466192667169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775935718507644128444779 7163903577761466192667169)
              ·
                refine ⟨5372927683321099644500377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7163903577761466192667169 5372927683321099644500377)
                ·
                  refine ⟨4029695762490824733375283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5372927683321099644500377 4029695762490824733375283)
                  ·
                    refine ⟨6044543643736237100062925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029695762490824733375283 6044543643736237100062925)
                    ·
                      refine ⟨2266703866401088912523597, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6044543643736237100062925 2266703866401088912523597)
                      ·
                        rfl

theorem cell23_4414390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 1, 2, 2, 1, 3].length) (baseStart_4414390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414390 prefixEnd_4414390 := by exact prefixLift 4414390
  have htrace : WordTrace (prefixWord ++ tailWord_4414390) baseStart_4414390 baseEnd_4414390 := by
    simpa [prefixWord, tailWord_4414390, baseEnd_4414390] using wordTrace_append hprefix tailTrace_4414390
  have hstable : (prefixWord ++ tailWord_4414390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414390).length < 2 ^ (prefixWord ++ tailWord_4414390).sum := by decide
  have hdescent : baseEnd_4414390 < baseStart_4414390 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414391 : List Nat := [1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 5]
def baseStart_4414391 : Nat := 118140960795 + 4414391 * 2 ^ 59
def prefixEnd_4414391 : Nat := 4983230072969 + 3 ^ 40 * 4414391 * 2
def baseEnd_4414391 : Nat := 2266704379881743408611091

theorem tailTrace_4414391 : CollatzResearch.WordTrace tailWord_4414391 prefixEnd_4414391 2266704379881743408611091 := by
  unfold tailWord_4414391
  simp only [CollatzResearch.WordTrace]
  refine ⟨161006066950422799805435027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107337377966948533203623351 161006066950422799805435027)
  ·
    refine ⟨241509100425634199708152541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161006066950422799805435027 241509100425634199708152541)
    ·
      refine ⟨90565912659612824890557203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241509100425634199708152541 90565912659612824890557203)
      ·
        refine ⟨135848868989419237335835805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90565912659612824890557203 135848868989419237335835805)
        ·
          refine ⟨50943325871032214000938427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135848868989419237335835805 50943325871032214000938427)
          ·
            refine ⟨76414988806548321001407641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50943325871032214000938427 76414988806548321001407641)
            ·
              refine ⟨57311241604911240751055731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76414988806548321001407641 57311241604911240751055731)
              ·
                refine ⟨85966862407366861126583597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57311241604911240751055731 85966862407366861126583597)
                ·
                  refine ⟨32237573402762572922468849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85966862407366861126583597 32237573402762572922468849)
                  ·
                    refine ⟨24178180052071929691851637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 32237573402762572922468849 24178180052071929691851637)
                    ·
                      refine ⟨2266704379881743408611091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24178180052071929691851637 2266704379881743408611091)
                      ·
                        rfl

theorem cell23_4414391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 1, 3, 2, 5].length) (baseStart_4414391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414391 prefixEnd_4414391 := by exact prefixLift 4414391
  have htrace : WordTrace (prefixWord ++ tailWord_4414391) baseStart_4414391 baseEnd_4414391 := by
    simpa [prefixWord, tailWord_4414391, baseEnd_4414391] using wordTrace_append hprefix tailTrace_4414391
  have hstable : (prefixWord ++ tailWord_4414391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414391).length < 2 ^ (prefixWord ++ tailWord_4414391).sum := by decide
  have hdescent : baseEnd_4414391 < baseStart_4414391 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414398 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 4, 5]
def baseStart_4414398 : Nat := 118140960795 + 4414398 * 2 ^ 59
def prefixEnd_4414398 : Nat := 4983230072969 + 3 ^ 40 * 4414398 * 2
def baseEnd_4414398 : Nat := 755569324748774960407853

theorem tailTrace_4414398 : CollatzResearch.WordTrace tailWord_4414398 prefixEnd_4414398 755569324748774960407853 := by
  unfold tailWord_4414398
  simp only [CollatzResearch.WordTrace]
  refine ⟨20125790282674680000117481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107337548174264960000626565 20125790282674680000117481)
  ·
    refine ⟨15094342712006010000088111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20125790282674680000117481 15094342712006010000088111)
    ·
      refine ⟨22641514068009015000132167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15094342712006010000088111 22641514068009015000132167)
      ·
        refine ⟨33962271102013522500198251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22641514068009015000132167 33962271102013522500198251)
        ·
          refine ⟨50943406653020283750297377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33962271102013522500198251 50943406653020283750297377)
          ·
            refine ⟨38207554989765212812723033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50943406653020283750297377 38207554989765212812723033)
            ·
              refine ⟨28655666242323909609542275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38207554989765212812723033 28655666242323909609542275)
              ·
                refine ⟨42983499363485864414313413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28655666242323909609542275 42983499363485864414313413)
                ·
                  refine ⟨8059406130653599577683765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42983499363485864414313413 8059406130653599577683765)
                  ·
                    refine ⟨755569324748774960407853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8059406130653599577683765 755569324748774960407853)
                    ·
                      rfl

theorem cell23_4414398_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 4, 5].length) (baseStart_4414398 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414398 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414398 prefixEnd_4414398 := by exact prefixLift 4414398
  have htrace : WordTrace (prefixWord ++ tailWord_4414398) baseStart_4414398 baseEnd_4414398 := by
    simpa [prefixWord, tailWord_4414398, baseEnd_4414398] using wordTrace_append hprefix tailTrace_4414398
  have hstable : (prefixWord ++ tailWord_4414398).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414398).length < 2 ^ (prefixWord ++ tailWord_4414398).sum := by decide
  have hdescent : baseEnd_4414398 < baseStart_4414398 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414398) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414413 : List Nat := [1, 6, 3, 1, 1, 2, 1, 1, 1, 4, 2]
def baseStart_4414413 : Nat := 118140960795 + 4414413 * 2 ^ 59
def prefixEnd_4414413 : Nat := 4983230072969 + 3 ^ 40 * 4414413 * 2
def baseEnd_4414413 : Nat := 2266715676456142322535991

theorem tailTrace_4414413 : CollatzResearch.WordTrace tailWord_4414413 prefixEnd_4414413 2266715676456142322535991 := by
  unfold tailWord_4414413
  simp only [CollatzResearch.WordTrace]
  refine ⟨161006869356343097562735893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107337912904228731708490595 161006869356343097562735893)
  ·
    refine ⟨7547197001078582698253245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 161006869356343097562735893 7547197001078582698253245)
    ·
      refine ⟨2830198875404468511844967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 7547197001078582698253245 2830198875404468511844967)
      ·
        refine ⟨4245298313106702767767451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830198875404468511844967 4245298313106702767767451)
        ·
          refine ⟨6367947469660054151651177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245298313106702767767451 6367947469660054151651177)
          ·
            refine ⟨4775960602245040613738383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6367947469660054151651177 4775960602245040613738383)
            ·
              refine ⟨7163940903367560920607575, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4775960602245040613738383 7163940903367560920607575)
              ·
                refine ⟨10745911355051341380911363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7163940903367560920607575 10745911355051341380911363)
                ·
                  refine ⟨16118867032577012071367045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10745911355051341380911363 16118867032577012071367045)
                  ·
                    refine ⟨3022287568608189763381321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16118867032577012071367045 3022287568608189763381321)
                    ·
                      refine ⟨2266715676456142322535991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022287568608189763381321 2266715676456142322535991)
                      ·
                        rfl

theorem cell23_4414413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 3, 1, 1, 2, 1, 1, 1, 4, 2].length) (baseStart_4414413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414413 prefixEnd_4414413 := by exact prefixLift 4414413
  have htrace : WordTrace (prefixWord ++ tailWord_4414413) baseStart_4414413 baseEnd_4414413 := by
    simpa [prefixWord, tailWord_4414413, baseEnd_4414413] using wordTrace_append hprefix tailTrace_4414413
  have hstable : (prefixWord ++ tailWord_4414413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414413).length < 2 ^ (prefixWord ++ tailWord_4414413).sum := by decide
  have hdescent : baseEnd_4414413 < baseStart_4414413 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414475 : List Nat := [1, 1, 1, 1, 6, 2, 4, 1, 6]
def baseStart_4414475 : Nat := 118140960795 + 4414475 * 2 ^ 59
def prefixEnd_4414475 : Nat := 4983230072969 + 3 ^ 40 * 4414475 * 2
def baseEnd_4414475 : Nat := 251860834695191231106745

theorem tailTrace_4414475 : CollatzResearch.WordTrace tailWord_4414475 prefixEnd_4414475 251860834695191231106745 := by
  unfold tailWord_4414475
  simp only [CollatzResearch.WordTrace]
  refine ⟨161009130682118482151492879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107339420454745654767661919 161009130682118482151492879)
  ·
    refine ⟨241513696023177723227239319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161009130682118482151492879 241513696023177723227239319)
    ·
      refine ⟨362270544034766584840858979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241513696023177723227239319 362270544034766584840858979)
      ·
        refine ⟨543405816052149877261288469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362270544034766584840858979 543405816052149877261288469)
        ·
          refine ⟨25472147627444525496622897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 543405816052149877261288469 25472147627444525496622897)
          ·
            refine ⟨19104110720583394122467173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25472147627444525496622897 19104110720583394122467173)
            ·
              refine ⟨3582020760109386397962595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19104110720583394122467173 3582020760109386397962595)
              ·
                refine ⟨5373031140164079596943893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582020760109386397962595 5373031140164079596943893)
                ·
                  refine ⟨251860834695191231106745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5373031140164079596943893 251860834695191231106745)
                  ·
                    rfl

theorem cell23_4414475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 4, 1, 6].length) (baseStart_4414475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414475 prefixEnd_4414475 := by exact prefixLift 4414475
  have htrace : WordTrace (prefixWord ++ tailWord_4414475) baseStart_4414475 baseEnd_4414475 := by
    simpa [prefixWord, tailWord_4414475, baseEnd_4414475] using wordTrace_append hprefix tailTrace_4414475
  have hstable : (prefixWord ++ tailWord_4414475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414475).length < 2 ^ (prefixWord ++ tailWord_4414475).sum := by decide
  have hdescent : baseEnd_4414475 < baseStart_4414475 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414525 : List Nat := [1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 4]
def baseStart_4414525 : Nat := 118140960795 + 4414525 * 2 ^ 59
def prefixEnd_4414525 : Nat := 4983230072969 + 3 ^ 40 * 4414525 * 2
def baseEnd_4414525 : Nat := 2266773186289445884335475

theorem tailTrace_4414525 : CollatzResearch.WordTrace tailWord_4414525 prefixEnd_4414525 2266773186289445884335475 := by
  unfold tailWord_4414525
  simp only [CollatzResearch.WordTrace]
  refine ⟨161010954331937340690813029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107340636221291560460542019 161010954331937340690813029)
  ·
    refine ⟨30189553937238251379527443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161010954331937340690813029 30189553937238251379527443)
    ·
      refine ⟨45284330905857377069291165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30189553937238251379527443 45284330905857377069291165)
      ·
        refine ⟨16981624089696516400984187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45284330905857377069291165 16981624089696516400984187)
        ·
          refine ⟨25472436134544774601476281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16981624089696516400984187 25472436134544774601476281)
          ·
            refine ⟨19104327100908580951107211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25472436134544774601476281 19104327100908580951107211)
            ·
              refine ⟨28656490651362871426660817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19104327100908580951107211 28656490651362871426660817)
              ·
                refine ⟨21492367988522153569995613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28656490651362871426660817 21492367988522153569995613)
                ·
                  refine ⟨8059637995695807588748355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21492367988522153569995613 8059637995695807588748355)
                  ·
                    refine ⟨12089456993543711383122533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8059637995695807588748355 12089456993543711383122533)
                    ·
                      refine ⟨2266773186289445884335475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12089456993543711383122533 2266773186289445884335475)
                      ·
                        rfl

theorem cell23_4414525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 2, 3, 1, 4].length) (baseStart_4414525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414525 prefixEnd_4414525 := by exact prefixLift 4414525
  have htrace : WordTrace (prefixWord ++ tailWord_4414525) baseStart_4414525 baseEnd_4414525 := by
    simpa [prefixWord, tailWord_4414525, baseEnd_4414525] using wordTrace_append hprefix tailTrace_4414525
  have hstable : (prefixWord ++ tailWord_4414525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414525).length < 2 ^ (prefixWord ++ tailWord_4414525).sum := by decide
  have hdescent : baseEnd_4414525 < baseStart_4414525 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414528 : List Nat := [2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5]
def baseStart_4414528 : Nat := 118140960795 + 4414528 * 2 ^ 59
def prefixEnd_4414528 : Nat := 4983230072969 + 3 ^ 40 * 4414528 * 2
def baseEnd_4414528 : Nat := 2266774726731409372597961

theorem tailTrace_4414528 : CollatzResearch.WordTrace tailWord_4414528 prefixEnd_4414528 2266774726731409372597961 := by
  unfold tailWord_4414528
  simp only [CollatzResearch.WordTrace]
  refine ⟨80505531875463236101586119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107340709167284314802114825 80505531875463236101586119)
  ·
    refine ⟨120758297813194854152379179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80505531875463236101586119 120758297813194854152379179)
    ·
      refine ⟨181137446719792281228568769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120758297813194854152379179 181137446719792281228568769)
      ·
        refine ⟨135853085039844210921426577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181137446719792281228568769 135853085039844210921426577)
        ·
          refine ⟨101889813779883158191069933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135853085039844210921426577 101889813779883158191069933)
          ·
            refine ⟨38208680167456184321651225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101889813779883158191069933 38208680167456184321651225)
            ·
              refine ⟨28656510125592138241238419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38208680167456184321651225 28656510125592138241238419)
              ·
                refine ⟨42984765188388207361857629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28656510125592138241238419 42984765188388207361857629)
                ·
                  refine ⟨16119286945645577760696611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 42984765188388207361857629 16119286945645577760696611)
                  ·
                    refine ⟨24178930418468366641044917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16119286945645577760696611 24178930418468366641044917)
                    ·
                      refine ⟨2266774726731409372597961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24178930418468366641044917 2266774726731409372597961)
                      ·
                        rfl

theorem cell23_4414528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 5].length) (baseStart_4414528 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414528 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414528 prefixEnd_4414528 := by exact prefixLift 4414528
  have htrace : WordTrace (prefixWord ++ tailWord_4414528) baseStart_4414528 baseEnd_4414528 := by
    simpa [prefixWord, tailWord_4414528, baseEnd_4414528] using wordTrace_append hprefix tailTrace_4414528
  have hstable : (prefixWord ++ tailWord_4414528).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414528).length < 2 ^ (prefixWord ++ tailWord_4414528).sum := by decide
  have hdescent : baseEnd_4414528 < baseStart_4414528 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414535 : List Nat := [1, 1, 4, 1, 3, 3, 2, 1, 1, 6]
def baseStart_4414535 : Nat := 118140960795 + 4414535 * 2 ^ 59
def prefixEnd_4414535 : Nat := 4983230072969 + 3 ^ 40 * 4414535 * 2
def baseEnd_4414535 : Nat := 755592773698663615070143

theorem tailTrace_4414535 : CollatzResearch.WordTrace tailWord_4414535 prefixEnd_4414535 755592773698663615070143 := by
  unfold tailWord_4414535
  simp only [CollatzResearch.WordTrace]
  refine ⟨161011319061901112398677059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107340879374600741599118039 161011319061901112398677059)
  ·
    refine ⟨241516978592851668598015589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161011319061901112398677059 241516978592851668598015589)
    ·
      refine ⟨45284433486159687862127923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241516978592851668598015589 45284433486159687862127923)
      ·
        refine ⟨67926650229239531793191885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45284433486159687862127923 67926650229239531793191885)
        ·
          refine ⟨25472493835964824422446957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67926650229239531793191885 25472493835964824422446957)
          ·
            refine ⟨9552185188486809158417609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25472493835964824422446957 9552185188486809158417609)
            ·
              refine ⟨7164138891365106868813207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9552185188486809158417609 7164138891365106868813207)
              ·
                refine ⟨10746208337047660303219811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7164138891365106868813207 10746208337047660303219811)
                ·
                  refine ⟨16119312505571490454829717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10746208337047660303219811 16119312505571490454829717)
                  ·
                    refine ⟨755592773698663615070143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16119312505571490454829717 755592773698663615070143)
                    ·
                      rfl

theorem cell23_4414535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 3, 2, 1, 1, 6].length) (baseStart_4414535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414535 prefixEnd_4414535 := by exact prefixLift 4414535
  have htrace : WordTrace (prefixWord ++ tailWord_4414535) baseStart_4414535 baseEnd_4414535 := by
    simpa [prefixWord, tailWord_4414535, baseEnd_4414535] using wordTrace_append hprefix tailTrace_4414535
  have hstable : (prefixWord ++ tailWord_4414535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414535).length < 2 ^ (prefixWord ++ tailWord_4414535).sum := by decide
  have hdescent : baseEnd_4414535 < baseStart_4414535 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414538 : List Nat := [3, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6]
def baseStart_4414538 : Nat := 118140960795 + 4414538 * 2 ^ 59
def prefixEnd_4414538 : Nat := 4983230072969 + 3 ^ 40 * 4414538 * 2
def baseEnd_4414538 : Nat := 2266779861537954333472915

theorem tailTrace_4414538 : CollatzResearch.WordTrace tailWord_4414538 prefixEnd_4414538 2266779861537954333472915 := by
  unfold tailWord_4414538
  simp only [CollatzResearch.WordTrace]
  refine ⟨40252857120222560977759067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107340952320593495940690845 40252857120222560977759067)
  ·
    refine ⟨60379285680333841466638601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40252857120222560977759067 60379285680333841466638601)
    ·
      refine ⟨45284464260250381099978951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60379285680333841466638601 45284464260250381099978951)
      ·
        refine ⟨67926696390375571649968427, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45284464260250381099978951 67926696390375571649968427)
        ·
          refine ⟨101890044585563357474952641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67926696390375571649968427 101890044585563357474952641)
          ·
            refine ⟨76417533439172518106214481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101890044585563357474952641 76417533439172518106214481)
            ·
              refine ⟨57313150079379388579660861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76417533439172518106214481 57313150079379388579660861)
              ·
                refine ⟨21492431279767270717372823, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57313150079379388579660861 21492431279767270717372823)
                ·
                  refine ⟨32238646919650906076059235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21492431279767270717372823 32238646919650906076059235)
                  ·
                    refine ⟨48357970379476359114088853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32238646919650906076059235 48357970379476359114088853)
                    ·
                      refine ⟨2266779861537954333472915, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48357970379476359114088853 2266779861537954333472915)
                      ·
                        rfl

theorem cell23_4414538_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 3, 1, 1, 6].length) (baseStart_4414538 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414538 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414538 prefixEnd_4414538 := by exact prefixLift 4414538
  have htrace : WordTrace (prefixWord ++ tailWord_4414538) baseStart_4414538 baseEnd_4414538 := by
    simpa [prefixWord, tailWord_4414538, baseEnd_4414538] using wordTrace_append hprefix tailTrace_4414538
  have hstable : (prefixWord ++ tailWord_4414538).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414538).length < 2 ^ (prefixWord ++ tailWord_4414538).sum := by decide
  have hdescent : baseEnd_4414538 < baseStart_4414538 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414538) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414545 : List Nat := [1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 3]
def baseStart_4414545 : Nat := 118140960795 + 4414545 * 2 ^ 59
def prefixEnd_4414545 : Nat := 4983230072969 + 3 ^ 40 * 4414545 * 2
def baseEnd_4414545 : Nat := 2266783455902535806085383

theorem tailTrace_4414545 : CollatzResearch.WordTrace tailWord_4414545 prefixEnd_4414545 2266783455902535806085383 := by
  unfold tailWord_4414545
  simp only [CollatzResearch.WordTrace]
  refine ⟨161011683791864884106541089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107341122527909922737694059 161011683791864884106541089)
  ·
    refine ⟨120758762843898663079905817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161011683791864884106541089 120758762843898663079905817)
    ·
      refine ⟨90569072132923997309929363, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120758762843898663079905817 90569072132923997309929363)
      ·
        refine ⟨135853608199385995964894045, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90569072132923997309929363 135853608199385995964894045)
        ·
          refine ⟨50945103074769748486835267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135853608199385995964894045 50945103074769748486835267)
          ·
            refine ⟨76417654612154622730252901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50945103074769748486835267 76417654612154622730252901)
            ·
              refine ⟨14328310239778991761922419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76417654612154622730252901 14328310239778991761922419)
              ·
                refine ⟨21492465359668487642883629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14328310239778991761922419 21492465359668487642883629)
                ·
                  refine ⟨8059674509875682866081361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21492465359668487642883629 8059674509875682866081361)
                  ·
                    refine ⟨6044755882406762149561021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8059674509875682866081361 6044755882406762149561021)
                    ·
                      refine ⟨2266783455902535806085383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6044755882406762149561021 2266783455902535806085383)
                      ·
                        rfl

theorem cell23_4414545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 1, 3, 2, 3].length) (baseStart_4414545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414545 prefixEnd_4414545 := by exact prefixLift 4414545
  have htrace : WordTrace (prefixWord ++ tailWord_4414545) baseStart_4414545 baseEnd_4414545 := by
    simpa [prefixWord, tailWord_4414545, baseEnd_4414545] using wordTrace_append hprefix tailTrace_4414545
  have hstable : (prefixWord ++ tailWord_4414545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414545).length < 2 ^ (prefixWord ++ tailWord_4414545).sum := by decide
  have hdescent : baseEnd_4414545 < baseStart_4414545 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414548 : List Nat := [2, 4, 1, 1, 1, 1, 2, 11]
def baseStart_4414548 : Nat := 118140960795 + 4414548 * 2 ^ 59
def prefixEnd_4414548 : Nat := 4983230072969 + 3 ^ 40 * 4414548 * 2
def baseEnd_4414548 : Nat := 83954999864611084975847

theorem tailTrace_4414548 : CollatzResearch.WordTrace tailWord_4414548 prefixEnd_4414548 83954999864611084975847 := by
  unfold tailWord_4414548
  simp only [CollatzResearch.WordTrace]
  refine ⟨80505896605427007809450149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107341195473902677079266865 80505896605427007809450149)
  ·
    refine ⟨15094855613517563964271903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80505896605427007809450149 15094855613517563964271903)
    ·
      refine ⟨22642283420276345946407855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15094855613517563964271903 22642283420276345946407855)
      ·
        refine ⟨33963425130414518919611783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22642283420276345946407855 33963425130414518919611783)
        ·
          refine ⟨50945137695621778379417675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33963425130414518919611783 50945137695621778379417675)
          ·
            refine ⟨76417706543432667569126513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50945137695621778379417675 76417706543432667569126513)
            ·
              refine ⟨57313279907574500676844885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76417706543432667569126513 57313279907574500676844885)
              ·
                refine ⟨83954999864611084975847, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 57313279907574500676844885 83954999864611084975847)
                ·
                  rfl

theorem cell23_4414548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 11].length) (baseStart_4414548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414548 prefixEnd_4414548 := by exact prefixLift 4414548
  have htrace : WordTrace (prefixWord ++ tailWord_4414548) baseStart_4414548 baseEnd_4414548 := by
    simpa [prefixWord, tailWord_4414548, baseEnd_4414548] using wordTrace_append hprefix tailTrace_4414548
  have hstable : (prefixWord ++ tailWord_4414548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414548).length < 2 ^ (prefixWord ++ tailWord_4414548).sum := by decide
  have hdescent : baseEnd_4414548 < baseStart_4414548 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414592 : List Nat := [2, 1, 1, 2, 1, 3, 2, 5, 2, 1, 3]
def baseStart_4414592 : Nat := 118140960795 + 4414592 * 2 ^ 59
def prefixEnd_4414592 : Nat := 4983230072969 + 3 ^ 40 * 4414592 * 2
def baseEnd_4414592 : Nat := 2266807589493297122197667

theorem tailTrace_4414592 : CollatzResearch.WordTrace tailWord_4414592 prefixEnd_4414592 2266807589493297122197667 := by
  unfold tailWord_4414592
  simp only [CollatzResearch.WordTrace]
  refine ⟨80506699011347305566751015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107342265348463074089001353 80506699011347305566751015)
  ·
    refine ⟨120760048517020958350126523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80506699011347305566751015 120760048517020958350126523)
    ·
      refine ⟨181140072775531437525189785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120760048517020958350126523 181140072775531437525189785)
      ·
        refine ⟨135855054581648578143892339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181140072775531437525189785 135855054581648578143892339)
        ·
          refine ⟨203782581872472867215838509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135855054581648578143892339 203782581872472867215838509)
          ·
            refine ⟨76418468202177325205939441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203782581872472867215838509 76418468202177325205939441)
            ·
              refine ⟨57313851151632993904454581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76418468202177325205939441 57313851151632993904454581)
              ·
                refine ⟨5373173545465593178542617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 57313851151632993904454581 5373173545465593178542617)
                ·
                  refine ⟨4029880159099194883906963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5373173545465593178542617 4029880159099194883906963)
                  ·
                    refine ⟨6044820238648792325860445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4029880159099194883906963 6044820238648792325860445)
                    ·
                      refine ⟨2266807589493297122197667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6044820238648792325860445 2266807589493297122197667)
                      ·
                        rfl

theorem cell23_4414592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 5, 2, 1, 3].length) (baseStart_4414592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414592 prefixEnd_4414592 := by exact prefixLift 4414592
  have htrace : WordTrace (prefixWord ++ tailWord_4414592) baseStart_4414592 baseEnd_4414592 := by
    simpa [prefixWord, tailWord_4414592, baseEnd_4414592] using wordTrace_append hprefix tailTrace_4414592
  have hstable : (prefixWord ++ tailWord_4414592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414592).length < 2 ^ (prefixWord ++ tailWord_4414592).sum := by decide
  have hdescent : baseEnd_4414592 < baseStart_4414592 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414608 : List Nat := [2, 1, 1, 1, 1, 1, 4, 2, 4, 6]
def baseStart_4414608 : Nat := 118140960795 + 4414608 * 2 ^ 59
def prefixEnd_4414608 : Nat := 4983230072969 + 3 ^ 40 * 4414608 * 2
def baseEnd_4414608 : Nat := 755605268394589686532531

theorem tailTrace_4414608 : CollatzResearch.WordTrace tailWord_4414608 prefixEnd_4414608 755605268394589686532531 := by
  unfold tailWord_4414608
  simp only [CollatzResearch.WordTrace]
  refine ⟨80506990795318322933042239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107342654393757763910722985 80506990795318322933042239)
  ·
    refine ⟨120760486192977484399563359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80506990795318322933042239 120760486192977484399563359)
    ·
      refine ⟨181140729289466226599345039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120760486192977484399563359 181140729289466226599345039)
      ·
        refine ⟨271711093934199339899017559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181140729289466226599345039 271711093934199339899017559)
        ·
          refine ⟨407566640901299009848526339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271711093934199339899017559 407566640901299009848526339)
          ·
            refine ⟨611349961351948514772789509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407566640901299009848526339 611349961351948514772789509)
            ·
              refine ⟨114628117753490346519898033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 611349961351948514772789509 114628117753490346519898033)
              ·
                refine ⟨85971088315117759889923525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114628117753490346519898033 85971088315117759889923525)
                ·
                  refine ⟨16119579059084579979360661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 85971088315117759889923525 16119579059084579979360661)
                  ·
                    refine ⟨755605268394589686532531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16119579059084579979360661 755605268394589686532531)
                    ·
                      rfl

theorem cell23_4414608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 2, 4, 6].length) (baseStart_4414608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414608 prefixEnd_4414608 := by exact prefixLift 4414608
  have htrace : WordTrace (prefixWord ++ tailWord_4414608) baseStart_4414608 baseEnd_4414608 := by
    simpa [prefixWord, tailWord_4414608, baseEnd_4414608] using wordTrace_append hprefix tailTrace_4414608
  have hstable : (prefixWord ++ tailWord_4414608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414608).length < 2 ^ (prefixWord ++ tailWord_4414608).sum := by decide
  have hdescent : baseEnd_4414608 < baseStart_4414608 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414689 : List Nat := [1, 2, 3, 1, 3, 2, 4, 2, 5]
def baseStart_4414689 : Nat := 118140960795 + 4414689 * 2 ^ 59
def prefixEnd_4414689 : Nat := 4983230072969 + 3 ^ 40 * 4414689 * 2
def baseEnd_4414689 : Nat := 251873044124087026964969

theorem tailTrace_4414689 : CollatzResearch.WordTrace tailWord_4414689 prefixEnd_4414689 251873044124087026964969 := by
  unfold tailWord_4414689
  simp only [CollatzResearch.WordTrace]
  refine ⟨161016935903343196699783121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107344623935562131133188747 161016935903343196699783121)
  ·
    refine ⟨120762701927507397524837341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161016935903343196699783121 120762701927507397524837341)
    ·
      refine ⟨45286013222815274071814003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120762701927507397524837341 45286013222815274071814003)
      ·
        refine ⟨67929019834222911107721005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45286013222815274071814003 67929019834222911107721005)
        ·
          refine ⟨25473382437833591665395377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67929019834222911107721005 25473382437833591665395377)
          ·
            refine ⟨19105036828375193749046533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25473382437833591665395377 19105036828375193749046533)
            ·
              refine ⟨3582194405320348827946225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19105036828375193749046533 3582194405320348827946225)
              ·
                refine ⟨2686645803990261620959669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582194405320348827946225 2686645803990261620959669)
                ·
                  refine ⟨251873044124087026964969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686645803990261620959669 251873044124087026964969)
                  ·
                    rfl

theorem cell23_4414689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 2, 4, 2, 5].length) (baseStart_4414689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414689 prefixEnd_4414689 := by exact prefixLift 4414689
  have htrace : WordTrace (prefixWord ++ tailWord_4414689) baseStart_4414689 baseEnd_4414689 := by
    simpa [prefixWord, tailWord_4414689, baseEnd_4414689] using wordTrace_append hprefix tailTrace_4414689
  have hstable : (prefixWord ++ tailWord_4414689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414689).length < 2 ^ (prefixWord ++ tailWord_4414689).sum := by decide
  have hdescent : baseEnd_4414689 < baseStart_4414689 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414692 : List Nat := [2, 3, 1, 1, 1, 2, 3, 1, 2, 5, 2]
def baseStart_4414692 : Nat := 118140960795 + 4414692 * 2 ^ 59
def prefixEnd_4414692 : Nat := 4983230072969 + 3 ^ 40 * 4414692 * 2
def baseEnd_4414692 : Nat := 2266858937558746730947207

theorem tailTrace_4414692 : CollatzResearch.WordTrace tailWord_4414692 prefixEnd_4414692 2266858937558746730947207 := by
  unfold tailWord_4414692
  simp only [CollatzResearch.WordTrace]
  refine ⟨80508522661166164106071165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107344696881554885474761553 80508522661166164106071165)
  ·
    refine ⟨30190695997937311539776687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80508522661166164106071165 30190695997937311539776687)
    ·
      refine ⟨45286043996905967309665031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30190695997937311539776687 45286043996905967309665031)
      ·
        refine ⟨67929065995358950964497547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45286043996905967309665031 67929065995358950964497547)
        ·
          refine ⟨101893598993038426446746321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67929065995358950964497547 101893598993038426446746321)
          ·
            refine ⟨76420199244778819835059741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101893598993038426446746321 76420199244778819835059741)
            ·
              refine ⟨28657574716792057438147403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76420199244778819835059741 28657574716792057438147403)
              ·
                refine ⟨42986362075188086157221105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28657574716792057438147403 42986362075188086157221105)
                ·
                  refine ⟨32239771556391064617915829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42986362075188086157221105 32239771556391064617915829)
                  ·
                    refine ⟨3022478583411662307929609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32239771556391064617915829 3022478583411662307929609)
                    ·
                      refine ⟨2266858937558746730947207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022478583411662307929609 2266858937558746730947207)
                      ·
                        rfl

theorem cell23_4414692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 2, 3, 1, 2, 5, 2].length) (baseStart_4414692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414692 prefixEnd_4414692 := by exact prefixLift 4414692
  have htrace : WordTrace (prefixWord ++ tailWord_4414692) baseStart_4414692 baseEnd_4414692 := by
    simpa [prefixWord, tailWord_4414692, baseEnd_4414692] using wordTrace_append hprefix tailTrace_4414692
  have hstable : (prefixWord ++ tailWord_4414692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414692).length < 2 ^ (prefixWord ++ tailWord_4414692).sum := by decide
  have hdescent : baseEnd_4414692 < baseStart_4414692 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414705 : List Nat := [1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 4]
def baseStart_4414705 : Nat := 118140960795 + 4414705 * 2 ^ 59
def prefixEnd_4414705 : Nat := 4983230072969 + 3 ^ 40 * 4414705 * 2
def baseEnd_4414705 : Nat := 2266865612807255180084647

theorem tailTrace_4414705 : CollatzResearch.WordTrace tailWord_4414705 prefixEnd_4414705 2266865612807255180084647 := by
  unfold tailWord_4414705
  simp only [CollatzResearch.WordTrace]
  refine ⟨161017519471285231432365569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107345012980856820954910379 161017519471285231432365569)
  ·
    refine ⟨120763139603463923574274177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161017519471285231432365569 120763139603463923574274177)
    ·
      refine ⟨90572354702597942680705633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120763139603463923574274177 90572354702597942680705633)
      ·
        refine ⟨67929266026948457010529225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90572354702597942680705633 67929266026948457010529225)
        ·
          refine ⟨50946949520211342757896919, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67929266026948457010529225 50946949520211342757896919)
          ·
            refine ⟨76420424280317014136845379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50946949520211342757896919 76420424280317014136845379)
            ·
              refine ⟨114630636420475521205268069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76420424280317014136845379 114630636420475521205268069)
              ·
                refine ⟨21493244328839160225987763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114630636420475521205268069 21493244328839160225987763)
                ·
                  refine ⟨32239866493258740338981645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21493244328839160225987763 32239866493258740338981645)
                  ·
                    refine ⟨12089949934972027627118117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32239866493258740338981645 12089949934972027627118117)
                    ·
                      refine ⟨2266865612807255180084647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12089949934972027627118117 2266865612807255180084647)
                      ·
                        rfl

theorem cell23_4414705_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_4414705 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414705 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414705 prefixEnd_4414705 := by exact prefixLift 4414705
  have htrace : WordTrace (prefixWord ++ tailWord_4414705) baseStart_4414705 baseEnd_4414705 := by
    simpa [prefixWord, tailWord_4414705, baseEnd_4414705] using wordTrace_append hprefix tailTrace_4414705
  have hstable : (prefixWord ++ tailWord_4414705).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414705).length < 2 ^ (prefixWord ++ tailWord_4414705).sum := by decide
  have hdescent : baseEnd_4414705 < baseStart_4414705 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414705) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414749 : List Nat := [1, 4, 2, 3, 1, 1, 1, 3, 3, 4]
def baseStart_4414749 : Nat := 118140960795 + 4414749 * 2 ^ 59
def prefixEnd_4414749 : Nat := 4983230072969 + 3 ^ 40 * 4414749 * 2
def baseEnd_4414749 : Nat := 755629401985351002644815

theorem tailTrace_4414749 : CollatzResearch.WordTrace tailWord_4414749 prefixEnd_4414749 755629401985351002644815 := by
  unfold tailWord_4414749
  simp only [CollatzResearch.WordTrace]
  refine ⟨161019124283125826946967301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107346082855417217964644867 161019124283125826946967301)
  ·
    refine ⟨30191085803086092552556369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161019124283125826946967301 30191085803086092552556369)
    ·
      refine ⟨22643314352314569414417277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30191085803086092552556369 22643314352314569414417277)
      ·
        refine ⟨8491242882117963530406479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22643314352314569414417277 8491242882117963530406479)
        ·
          refine ⟨12736864323176945295609719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8491242882117963530406479 12736864323176945295609719)
          ·
            refine ⟨19105296484765417943414579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12736864323176945295609719 19105296484765417943414579)
            ·
              refine ⟨28657944727148126915121869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19105296484765417943414579 28657944727148126915121869)
              ·
                refine ⟨10746729272680547593170701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28657944727148126915121869 10746729272680547593170701)
                ·
                  refine ⟨4030023477255205347439013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10746729272680547593170701 4030023477255205347439013)
                  ·
                    refine ⟨755629401985351002644815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030023477255205347439013 755629401985351002644815)
                    ·
                      rfl

theorem cell23_4414749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 1, 1, 1, 3, 3, 4].length) (baseStart_4414749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414749 prefixEnd_4414749 := by exact prefixLift 4414749
  have htrace : WordTrace (prefixWord ++ tailWord_4414749) baseStart_4414749 baseEnd_4414749 := by
    simpa [prefixWord, tailWord_4414749, baseEnd_4414749] using wordTrace_append hprefix tailTrace_4414749
  have hstable : (prefixWord ++ tailWord_4414749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414749).length < 2 ^ (prefixWord ++ tailWord_4414749).sum := by decide
  have hdescent : baseEnd_4414749 < baseStart_4414749 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414795 : List Nat := [1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4]
def baseStart_4414795 : Nat := 118140960795 + 4414795 * 2 ^ 59
def prefixEnd_4414795 : Nat := 4983230072969 + 3 ^ 40 * 4414795 * 2
def baseEnd_4414795 : Nat := 2266911826066159827959233

theorem tailTrace_4414795 : CollatzResearch.WordTrace tailWord_4414795 prefixEnd_4414795 2266911826066159827959233 := by
  unfold tailWord_4414795
  simp only [CollatzResearch.WordTrace]
  refine ⟨161020802040959176803141839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107347201360639451202094559 161020802040959176803141839)
  ·
    refine ⟨241531203061438765204712759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161020802040959176803141839 241531203061438765204712759)
    ·
      refine ⟨362296804592158147807069139, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241531203061438765204712759 362296804592158147807069139)
      ·
        refine ⟨543445206888237221710603709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362296804592158147807069139 543445206888237221710603709)
        ·
          refine ⟨203791952583088958141476391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543445206888237221710603709 203791952583088958141476391)
          ·
            refine ⟨305687928874633437212214587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203791952583088958141476391 305687928874633437212214587)
            ·
              refine ⟨458531893311950155818321881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 305687928874633437212214587 458531893311950155818321881)
              ·
                refine ⟨343898919983962616863741411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458531893311950155818321881 343898919983962616863741411)
                ·
                  refine ⟨515848379975943925295612117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 343898919983962616863741411 515848379975943925295612117)
                  ·
                    refine ⟨12090196405686185749115909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 515848379975943925295612117 12090196405686185749115909)
                    ·
                      refine ⟨2266911826066159827959233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12090196405686185749115909 2266911826066159827959233)
                      ·
                        rfl

theorem cell23_4414795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 2, 1, 7, 4].length) (baseStart_4414795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414795 prefixEnd_4414795 := by exact prefixLift 4414795
  have htrace : WordTrace (prefixWord ++ tailWord_4414795) baseStart_4414795 baseEnd_4414795 := by
    simpa [prefixWord, tailWord_4414795, baseEnd_4414795] using wordTrace_append hprefix tailTrace_4414795
  have hstable : (prefixWord ++ tailWord_4414795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414795).length < 2 ^ (prefixWord ++ tailWord_4414795).sum := by decide
  have hdescent : baseEnd_4414795 < baseStart_4414795 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414813 : List Nat := [1, 4, 5, 1, 1, 1, 1, 3, 6]
def baseStart_4414813 : Nat := 118140960795 + 4414813 * 2 ^ 59
def prefixEnd_4414813 : Nat := 4983230072969 + 3 ^ 40 * 4414813 * 2
def baseEnd_4414813 : Nat := 251880118746437861948239

theorem tailTrace_4414813 : CollatzResearch.WordTrace tailWord_4414813 prefixEnd_4414813 251880118746437861948239 := by
  unfold tailWord_4414813
  simp only [CollatzResearch.WordTrace]
  refine ⟨161021458554893965877297093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107347639036595977251531395 161021458554893965877297093)
  ·
    refine ⟨30191523479042618601993205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161021458554893965877297093 30191523479042618601993205)
    ·
      refine ⟨2830455326160245493936863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 30191523479042618601993205 2830455326160245493936863)
      ·
        refine ⟨4245682989240368240905295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830455326160245493936863 4245682989240368240905295)
        ·
          refine ⟨6368524483860552361357943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4245682989240368240905295 6368524483860552361357943)
          ·
            refine ⟨9552786725790828542036915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6368524483860552361357943 9552786725790828542036915)
            ·
              refine ⟨14329180088686242813055373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9552786725790828542036915 14329180088686242813055373)
              ·
                refine ⟨5373442533257341054895765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14329180088686242813055373 5373442533257341054895765)
                ·
                  refine ⟨251880118746437861948239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5373442533257341054895765 251880118746437861948239)
                  ·
                    rfl

theorem cell23_4414813_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 1, 1, 3, 6].length) (baseStart_4414813 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414813 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414813 prefixEnd_4414813 := by exact prefixLift 4414813
  have htrace : WordTrace (prefixWord ++ tailWord_4414813) baseStart_4414813 baseEnd_4414813 := by
    simpa [prefixWord, tailWord_4414813, baseEnd_4414813] using wordTrace_append hprefix tailTrace_4414813
  have hstable : (prefixWord ++ tailWord_4414813).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414813).length < 2 ^ (prefixWord ++ tailWord_4414813).sum := by decide
  have hdescent : baseEnd_4414813 < baseStart_4414813 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414813) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414829 : List Nat := [1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 4]
def baseStart_4414829 : Nat := 118140960795 + 4414829 * 2 ^ 59
def prefixEnd_4414829 : Nat := 4983230072969 + 3 ^ 40 * 4414829 * 2
def baseEnd_4414829 : Nat := 2266929284408412694934077

theorem tailTrace_4414829 : CollatzResearch.WordTrace tailWord_4414829 prefixEnd_4414829 2266929284408412694934077 := by
  unfold tailWord_4414829
  simp only [CollatzResearch.WordTrace]
  refine ⟨161022042122836000609879541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107348028081890667073253027 161022042122836000609879541)
  ·
    refine ⟨15095816449015875057176207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161022042122836000609879541 15095816449015875057176207)
    ·
      refine ⟨22643724673523812585764311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15095816449015875057176207 22643724673523812585764311)
      ·
        refine ⟨33965587010285718878646467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22643724673523812585764311 33965587010285718878646467)
        ·
          refine ⟨50948380515428578317969701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33965587010285718878646467 50948380515428578317969701)
          ·
            refine ⟨9552821346642858434619319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50948380515428578317969701 9552821346642858434619319)
            ·
              refine ⟨14329232019964287651928979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9552821346642858434619319 14329232019964287651928979)
              ·
                refine ⟨21493848029946431477893469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14329232019964287651928979 21493848029946431477893469)
                ·
                  refine ⟨8060193011229911804210051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21493848029946431477893469 8060193011229911804210051)
                  ·
                    refine ⟨12090289516844867706315077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8060193011229911804210051 12090289516844867706315077)
                    ·
                      refine ⟨2266929284408412694934077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12090289516844867706315077 2266929284408412694934077)
                      ·
                        rfl

theorem cell23_4414829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 1, 3, 1, 4].length) (baseStart_4414829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414829 prefixEnd_4414829 := by exact prefixLift 4414829
  have htrace : WordTrace (prefixWord ++ tailWord_4414829) baseStart_4414829 baseEnd_4414829 := by
    simpa [prefixWord, tailWord_4414829, baseEnd_4414829] using wordTrace_append hprefix tailTrace_4414829
  have hstable : (prefixWord ++ tailWord_4414829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414829).length < 2 ^ (prefixWord ++ tailWord_4414829).sum := by decide
  have hdescent : baseEnd_4414829 < baseStart_4414829 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414842 : List Nat := [3, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4]
def baseStart_4414842 : Nat := 118140960795 + 4414842 * 2 ^ 59
def prefixEnd_4414842 : Nat := 4983230072969 + 3 ^ 40 * 4414842 * 2
def baseEnd_4414842 : Nat := 2266935959656921144071517

theorem tailTrace_4414842 : CollatzResearch.WordTrace tailWord_4414842 prefixEnd_4414842 2266935959656921144071517 := by
  unfold tailWord_4414842
  simp only [CollatzResearch.WordTrace]
  refine ⟨40255629067947225957525695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107348344181192602553401853 40255629067947225957525695)
  ·
    refine ⟨60383443601920838936288543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40255629067947225957525695 60383443601920838936288543)
    ·
      refine ⟨90575165402881258404432815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60383443601920838936288543 90575165402881258404432815)
      ·
        refine ⟨135862748104321887606649223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90575165402881258404432815 135862748104321887606649223)
        ·
          refine ⟨203794122156482831409973835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135862748104321887606649223 203794122156482831409973835)
          ·
            refine ⟨305691183234724247114960753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203794122156482831409973835 305691183234724247114960753)
            ·
              refine ⟨229268387426043185336220565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305691183234724247114960753 229268387426043185336220565)
              ·
                refine ⟨10746955660595774312635339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229268387426043185336220565 10746955660595774312635339)
                ·
                  refine ⟨16120433490893661468953009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10746955660595774312635339 16120433490893661468953009)
                  ·
                    refine ⟨12090325118170246101714757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16120433490893661468953009 12090325118170246101714757)
                    ·
                      refine ⟨2266935959656921144071517, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12090325118170246101714757 2266935959656921144071517)
                      ·
                        rfl

theorem cell23_4414842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 2, 6, 1, 2, 4].length) (baseStart_4414842 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414842 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414842 prefixEnd_4414842 := by exact prefixLift 4414842
  have htrace : WordTrace (prefixWord ++ tailWord_4414842) baseStart_4414842 baseEnd_4414842 := by
    simpa [prefixWord, tailWord_4414842, baseEnd_4414842] using wordTrace_append hprefix tailTrace_4414842
  have hstable : (prefixWord ++ tailWord_4414842).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414842).length < 2 ^ (prefixWord ++ tailWord_4414842).sum := by decide
  have hdescent : baseEnd_4414842 < baseStart_4414842 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414856 : List Nat := [2, 1, 3, 3, 1, 3, 2, 2, 2, 4]
def baseStart_4414856 : Nat := 118140960795 + 4414856 * 2 ^ 59
def prefixEnd_4414856 : Nat := 4983230072969 + 3 ^ 40 * 4414856 * 2
def baseEnd_4414856 : Nat := 755647716128694696432151

theorem tailTrace_4414856 : CollatzResearch.WordTrace tailWord_4414856 prefixEnd_4414856 755647716128694696432151 := by
  unfold tailWord_4414856
  simp only [CollatzResearch.WordTrace]
  refine ⟨80511513446869092110556211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107348684595825456147408281 80511513446869092110556211)
  ·
    refine ⟨120767270170303638165834317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80511513446869092110556211 120767270170303638165834317)
    ·
      refine ⟨45287726313863864312187869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120767270170303638165834317 45287726313863864312187869)
      ·
        refine ⟨16982897367698949117070451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45287726313863864312187869 16982897367698949117070451)
        ·
          refine ⟨25474346051548423675605677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16982897367698949117070451 25474346051548423675605677)
          ·
            refine ⟨9552879769330658878352129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25474346051548423675605677 9552879769330658878352129)
            ·
              refine ⟨7164659826997994158764097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9552879769330658878352129 7164659826997994158764097)
              ·
                refine ⟨5373494870248495619073073, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7164659826997994158764097 5373494870248495619073073)
                ·
                  refine ⟨4030121152686371714304805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5373494870248495619073073 4030121152686371714304805)
                  ·
                    refine ⟨755647716128694696432151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030121152686371714304805 755647716128694696432151)
                    ·
                      rfl

theorem cell23_4414856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 2, 2, 2, 4].length) (baseStart_4414856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414856 prefixEnd_4414856 := by exact prefixLift 4414856
  have htrace : WordTrace (prefixWord ++ tailWord_4414856) baseStart_4414856 baseEnd_4414856 := by
    simpa [prefixWord, tailWord_4414856, baseEnd_4414856] using wordTrace_append hprefix tailTrace_4414856
  have hstable : (prefixWord ++ tailWord_4414856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414856).length < 2 ^ (prefixWord ++ tailWord_4414856).sum := by decide
  have hdescent : baseEnd_4414856 < baseStart_4414856 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414857 : List Nat := [1, 2, 1, 1, 8, 1, 2, 2, 1, 1, 3]
def baseStart_4414857 : Nat := 118140960795 + 4414857 * 2 ^ 59
def prefixEnd_4414857 : Nat := 4983230072969 + 3 ^ 40 * 4414857 * 2
def baseEnd_4414857 : Nat := 2266943661866738585383949

theorem tailTrace_4414857 : CollatzResearch.WordTrace tailWord_4414857 prefixEnd_4414857 2266943661866738585383949 := by
  unfold tailWord_4414857
  simp only [CollatzResearch.WordTrace]
  refine ⟨161023063366734561391898825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107348708911156374261265883 161023063366734561391898825)
  ·
    refine ⟨120767297525050921043924119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161023063366734561391898825 120767297525050921043924119)
    ·
      refine ⟨181150946287576381565886179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120767297525050921043924119 181150946287576381565886179)
      ·
        refine ⟨271726419431364572348829269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181150946287576381565886179 271726419431364572348829269)
        ·
          refine ⟨3184293977711303582212843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 271726419431364572348829269 3184293977711303582212843)
          ·
            refine ⟨4776440966566955373319265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184293977711303582212843 4776440966566955373319265)
            ·
              refine ⟨3582330724925216529989449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4776440966566955373319265 3582330724925216529989449)
              ·
                refine ⟨2686748043693912397492087, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582330724925216529989449 2686748043693912397492087)
                ·
                  refine ⟨4030122065540868596238131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686748043693912397492087 4030122065540868596238131)
                  ·
                    refine ⟨6045183098311302894357197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4030122065540868596238131 6045183098311302894357197)
                    ·
                      refine ⟨2266943661866738585383949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6045183098311302894357197 2266943661866738585383949)
                      ·
                        rfl

theorem cell23_4414857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 2, 1, 1, 3].length) (baseStart_4414857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414857 prefixEnd_4414857 := by exact prefixLift 4414857
  have htrace : WordTrace (prefixWord ++ tailWord_4414857) baseStart_4414857 baseEnd_4414857 := by
    simpa [prefixWord, tailWord_4414857, baseEnd_4414857] using wordTrace_append hprefix tailTrace_4414857
  have hstable : (prefixWord ++ tailWord_4414857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414857).length < 2 ^ (prefixWord ++ tailWord_4414857).sum := by decide
  have hdescent : baseEnd_4414857 < baseStart_4414857 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414879 : List Nat := [1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 3]
def baseStart_4414879 : Nat := 118140960795 + 4414879 * 2 ^ 59
def prefixEnd_4414879 : Nat := 4983230072969 + 3 ^ 40 * 4414879 * 2
def baseEnd_4414879 : Nat := 2266954958441137499308847

theorem tailTrace_4414879 : CollatzResearch.WordTrace tailWord_4414879 prefixEnd_4414879 2266954958441137499308847 := by
  unfold tailWord_4414879
  simp only [CollatzResearch.WordTrace]
  refine ⟨161023865772654859149199691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107349243848436572766133127 161023865772654859149199691)
  ·
    refine ⟨241535798658982288723799537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161023865772654859149199691 241535798658982288723799537)
    ·
      refine ⟨181151848994236716542849653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241535798658982288723799537 181151848994236716542849653)
      ·
        refine ⟨16982985843209692175892155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181151848994236716542849653 16982985843209692175892155)
        ·
          refine ⟨25474478764814538263838233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16982985843209692175892155 25474478764814538263838233)
          ·
            refine ⟨19105859073610903697878675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25474478764814538263838233 19105859073610903697878675)
            ·
              refine ⟨28658788610416355546818013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19105859073610903697878675 28658788610416355546818013)
              ·
                refine ⟨10747045728906133330056755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28658788610416355546818013 10747045728906133330056755)
                ·
                  refine ⟨16120568593359199995085133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10747045728906133330056755 16120568593359199995085133)
                  ·
                    refine ⟨6045213222509699998156925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16120568593359199995085133 6045213222509699998156925)
                    ·
                      refine ⟨2266954958441137499308847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6045213222509699998156925 2266954958441137499308847)
                      ·
                        rfl

theorem cell23_4414879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 3, 1, 3, 3].length) (baseStart_4414879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414879 prefixEnd_4414879 := by exact prefixLift 4414879
  have htrace : WordTrace (prefixWord ++ tailWord_4414879) baseStart_4414879 baseEnd_4414879 := by
    simpa [prefixWord, tailWord_4414879, baseEnd_4414879] using wordTrace_append hprefix tailTrace_4414879
  have hstable : (prefixWord ++ tailWord_4414879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414879).length < 2 ^ (prefixWord ++ tailWord_4414879).sum := by decide
  have hdescent : baseEnd_4414879 < baseStart_4414879 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414912 : List Nat := [2, 1, 1, 2, 3, 1, 3, 2, 2, 6]
def baseStart_4414912 : Nat := 118140960795 + 4414912 * 2 ^ 59
def prefixEnd_4414912 : Nat := 4983230072969 + 3 ^ 40 * 4414912 * 2
def baseEnd_4414912 : Nat := 755657301100911956732065

theorem tailTrace_4414912 : CollatzResearch.WordTrace tailWord_4414912 prefixEnd_4414912 755657301100911956732065 := by
  unfold tailWord_4414912
  simp only [CollatzResearch.WordTrace]
  refine ⟨80512534690767652892575495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107350046254356870523433993 80512534690767652892575495)
  ·
    refine ⟨120768802036151479338863243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80512534690767652892575495 120768802036151479338863243)
    ·
      refine ⟨181153203054227219008294865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120768802036151479338863243 181153203054227219008294865)
      ·
        refine ⟨135864902290670414256221149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181153203054227219008294865 135864902290670414256221149)
        ·
          refine ⟨50949338359001405346082931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135864902290670414256221149 50949338359001405346082931)
          ·
            refine ⟨76424007538502108019124397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50949338359001405346082931 76424007538502108019124397)
            ·
              refine ⟨28659002826938290507171649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76424007538502108019124397 28659002826938290507171649)
              ·
                refine ⟨21494252120203717880378737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28659002826938290507171649 21494252120203717880378737)
                ·
                  refine ⟨16120689090152788410284053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21494252120203717880378737 16120689090152788410284053)
                  ·
                    refine ⟨755657301100911956732065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16120689090152788410284053 755657301100911956732065)
                    ·
                      rfl

theorem cell23_4414912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 3, 2, 2, 6].length) (baseStart_4414912 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414912 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414912 prefixEnd_4414912 := by exact prefixLift 4414912
  have htrace : WordTrace (prefixWord ++ tailWord_4414912) baseStart_4414912 baseEnd_4414912 := by
    simpa [prefixWord, tailWord_4414912, baseEnd_4414912] using wordTrace_append hprefix tailTrace_4414912
  have hstable : (prefixWord ++ tailWord_4414912).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414912).length < 2 ^ (prefixWord ++ tailWord_4414912).sum := by decide
  have hdescent : baseEnd_4414912 < baseStart_4414912 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414936 : List Nat := [2, 1, 2, 2, 2, 1, 5, 1, 1, 4, 2]
def baseStart_4414936 : Nat := 118140960795 + 4414936 * 2 ^ 59
def prefixEnd_4414936 : Nat := 4983230072969 + 3 ^ 40 * 4414936 * 2
def baseEnd_4414936 : Nat := 2266984226838443776296085

theorem tailTrace_4414936 : CollatzResearch.WordTrace tailWord_4414936 prefixEnd_4414936 2266984226838443776296085 := by
  unfold tailWord_4414936
  simp only [CollatzResearch.WordTrace]
  refine ⟨80512972366724178942012331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107350629822298905256016441 80512972366724178942012331)
  ·
    refine ⟨120769458550086268413018497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80512972366724178942012331 120769458550086268413018497)
    ·
      refine ⟨90577093912564701309763873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120769458550086268413018497 90577093912564701309763873)
      ·
        refine ⟨67932820434423525982322905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90577093912564701309763873 67932820434423525982322905)
        ·
          refine ⟨50949615325817644486742179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67932820434423525982322905 50949615325817644486742179)
          ·
            refine ⟨76424422988726466730113269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50949615325817644486742179 76424422988726466730113269)
            ·
              refine ⟨7164789655193106255948119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 76424422988726466730113269 7164789655193106255948119)
              ·
                refine ⟨10747184482789659383922179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7164789655193106255948119 10747184482789659383922179)
                ·
                  refine ⟨16120776724184489075883269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10747184482789659383922179 16120776724184489075883269)
                  ·
                    refine ⟨3022645635784591701728113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16120776724184489075883269 3022645635784591701728113)
                    ·
                      refine ⟨2266984226838443776296085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022645635784591701728113 2266984226838443776296085)
                      ·
                        rfl

theorem cell23_4414936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 1, 5, 1, 1, 4, 2].length) (baseStart_4414936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414936 prefixEnd_4414936 := by exact prefixLift 4414936
  have htrace : WordTrace (prefixWord ++ tailWord_4414936) baseStart_4414936 baseEnd_4414936 := by
    simpa [prefixWord, tailWord_4414936, baseEnd_4414936] using wordTrace_append hprefix tailTrace_4414936
  have hstable : (prefixWord ++ tailWord_4414936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414936).length < 2 ^ (prefixWord ++ tailWord_4414936).sum := by decide
  have hdescent : baseEnd_4414936 < baseStart_4414936 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4414987 : List Nat := [1, 1, 1, 1, 8, 2, 2, 1, 2, 2, 2]
def baseStart_4414987 : Nat := 118140960795 + 4414987 * 2 ^ 59
def prefixEnd_4414987 : Nat := 4983230072969 + 3 ^ 40 * 4414987 * 2
def baseEnd_4414987 : Nat := 2267010414351823076758351

theorem tailTrace_4414987 : CollatzResearch.WordTrace tailWord_4414987 prefixEnd_4414987 2267010414351823076758351 := by
  unfold tailWord_4414987
  simp only [CollatzResearch.WordTrace]
  refine ⟨161027804856263593594131215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107351869904175729062754143 161027804856263593594131215)
  ·
    refine ⟨241541707284395390391196823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161027804856263593594131215 241541707284395390391196823)
    ·
      refine ⟨362312560926593085586795235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241541707284395390391196823 362312560926593085586795235)
      ·
        refine ⟨543468841389889628380192853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362312560926593085586795235 543468841389889628380192853)
        ·
          refine ⟨6368775485037769082580385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 543468841389889628380192853 6368775485037769082580385)
          ·
            refine ⟨4776581613778326811935289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6368775485037769082580385 4776581613778326811935289)
            ·
              refine ⟨3582436210333745108951467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4776581613778326811935289 3582436210333745108951467)
              ·
                refine ⟨5373654315500617663427201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582436210333745108951467 5373654315500617663427201)
                ·
                  refine ⟨4030240736625463247570401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5373654315500617663427201 4030240736625463247570401)
                  ·
                    refine ⟨3022680552469097435677801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4030240736625463247570401 3022680552469097435677801)
                    ·
                      refine ⟨2267010414351823076758351, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022680552469097435677801 2267010414351823076758351)
                      ·
                        rfl

theorem cell23_4414987_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 2, 1, 2, 2, 2].length) (baseStart_4414987 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4414987 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4414987 prefixEnd_4414987 := by exact prefixLift 4414987
  have htrace : WordTrace (prefixWord ++ tailWord_4414987) baseStart_4414987 baseEnd_4414987 := by
    simpa [prefixWord, tailWord_4414987, baseEnd_4414987] using wordTrace_append hprefix tailTrace_4414987
  have hstable : (prefixWord ++ tailWord_4414987).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4414987).length < 2 ^ (prefixWord ++ tailWord_4414987).sum := by decide
  have hdescent : baseEnd_4414987 < baseStart_4414987 := by decide
  rcases family_descends (prefixWord ++ tailWord_4414987) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415026 : List Nat := [3, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2]
def baseStart_4415026 : Nat := 118140960795 + 4415026 * 2 ^ 59
def prefixEnd_4415026 : Nat := 4983230072969 + 3 ^ 40 * 4415026 * 2
def baseEnd_4415026 : Nat := 2267030440097348424170671

theorem tailTrace_4415026 : CollatzResearch.WordTrace tailWord_4415026 prefixEnd_4415026 2267030440097348424170671 := by
  unfold tailWord_4415026
  simp only [CollatzResearch.WordTrace]
  refine ⟨40257306825780575813700233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107352818202081535503200621 40257306825780575813700233)
  ·
    refine ⟨30192980119335431860275175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40257306825780575813700233 30192980119335431860275175)
    ·
      refine ⟨45289470179003147790412763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30192980119335431860275175 45289470179003147790412763)
      ·
        refine ⟨67934205268504721685619145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45289470179003147790412763 67934205268504721685619145)
        ·
          refine ⟨50950653951378541264214359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67934205268504721685619145 50950653951378541264214359)
          ·
            refine ⟨76425980927067811896321539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50950653951378541264214359 76425980927067811896321539)
            ·
              refine ⟨114638971390601717844482309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76425980927067811896321539 114638971390601717844482309)
              ·
                refine ⟨21494807135737822095840433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114638971390601717844482309 21494807135737822095840433)
                ·
                  refine ⟨16121105351803366571880325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21494807135737822095840433 16121105351803366571880325)
                  ·
                    refine ⟨3022707253463131232227561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16121105351803366571880325 3022707253463131232227561)
                    ·
                      refine ⟨2267030440097348424170671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022707253463131232227561 2267030440097348424170671)
                      ·
                        rfl

theorem cell23_4415026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 1, 4, 2, 4, 2].length) (baseStart_4415026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415026 prefixEnd_4415026 := by exact prefixLift 4415026
  have htrace : WordTrace (prefixWord ++ tailWord_4415026) baseStart_4415026 baseEnd_4415026 := by
    simpa [prefixWord, tailWord_4415026, baseEnd_4415026] using wordTrace_append hprefix tailTrace_4415026
  have hstable : (prefixWord ++ tailWord_4415026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415026).length < 2 ^ (prefixWord ++ tailWord_4415026).sum := by decide
  have hdescent : baseEnd_4415026 < baseStart_4415026 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415063 : List Nat := [1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 3]
def baseStart_4415063 : Nat := 118140960795 + 4415063 * 2 ^ 59
def prefixEnd_4415063 : Nat := 4983230072969 + 3 ^ 40 * 4415063 * 2
def baseEnd_4415063 : Nat := 2267049438881564779408001

theorem tailTrace_4415063 : CollatzResearch.WordTrace tailWord_4415063 prefixEnd_4415063 2267049438881564779408001 := by
  unfold tailWord_4415063
  simp only [CollatzResearch.WordTrace]
  refine ⟨161030576803988258573897843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107353717869325505715931895 161030576803988258573897843)
  ·
    refine ⟨241545865205982387860846765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161030576803988258573897843 241545865205982387860846765)
    ·
      refine ⟨90579699452243395447817537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241545865205982387860846765 90579699452243395447817537)
      ·
        refine ⟨67934774589182546585863153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90579699452243395447817537 67934774589182546585863153)
        ·
          refine ⟨50951080941886909939397365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67934774589182546585863153 50951080941886909939397365)
          ·
            refine ⟨4776663838301897806818503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50951080941886909939397365 4776663838301897806818503)
            ·
              refine ⟨7164995757452846710227755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776663838301897806818503 7164995757452846710227755)
              ·
                refine ⟨10747493636179270065341633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7164995757452846710227755 10747493636179270065341633)
                ·
                  refine ⟨8060620227134452549006225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10747493636179270065341633 8060620227134452549006225)
                  ·
                    refine ⟨6045465170350839411754669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8060620227134452549006225 6045465170350839411754669)
                    ·
                      refine ⟨2267049438881564779408001, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6045465170350839411754669 2267049438881564779408001)
                      ·
                        rfl

theorem cell23_4415063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 1, 1, 2, 2, 3].length) (baseStart_4415063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415063 prefixEnd_4415063 := by exact prefixLift 4415063
  have htrace : WordTrace (prefixWord ++ tailWord_4415063) baseStart_4415063 baseEnd_4415063 := by
    simpa [prefixWord, tailWord_4415063, baseEnd_4415063] using wordTrace_append hprefix tailTrace_4415063
  have hstable : (prefixWord ++ tailWord_4415063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415063).length < 2 ^ (prefixWord ++ tailWord_4415063).sum := by decide
  have hdescent : baseEnd_4415063 < baseStart_4415063 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415116 : List Nat := [2, 2, 1, 2, 1, 1, 3, 1, 2, 6, 2]
def baseStart_4415116 : Nat := 118140960795 + 4415116 * 2 ^ 59
def prefixEnd_4415116 : Nat := 4983230072969 + 3 ^ 40 * 4415116 * 2
def baseEnd_4415116 : Nat := 2267076653356253072045257

theorem tailTrace_4415116 : CollatzResearch.WordTrace tailWord_4415116 prefixEnd_4415116 2267076653356253072045257 := by
  unfold tailWord_4415116
  simp only [CollatzResearch.WordTrace]
  refine ⟨80516254936398124312788601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107355006581864165750384801 80516254936398124312788601)
  ·
    refine ⟨60387191202298593234591451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80516254936398124312788601 60387191202298593234591451)
    ·
      refine ⟨90580786803447889851887177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60387191202298593234591451 90580786803447889851887177)
      ·
        refine ⟨67935590102585917388915383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90580786803447889851887177 67935590102585917388915383)
        ·
          refine ⟨101903385153878876083373075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67935590102585917388915383 101903385153878876083373075)
          ·
            refine ⟨152855077730818314125059613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101903385153878876083373075 152855077730818314125059613)
            ·
              refine ⟨57320654149056867796897355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152855077730818314125059613 57320654149056867796897355)
              ·
                refine ⟨85980981223585301695346033, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57320654149056867796897355 85980981223585301695346033)
                ·
                  refine ⟨64485735917688976271509525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85980981223585301695346033 64485735917688976271509525)
                  ·
                    refine ⟨3022768871141670762727009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64485735917688976271509525 3022768871141670762727009)
                    ·
                      refine ⟨2267076653356253072045257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022768871141670762727009 2267076653356253072045257)
                      ·
                        rfl

theorem cell23_4415116_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 3, 1, 2, 6, 2].length) (baseStart_4415116 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415116 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415116 prefixEnd_4415116 := by exact prefixLift 4415116
  have htrace : WordTrace (prefixWord ++ tailWord_4415116) baseStart_4415116 baseEnd_4415116 := by
    simpa [prefixWord, tailWord_4415116, baseEnd_4415116] using wordTrace_append hprefix tailTrace_4415116
  have hstable : (prefixWord ++ tailWord_4415116).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415116).length < 2 ^ (prefixWord ++ tailWord_4415116).sum := by decide
  have hdescent : baseEnd_4415116 < baseStart_4415116 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415116) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415127 : List Nat := [1, 1, 3, 3, 2, 4, 1, 3, 1, 1, 3]
def baseStart_4415127 : Nat := 118140960795 + 4415127 * 2 ^ 59
def prefixEnd_4415127 : Nat := 4983230072969 + 3 ^ 40 * 4415127 * 2
def baseEnd_4415127 : Nat := 2267082301643452529007707

theorem tailTrace_4415127 : CollatzResearch.WordTrace tailWord_4415127 prefixEnd_4415127 2267082301643452529007707 := by
  unfold tailWord_4415127
  simp only [CollatzResearch.WordTrace]
  refine ⟨161032911075756397504227635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107355274050504265002818423 161032911075756397504227635)
  ·
    refine ⟨241549366613634596256341453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161032911075756397504227635 241549366613634596256341453)
    ·
      refine ⟨90581012480112973596128045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241549366613634596256341453 90581012480112973596128045)
      ·
        refine ⟨33967879680042365098548017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90581012480112973596128045 33967879680042365098548017)
        ·
          refine ⟨25475909760031773823911013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33967879680042365098548017 25475909760031773823911013)
          ·
            refine ⟨4776733080005957591983315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25475909760031773823911013 4776733080005957591983315)
            ·
              refine ⟨7165099620008936387974973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4776733080005957591983315 7165099620008936387974973)
              ·
                refine ⟨2686912357503351145490615, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7165099620008936387974973 2686912357503351145490615)
                ·
                  refine ⟨4030368536255026718235923, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686912357503351145490615 4030368536255026718235923)
                  ·
                    refine ⟨6045552804382540077353885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4030368536255026718235923 6045552804382540077353885)
                    ·
                      refine ⟨2267082301643452529007707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6045552804382540077353885 2267082301643452529007707)
                      ·
                        rfl

theorem cell23_4415127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 1, 3, 1, 1, 3].length) (baseStart_4415127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415127 prefixEnd_4415127 := by exact prefixLift 4415127
  have htrace : WordTrace (prefixWord ++ tailWord_4415127) baseStart_4415127 baseEnd_4415127 := by
    simpa [prefixWord, tailWord_4415127, baseEnd_4415127] using wordTrace_append hprefix tailTrace_4415127
  have hstable : (prefixWord ++ tailWord_4415127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415127).length < 2 ^ (prefixWord ++ tailWord_4415127).sum := by decide
  have hdescent : baseEnd_4415127 < baseStart_4415127 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415136 : List Nat := [2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5]
def baseStart_4415136 : Nat := 118140960795 + 4415136 * 2 ^ 59
def prefixEnd_4415136 : Nat := 4983230072969 + 3 ^ 40 * 4415136 * 2
def baseEnd_4415136 : Nat := 2267086922969342993795165

theorem tailTrace_4415136 : CollatzResearch.WordTrace tailWord_4415136 prefixEnd_4415136 2267086922969342993795165 := by
  unfold tailWord_4415136
  simp only [CollatzResearch.WordTrace]
  refine ⟨80516619666361896020652631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107355492888482528027536841 80516619666361896020652631)
  ·
    refine ⟨120774929499542844030978947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80516619666361896020652631 120774929499542844030978947)
    ·
      refine ⟨181162394249314266046468421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120774929499542844030978947 181162394249314266046468421)
      ·
        refine ⟨33967948921746424883712829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181162394249314266046468421 33967948921746424883712829)
        ·
          refine ⟨12737980845654909331392311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 33967948921746424883712829 12737980845654909331392311)
          ·
            refine ⟨19106971268482363997088467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12737980845654909331392311 19106971268482363997088467)
            ·
              refine ⟨28660456902723545995632701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19106971268482363997088467 28660456902723545995632701)
              ·
                refine ⟨10747671338521329748362263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28660456902723545995632701 10747671338521329748362263)
                ·
                  refine ⟨16121507007781994622543395, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10747671338521329748362263 16121507007781994622543395)
                  ·
                    refine ⟨24182260511672991933815093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16121507007781994622543395 24182260511672991933815093)
                    ·
                      refine ⟨2267086922969342993795165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24182260511672991933815093 2267086922969342993795165)
                      ·
                        rfl

theorem cell23_4415136_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 5].length) (baseStart_4415136 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415136 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415136 prefixEnd_4415136 := by exact prefixLift 4415136
  have htrace : WordTrace (prefixWord ++ tailWord_4415136) baseStart_4415136 baseEnd_4415136 := by
    simpa [prefixWord, tailWord_4415136, baseEnd_4415136] using wordTrace_append hprefix tailTrace_4415136
  have hstable : (prefixWord ++ tailWord_4415136).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415136).length < 2 ^ (prefixWord ++ tailWord_4415136).sum := by decide
  have hdescent : baseEnd_4415136 < baseStart_4415136 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415136) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415179 : List Nat := [1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5]
def baseStart_4415179 : Nat := 118140960795 + 4415179 * 2 ^ 59
def prefixEnd_4415179 : Nat := 4983230072969 + 3 ^ 40 * 4415179 * 2
def baseEnd_4415179 : Nat := 2267109002637486325557467

theorem tailTrace_4415179 : CollatzResearch.WordTrace tailWord_4415179 prefixEnd_4415179 2267109002637486325557467 := by
  unfold tailWord_4415179
  simp only [CollatzResearch.WordTrace]
  refine ⟨161034807671568010385120591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107356538447712006923413727 161034807671568010385120591)
  ·
    refine ⟨241552211507352015577680887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161034807671568010385120591 241552211507352015577680887)
    ·
      refine ⟨362328317261028023366521331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241552211507352015577680887 362328317261028023366521331)
      ·
        refine ⟨543492475891542035049781997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362328317261028023366521331 543492475891542035049781997)
        ·
          refine ⟨203809678459328263143668249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543492475891542035049781997 203809678459328263143668249)
          ·
            refine ⟨152857258844496197357751187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 203809678459328263143668249 152857258844496197357751187)
            ·
              refine ⟨229285888266744296036626781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152857258844496197357751187 229285888266744296036626781)
              ·
                refine ⟨85982208100029111013735043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229285888266744296036626781 85982208100029111013735043)
                ·
                  refine ⟨128973312150043666520602565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85982208100029111013735043 128973312150043666520602565)
                  ·
                    refine ⟨24182496028133187472612981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 128973312150043666520602565 24182496028133187472612981)
                    ·
                      refine ⟨2267109002637486325557467, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24182496028133187472612981 2267109002637486325557467)
                      ·
                        rfl

theorem cell23_4415179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 1, 3, 1, 4, 5].length) (baseStart_4415179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415179 prefixEnd_4415179 := by exact prefixLift 4415179
  have htrace : WordTrace (prefixWord ++ tailWord_4415179) baseStart_4415179 baseEnd_4415179 := by
    simpa [prefixWord, tailWord_4415179, baseEnd_4415179] using wordTrace_append hprefix tailTrace_4415179
  have hstable : (prefixWord ++ tailWord_4415179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415179).length < 2 ^ (prefixWord ++ tailWord_4415179).sum := by decide
  have hdescent : baseEnd_4415179 < baseStart_4415179 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415190 : List Nat := [5, 2, 1, 3, 2, 10]
def baseStart_4415190 : Nat := 118140960795 + 4415190 * 2 ^ 59
def prefixEnd_4415190 : Nat := 4983230072969 + 3 ^ 40 * 4415190 * 2
def baseEnd_4415190 : Nat := 9329689921500764537119

theorem tailTrace_4415190 : CollatzResearch.WordTrace tailWord_4415190 prefixEnd_4415190 9329689921500764537119 := by
  unfold tailWord_4415190
  simp only [CollatzResearch.WordTrace]
  refine ⟨10064700554658009953985689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 107356805916352106175847349 10064700554658009953985689)
  ·
    refine ⟨7548525415993507465489267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 10064700554658009953985689 7548525415993507465489267)
    ·
      refine ⟨11322788123990261198233901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 7548525415993507465489267 11322788123990261198233901)
      ·
        refine ⟨4246045546496347949337713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 11322788123990261198233901 4246045546496347949337713)
        ·
          refine ⟨3184534159872260962003285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4246045546496347949337713 3184534159872260962003285)
          ·
            refine ⟨9329689921500764537119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 3184534159872260962003285 9329689921500764537119)
            ·
              rfl

theorem cell23_4415190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 3, 2, 10].length) (baseStart_4415190 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415190 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415190 prefixEnd_4415190 := by exact prefixLift 4415190
  have htrace : WordTrace (prefixWord ++ tailWord_4415190) baseStart_4415190 baseEnd_4415190 := by
    simpa [prefixWord, tailWord_4415190, baseEnd_4415190] using wordTrace_append hprefix tailTrace_4415190
  have hstable : (prefixWord ++ tailWord_4415190).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415190).length < 2 ^ (prefixWord ++ tailWord_4415190).sum := by decide
  have hdescent : baseEnd_4415190 < baseStart_4415190 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415201 : List Nat := [1, 2, 3, 1, 5, 2, 2, 2, 1, 2, 2]
def baseStart_4415201 : Nat := 118140960795 + 4415201 * 2 ^ 59
def prefixEnd_4415201 : Nat := 4983230072969 + 3 ^ 40 * 4415201 * 2
def baseEnd_4415201 : Nat := 2267120299211885239482367

theorem tailTrace_4415201 : CollatzResearch.WordTrace tailWord_4415201 prefixEnd_4415201 2267120299211885239482367 := by
  unfold tailWord_4415201
  simp only [CollatzResearch.WordTrace]
  refine ⟨161035610077488308142421457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107357073384992205428280971 161035610077488308142421457)
  ·
    refine ⟨120776707558116231106816093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161035610077488308142421457 120776707558116231106816093)
    ·
      refine ⟨45291265334293586665056035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120776707558116231106816093 45291265334293586665056035)
      ·
        refine ⟨67936898001440379997584053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45291265334293586665056035 67936898001440379997584053)
        ·
          refine ⟨6369084187635035624773505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67936898001440379997584053 6369084187635035624773505)
          ·
            refine ⟨4776813140726276718580129, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6369084187635035624773505 4776813140726276718580129)
            ·
              refine ⟨3582609855544707538935097, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4776813140726276718580129 3582609855544707538935097)
              ·
                refine ⟨2686957391658530654201323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3582609855544707538935097 2686957391658530654201323)
                ·
                  refine ⟨4030436087487795981301985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2686957391658530654201323 4030436087487795981301985)
                  ·
                    refine ⟨3022827065615846985976489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4030436087487795981301985 3022827065615846985976489)
                    ·
                      refine ⟨2267120299211885239482367, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022827065615846985976489 2267120299211885239482367)
                      ·
                        rfl

theorem cell23_4415201_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 5, 2, 2, 2, 1, 2, 2].length) (baseStart_4415201 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415201 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415201 prefixEnd_4415201 := by exact prefixLift 4415201
  have htrace : WordTrace (prefixWord ++ tailWord_4415201) baseStart_4415201 baseEnd_4415201 := by
    simpa [prefixWord, tailWord_4415201, baseEnd_4415201] using wordTrace_append hprefix tailTrace_4415201
  have hstable : (prefixWord ++ tailWord_4415201).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415201).length < 2 ^ (prefixWord ++ tailWord_4415201).sum := by decide
  have hdescent : baseEnd_4415201 < baseStart_4415201 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415201) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415223 : List Nat := [1, 1, 3, 1, 1, 1, 5, 3, 1, 4, 2]
def baseStart_4415223 : Nat := 118140960795 + 4415223 * 2 ^ 59
def prefixEnd_4415223 : Nat := 4983230072969 + 3 ^ 40 * 4415223 * 2
def baseEnd_4415223 : Nat := 2267131595786284153407265

theorem tailTrace_4415223 : CollatzResearch.WordTrace tailWord_4415223 prefixEnd_4415223 2267131595786284153407265 := by
  unfold tailWord_4415223
  simp only [CollatzResearch.WordTrace]
  refine ⟨161036412483408605899722323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107357608322272403933148215 161036412483408605899722323)
  ·
    refine ⟨241554618725112908849583485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161036412483408605899722323 241554618725112908849583485)
    ·
      refine ⟨90582982021917340818593807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241554618725112908849583485 90582982021917340818593807)
      ·
        refine ⟨135874473032876011227890711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90582982021917340818593807 135874473032876011227890711)
        ·
          refine ⟨203811709549314016841836067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135874473032876011227890711 203811709549314016841836067)
          ·
            refine ⟨305717564323971025262754101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203811709549314016841836067 305717564323971025262754101)
            ·
              refine ⟨28661021655372283618383197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 305717564323971025262754101 28661021655372283618383197)
              ·
                refine ⟨10747883120764606356893699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28661021655372283618383197 10747883120764606356893699)
                ·
                  refine ⟨16121824681146909535340549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10747883120764606356893699 16121824681146909535340549)
                  ·
                    refine ⟨3022842127715045537876353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16121824681146909535340549 3022842127715045537876353)
                    ·
                      refine ⟨2267131595786284153407265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022842127715045537876353 2267131595786284153407265)
                      ·
                        rfl

theorem cell23_4415223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 3, 1, 4, 2].length) (baseStart_4415223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415223 prefixEnd_4415223 := by exact prefixLift 4415223
  have htrace : WordTrace (prefixWord ++ tailWord_4415223) baseStart_4415223 baseEnd_4415223 := by
    simpa [prefixWord, tailWord_4415223, baseEnd_4415223] using wordTrace_append hprefix tailTrace_4415223
  have hstable : (prefixWord ++ tailWord_4415223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415223).length < 2 ^ (prefixWord ++ tailWord_4415223).sum := by decide
  have hdescent : baseEnd_4415223 < baseStart_4415223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415226 : List Nat := [3, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3]
def baseStart_4415226 : Nat := 118140960795 + 4415226 * 2 ^ 59
def prefixEnd_4415226 : Nat := 4983230072969 + 3 ^ 40 * 4415226 * 2
def baseEnd_4415226 : Nat := 2267133136228247641669751

theorem tailTrace_4415226 : CollatzResearch.WordTrace tailWord_4415226 prefixEnd_4415226 2267133136228247641669751 := by
  unfold tailWord_4415226
  simp only [CollatzResearch.WordTrace]
  refine ⟨40259130475599434353020383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107357681268265158274721021 40259130475599434353020383)
  ·
    refine ⟨60388695713399151529530575, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40259130475599434353020383 60388695713399151529530575)
    ·
      refine ⟨90583043570098727294295863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60388695713399151529530575 90583043570098727294295863)
      ·
        refine ⟨135874565355148090941443795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90583043570098727294295863 135874565355148090941443795)
        ·
          refine ⟨203811848032722136412165693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135874565355148090941443795 203811848032722136412165693)
          ·
            refine ⟨76429443012270801154562135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203811848032722136412165693 76429443012270801154562135)
            ·
              refine ⟨114644164518406201731843203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76429443012270801154562135 114644164518406201731843203)
              ·
                refine ⟨171966246777609302597764805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114644164518406201731843203 171966246777609302597764805)
                ·
                  refine ⟨32243671270801744237080901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 171966246777609302597764805 32243671270801744237080901)
                  ·
                    refine ⟨6045688363275327044452669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32243671270801744237080901 6045688363275327044452669)
                    ·
                      refine ⟨2267133136228247641669751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6045688363275327044452669 2267133136228247641669751)
                      ·
                        rfl

theorem cell23_4415226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 1, 1, 4, 4, 3].length) (baseStart_4415226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415226 prefixEnd_4415226 := by exact prefixLift 4415226
  have htrace : WordTrace (prefixWord ++ tailWord_4415226) baseStart_4415226 baseEnd_4415226 := by
    simpa [prefixWord, tailWord_4415226, baseEnd_4415226] using wordTrace_append hprefix tailTrace_4415226
  have hstable : (prefixWord ++ tailWord_4415226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415226).length < 2 ^ (prefixWord ++ tailWord_4415226).sum := by decide
  have hdescent : baseEnd_4415226 < baseStart_4415226 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415238 : List Nat := [6, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3]
def baseStart_4415238 : Nat := 118140960795 + 4415238 * 2 ^ 59
def prefixEnd_4415238 : Nat := 4983230072969 + 3 ^ 40 * 4415238 * 2
def baseEnd_4415238 : Nat := 2267139297996101594719697

theorem tailTrace_4415238 : CollatzResearch.WordTrace tailWord_4415238 prefixEnd_4415238 2267139297996101594719697 := by
  unfold tailWord_4415238
  simp only [CollatzResearch.WordTrace]
  refine ⟨5032404986823570733172449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 107357973052236175641012245 5032404986823570733172449)
  ·
    refine ⟨3774303740117678049879337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5032404986823570733172449 3774303740117678049879337)
    ·
      refine ⟨2830727805088258537409503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 3774303740117678049879337 2830727805088258537409503)
      ·
        refine ⟨4246091707632387806114255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2830727805088258537409503 4246091707632387806114255)
        ·
          refine ⟨6369137561448581709171383, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246091707632387806114255 6369137561448581709171383)
          ·
            refine ⟨9553706342172872563757075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369137561448581709171383 9553706342172872563757075)
            ·
              refine ⟨14330559513259308845635613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9553706342172872563757075 14330559513259308845635613)
              ·
                refine ⟨5373959817472240817113355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14330559513259308845635613 5373959817472240817113355)
                ·
                  refine ⟨8060939726208361225670033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5373959817472240817113355 8060939726208361225670033)
                  ·
                    refine ⟨6045704794656270919252525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8060939726208361225670033 6045704794656270919252525)
                    ·
                      refine ⟨2267139297996101594719697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6045704794656270919252525 2267139297996101594719697)
                      ·
                        rfl

theorem cell23_4415238_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3].length) (baseStart_4415238 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415238 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415238 prefixEnd_4415238 := by exact prefixLift 4415238
  have htrace : WordTrace (prefixWord ++ tailWord_4415238) baseStart_4415238 baseEnd_4415238 := by
    simpa [prefixWord, tailWord_4415238, baseEnd_4415238] using wordTrace_append hprefix tailTrace_4415238
  have hstable : (prefixWord ++ tailWord_4415238).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415238).length < 2 ^ (prefixWord ++ tailWord_4415238).sum := by decide
  have hdescent : baseEnd_4415238 < baseStart_4415238 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415238) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415240 : List Nat := [2, 1, 3, 2, 2, 1, 2, 2, 4, 2, 2]
def baseStart_4415240 : Nat := 118140960795 + 4415240 * 2 ^ 59
def prefixEnd_4415240 : Nat := 4983230072969 + 3 ^ 40 * 4415240 * 2
def baseEnd_4415240 : Nat := 2267140324957410586894687

theorem tailTrace_4415240 : CollatzResearch.WordTrace tailWord_4415240 prefixEnd_4415240 2267140324957410586894687 := by
  unfold tailWord_4415240
  simp only [CollatzResearch.WordTrace]
  refine ⟨80518516262173508901545587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107358021682898011868727449 80518516262173508901545587)
  ·
    refine ⟨120777774393260263352318381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80518516262173508901545587 120777774393260263352318381)
    ·
      refine ⟨45291665397472598757119393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120777774393260263352318381 45291665397472598757119393)
      ·
        refine ⟨33968749048104449067839545, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45291665397472598757119393 33968749048104449067839545)
        ·
          refine ⟨25476561786078336800879659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33968749048104449067839545 25476561786078336800879659)
          ·
            refine ⟨38214842679117505201319489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25476561786078336800879659 38214842679117505201319489)
            ·
              refine ⟨28661132009338128900989617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38214842679117505201319489 28661132009338128900989617)
              ·
                refine ⟨21495849007003596675742213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28661132009338128900989617 21495849007003596675742213)
                ·
                  refine ⟨4030471688813174376701665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21495849007003596675742213 4030471688813174376701665)
                  ·
                    refine ⟨3022853766609880782526249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4030471688813174376701665 3022853766609880782526249)
                    ·
                      refine ⟨2267140324957410586894687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3022853766609880782526249 2267140324957410586894687)
                      ·
                        rfl

theorem cell23_4415240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 2, 4, 2, 2].length) (baseStart_4415240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415240 prefixEnd_4415240 := by exact prefixLift 4415240
  have htrace : WordTrace (prefixWord ++ tailWord_4415240) baseStart_4415240 baseEnd_4415240 := by
    simpa [prefixWord, tailWord_4415240, baseEnd_4415240] using wordTrace_append hprefix tailTrace_4415240
  have hstable : (prefixWord ++ tailWord_4415240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415240).length < 2 ^ (prefixWord ++ tailWord_4415240).sum := by decide
  have hdescent : baseEnd_4415240 < baseStart_4415240 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415263 : List Nat := [1, 1, 2, 4, 2, 1, 1, 6, 5]
def baseStart_4415263 : Nat := 118140960795 + 4415263 * 2 ^ 59
def prefixEnd_4415263 : Nat := 4983230072969 + 3 ^ 40 * 4415263 * 2
def baseEnd_4415263 : Nat := 251905792779162666323009

theorem tailTrace_4415263 : CollatzResearch.WordTrace tailWord_4415263 prefixEnd_4415263 251905792779162666323009 := by
  unfold tailWord_4415263
  simp only [CollatzResearch.WordTrace]
  refine ⟨161037871403263692731178443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107358580935509128487452295 161037871403263692731178443)
  ·
    refine ⟨241556807104895539096767665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161037871403263692731178443 241556807104895539096767665)
    ·
      refine ⟨181167605328671654322575749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241556807104895539096767665 181167605328671654322575749)
      ·
        refine ⟨33968925999125935185482953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 181167605328671654322575749 33968925999125935185482953)
        ·
          refine ⟨25476694499344451389112215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33968925999125935185482953 25476694499344451389112215)
          ·
            refine ⟨38215041749016677083668323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25476694499344451389112215 38215041749016677083668323)
            ·
              refine ⟨57322562623525015625502485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38215041749016677083668323 57322562623525015625502485)
              ·
                refine ⟨2686995122977735107445429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 57322562623525015625502485 2686995122977735107445429)
                ·
                  refine ⟨251905792779162666323009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2686995122977735107445429 251905792779162666323009)
                  ·
                    rfl

theorem cell23_4415263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 1, 1, 6, 5].length) (baseStart_4415263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415263 prefixEnd_4415263 := by exact prefixLift 4415263
  have htrace : WordTrace (prefixWord ++ tailWord_4415263) baseStart_4415263 baseEnd_4415263 := by
    simpa [prefixWord, tailWord_4415263, baseEnd_4415263] using wordTrace_append hprefix tailTrace_4415263
  have hstable : (prefixWord ++ tailWord_4415263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415263).length < 2 ^ (prefixWord ++ tailWord_4415263).sum := by decide
  have hdescent : baseEnd_4415263 < baseStart_4415263 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415276 : List Nat := [2, 2, 1, 1, 1, 5, 1, 2, 1, 7]
def baseStart_4415276 : Nat := 118140960795 + 4415276 * 2 ^ 59
def prefixEnd_4415276 : Nat := 4983230072969 + 3 ^ 40 * 4415276 * 2
def baseEnd_4415276 : Nat := 755719603420324148681507

theorem tailTrace_4415276 : CollatzResearch.WordTrace tailWord_4415276 prefixEnd_4415276 755719603420324148681507 := by
  unfold tailWord_4415276
  simp only [CollatzResearch.WordTrace]
  refine ⟨80519172776108297975700841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107358897034811063967601121 80519172776108297975700841)
  ·
    refine ⟨60389379582081223481775631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80519172776108297975700841 60389379582081223481775631)
    ·
      refine ⟨90584069373121835222663447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60389379582081223481775631 90584069373121835222663447)
      ·
        refine ⟨135876104059682752833995171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90584069373121835222663447 135876104059682752833995171)
        ·
          refine ⟨203814156089524129250992757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135876104059682752833995171 203814156089524129250992757)
          ·
            refine ⟨19107577133392887117280571, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 203814156089524129250992757 19107577133392887117280571)
            ·
              refine ⟨28661365700089330675920857, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19107577133392887117280571 28661365700089330675920857)
              ·
                refine ⟨21496024275066998006940643, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28661365700089330675920857 21496024275066998006940643)
                ·
                  refine ⟨32244036412600497010410965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21496024275066998006940643 32244036412600497010410965)
                  ·
                    refine ⟨755719603420324148681507, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32244036412600497010410965 755719603420324148681507)
                    ·
                      rfl

theorem cell23_4415276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 7].length) (baseStart_4415276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415276 prefixEnd_4415276 := by exact prefixLift 4415276
  have htrace : WordTrace (prefixWord ++ tailWord_4415276) baseStart_4415276 baseEnd_4415276 := by
    simpa [prefixWord, tailWord_4415276, baseEnd_4415276] using wordTrace_append hprefix tailTrace_4415276
  have hstable : (prefixWord ++ tailWord_4415276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415276).length < 2 ^ (prefixWord ++ tailWord_4415276).sum := by decide
  have hdescent : baseEnd_4415276 < baseStart_4415276 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415293 : List Nat := [1, 4, 1, 4, 1, 1, 2, 1, 1, 7]
def baseStart_4415293 : Nat := 118140960795 + 4415293 * 2 ^ 59
def prefixEnd_4415293 : Nat := 4983230072969 + 3 ^ 40 * 4415293 * 2
def baseEnd_4415293 : Nat := 755722513144032959843981

theorem tailTrace_4415293 : CollatzResearch.WordTrace tailWord_4415293 prefixEnd_4415293 755722513144032959843981 := by
  unfold tailWord_4415293
  simp only [CollatzResearch.WordTrace]
  refine ⟨161038965593155007854770533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107359310395436671903180355 161038965593155007854770533)
  ·
    refine ⟨30194806048716563972769475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161038965593155007854770533 30194806048716563972769475)
    ·
      refine ⟨45292209073074845959154213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30194806048716563972769475 45292209073074845959154213)
      ·
        refine ⟨8492289201201533617341415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 45292209073074845959154213 8492289201201533617341415)
        ·
          refine ⟨12738433801802300426012123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8492289201201533617341415 12738433801802300426012123)
          ·
            refine ⟨19107650702703450639018185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12738433801802300426012123 19107650702703450639018185)
            ·
              refine ⟨14330738027027587979263639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19107650702703450639018185 14330738027027587979263639)
              ·
                refine ⟨21496107040541381968895459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14330738027027587979263639 21496107040541381968895459)
                ·
                  refine ⟨32244160560812072953343189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21496107040541381968895459 32244160560812072953343189)
                  ·
                    refine ⟨755722513144032959843981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32244160560812072953343189 755722513144032959843981)
                    ·
                      rfl

theorem cell23_4415293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 1, 1, 7].length) (baseStart_4415293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415293 prefixEnd_4415293 := by exact prefixLift 4415293
  have htrace : WordTrace (prefixWord ++ tailWord_4415293) baseStart_4415293 baseEnd_4415293 := by
    simpa [prefixWord, tailWord_4415293, baseEnd_4415293] using wordTrace_append hprefix tailTrace_4415293
  have hstable : (prefixWord ++ tailWord_4415293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415293).length < 2 ^ (prefixWord ++ tailWord_4415293).sum := by decide
  have hdescent : baseEnd_4415293 < baseStart_4415293 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415313 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 4]
def baseStart_4415313 : Nat := 118140960795 + 4415313 * 2 ^ 59
def prefixEnd_4415313 : Nat := 4983230072969 + 3 ^ 40 * 4415313 * 2
def baseEnd_4415313 : Nat := 2267177809045188801281851

theorem tailTrace_4415313 : CollatzResearch.WordTrace tailWord_4415313 prefixEnd_4415313 2267177809045188801281851 := by
  unfold tailWord_4415313
  simp only [CollatzResearch.WordTrace]
  refine ⟨161039695053082551270498593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107359796702055034180332395 161039695053082551270498593)
  ·
    refine ⟨120779771289811913452873945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161039695053082551270498593 120779771289811913452873945)
    ·
      refine ⟨90584828467358935089655459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120779771289811913452873945 90584828467358935089655459)
      ·
        refine ⟨135877242701038402634483189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90584828467358935089655459 135877242701038402634483189)
        ·
          refine ⟨12738491503222350246982799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135877242701038402634483189 12738491503222350246982799)
          ·
            refine ⟨19107737254833525370474199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12738491503222350246982799 19107737254833525370474199)
            ·
              refine ⟨28661605882250288055711299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19107737254833525370474199 28661605882250288055711299)
              ·
                refine ⟨42992408823375432083566949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28661605882250288055711299 42992408823375432083566949)
                ·
                  refine ⟨8061076654382893515668803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 42992408823375432083566949 8061076654382893515668803)
                  ·
                    refine ⟨12091614981574340273503205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8061076654382893515668803 12091614981574340273503205)
                    ·
                      refine ⟨2267177809045188801281851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12091614981574340273503205 2267177809045188801281851)
                      ·
                        rfl

theorem cell23_4415313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 4, 1, 4].length) (baseStart_4415313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415313 prefixEnd_4415313 := by exact prefixLift 4415313
  have htrace : WordTrace (prefixWord ++ tailWord_4415313) baseStart_4415313 baseEnd_4415313 := by
    simpa [prefixWord, tailWord_4415313, baseEnd_4415313] using wordTrace_append hprefix tailTrace_4415313
  have hstable : (prefixWord ++ tailWord_4415313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415313).length < 2 ^ (prefixWord ++ tailWord_4415313).sum := by decide
  have hdescent : baseEnd_4415313 < baseStart_4415313 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415333 : List Nat := [1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 3]
def baseStart_4415333 : Nat := 118140960795 + 4415333 * 2 ^ 59
def prefixEnd_4415333 : Nat := 4983230072969 + 3 ^ 40 * 4415333 * 2
def baseEnd_4415333 : Nat := 2267188078658278723031759

theorem tailTrace_4415333 : CollatzResearch.WordTrace tailWord_4415333 prefixEnd_4415333 2267188078658278723031759 := by
  unfold tailWord_4415333
  simp only [CollatzResearch.WordTrace]
  refine ⟨161040424513010094686226653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107360283008673396457484435 161040424513010094686226653)
  ·
    refine ⟨60390159192378785507334995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161040424513010094686226653 60390159192378785507334995)
    ·
      refine ⟨90585238788568178261002493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60390159192378785507334995 90585238788568178261002493)
      ·
        refine ⟨33969464545713066847875935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90585238788568178261002493 33969464545713066847875935)
        ·
          refine ⟨50954196818569600271813903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33969464545713066847875935 50954196818569600271813903)
          ·
            refine ⟨76431295227854400407720855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50954196818569600271813903 76431295227854400407720855)
            ·
              refine ⟨114646942841781600611581283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76431295227854400407720855 114646942841781600611581283)
              ·
                refine ⟨171970414262672400917371925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114646942841781600611581283 171970414262672400917371925)
                ·
                  refine ⟨8061113168562768793001809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 171970414262672400917371925 8061113168562768793001809)
                  ·
                    refine ⟨6045834876422076594751357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8061113168562768793001809 6045834876422076594751357)
                    ·
                      refine ⟨2267188078658278723031759, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6045834876422076594751357 2267188078658278723031759)
                      ·
                        rfl

theorem cell23_4415333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 1, 1, 1, 6, 2, 3].length) (baseStart_4415333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415333 prefixEnd_4415333 := by exact prefixLift 4415333
  have htrace : WordTrace (prefixWord ++ tailWord_4415333) baseStart_4415333 baseEnd_4415333 := by
    simpa [prefixWord, tailWord_4415333, baseEnd_4415333] using wordTrace_append hprefix tailTrace_4415333
  have hstable : (prefixWord ++ tailWord_4415333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415333).length < 2 ^ (prefixWord ++ tailWord_4415333).sum := by decide
  have hdescent : baseEnd_4415333 < baseStart_4415333 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415356 : List Nat := [2, 2, 2, 1, 1, 1, 1, 1, 3, 1, 8]
def baseStart_4415356 : Nat := 118140960795 + 4415356 * 2 ^ 59
def prefixEnd_4415356 : Nat := 4983230072969 + 3 ^ 40 * 4415356 * 2
def baseEnd_4415356 : Nat := 2267199888713332133044153

theorem tailTrace_4415356 : CollatzResearch.WordTrace tailWord_4415356 prefixEnd_4415356 2267199888713332133044153 := by
  unfold tailWord_4415356
  simp only [CollatzResearch.WordTrace]
  refine ⟨80520631695963384807156961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107360842261284513076209281 80520631695963384807156961)
  ·
    refine ⟨60390473771972538605367721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80520631695963384807156961 60390473771972538605367721)
    ·
      refine ⟨45292855328979403954025791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60390473771972538605367721 45292855328979403954025791)
      ·
        refine ⟨67939282993469105931038687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45292855328979403954025791 67939282993469105931038687)
        ·
          refine ⟨101908924490203658896558031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67939282993469105931038687 101908924490203658896558031)
          ·
            refine ⟨152863386735305488344837047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101908924490203658896558031 152863386735305488344837047)
            ·
              refine ⟨229295080102958232517255571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152863386735305488344837047 229295080102958232517255571)
              ·
                refine ⟨343942620154437348775883357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 229295080102958232517255571 343942620154437348775883357)
                ·
                  refine ⟨128978482557914005790956259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 343942620154437348775883357 128978482557914005790956259)
                  ·
                    refine ⟨193467723836871008686434389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 128978482557914005790956259 193467723836871008686434389)
                    ·
                      refine ⟨2267199888713332133044153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 193467723836871008686434389 2267199888713332133044153)
                      ·
                        rfl

theorem cell23_4415356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 1, 3, 1, 8].length) (baseStart_4415356 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415356 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415356 prefixEnd_4415356 := by exact prefixLift 4415356
  have htrace : WordTrace (prefixWord ++ tailWord_4415356) baseStart_4415356 baseEnd_4415356 := by
    simpa [prefixWord, tailWord_4415356, baseEnd_4415356] using wordTrace_append hprefix tailTrace_4415356
  have hstable : (prefixWord ++ tailWord_4415356).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415356).length < 2 ^ (prefixWord ++ tailWord_4415356).sum := by decide
  have hdescent : baseEnd_4415356 < baseStart_4415356 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415376 : List Nat := [2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7]
def baseStart_4415376 : Nat := 118140960795 + 4415376 * 2 ^ 59
def prefixEnd_4415376 : Nat := 4983230072969 + 3 ^ 40 * 4415376 * 2
def baseEnd_4415376 : Nat := 2267210158326422054794061

theorem tailTrace_4415376 : CollatzResearch.WordTrace tailWord_4415376 prefixEnd_4415376 2267210158326422054794061 := by
  unfold tailWord_4415376
  simp only [CollatzResearch.WordTrace]
  refine ⟨80520996425927156515020991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107361328567902875353361321 80520996425927156515020991)
  ·
    refine ⟨120781494638890734772531487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80520996425927156515020991 120781494638890734772531487)
    ·
      refine ⟨181172241958336102158797231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120781494638890734772531487 181172241958336102158797231)
      ·
        refine ⟨271758362937504153238195847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181172241958336102158797231 271758362937504153238195847)
        ·
          refine ⟨407637544406256229857293771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271758362937504153238195847 407637544406256229857293771)
          ·
            refine ⟨611456316609384344785940657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407637544406256229857293771 611456316609384344785940657)
            ·
              refine ⟨458592237457038258589455493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611456316609384344785940657 458592237457038258589455493)
              ·
                refine ⟨85986044523194673485522905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 458592237457038258589455493 85986044523194673485522905)
                ·
                  refine ⟨64489533392396005114142179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 85986044523194673485522905 64489533392396005114142179)
                  ·
                    refine ⟨96734300088594007671213269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 64489533392396005114142179 96734300088594007671213269)
                    ·
                      refine ⟨2267210158326422054794061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96734300088594007671213269 2267210158326422054794061)
                      ·
                        rfl

theorem cell23_4415376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 7].length) (baseStart_4415376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415376 prefixEnd_4415376 := by exact prefixLift 4415376
  have htrace : WordTrace (prefixWord ++ tailWord_4415376) baseStart_4415376 baseEnd_4415376 := by
    simpa [prefixWord, tailWord_4415376, baseEnd_4415376] using wordTrace_append hprefix tailTrace_4415376
  have hstable : (prefixWord ++ tailWord_4415376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415376).length < 2 ^ (prefixWord ++ tailWord_4415376).sum := by decide
  have hdescent : baseEnd_4415376 < baseStart_4415376 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415383 : List Nat := [1, 1, 3, 3, 1, 3, 1, 2, 3, 5]
def baseStart_4415383 : Nat := 118140960795 + 4415383 * 2 ^ 59
def prefixEnd_4415383 : Nat := 4983230072969 + 3 ^ 40 * 4415383 * 2
def baseEnd_4415383 : Nat := 755737917563667842468843

theorem tailTrace_4415383 : CollatzResearch.WordTrace tailWord_4415383 prefixEnd_4415383 755737917563667842468843 := by
  unfold tailWord_4415383
  simp only [CollatzResearch.WordTrace]
  refine ⟨161042248162828953225546803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107361498775219302150364535 161042248162828953225546803)
  ·
    refine ⟨241563372244243429838320205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161042248162828953225546803 241563372244243429838320205)
    ·
      refine ⟨90586264591591286189370077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241563372244243429838320205 90586264591591286189370077)
      ·
        refine ⟨33969849221846732321013779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90586264591591286189370077 33969849221846732321013779)
        ·
          refine ⟨50954773832770098481520669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33969849221846732321013779 50954773832770098481520669)
          ·
            refine ⟨19108040187288786930570251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50954773832770098481520669 19108040187288786930570251)
            ·
              refine ⟨28662060280933180395855377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19108040187288786930570251 28662060280933180395855377)
              ·
                refine ⟨21496545210699885296891533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28662060280933180395855377 21496545210699885296891533)
                ·
                  refine ⟨8061204454012456986334325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21496545210699885296891533 8061204454012456986334325)
                  ·
                    refine ⟨755737917563667842468843, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8061204454012456986334325 755737917563667842468843)
                    ·
                      rfl

theorem cell23_4415383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 2, 3, 5].length) (baseStart_4415383 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415383 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415383 prefixEnd_4415383 := by exact prefixLift 4415383
  have htrace : WordTrace (prefixWord ++ tailWord_4415383) baseStart_4415383 baseEnd_4415383 := by
    simpa [prefixWord, tailWord_4415383, baseEnd_4415383] using wordTrace_append hprefix tailTrace_4415383
  have hstable : (prefixWord ++ tailWord_4415383).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415383).length < 2 ^ (prefixWord ++ tailWord_4415383).sum := by decide
  have hdescent : baseEnd_4415383 < baseStart_4415383 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415423 : List Nat := [1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 5]
def baseStart_4415423 : Nat := 118140960795 + 4415423 * 2 ^ 59
def prefixEnd_4415423 : Nat := 4983230072969 + 3 ^ 40 * 4415423 * 2
def baseEnd_4415423 : Nat := 2267234291917183370906345

theorem tailTrace_4415423 : CollatzResearch.WordTrace tailWord_4415423 prefixEnd_4415423 2267234291917183370906345 := by
  unfold tailWord_4415423
  simp only [CollatzResearch.WordTrace]
  refine ⟨161043707082684040057002923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107362471388456026704668615 161043707082684040057002923)
  ·
    refine ⟨241565560624026060085504385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161043707082684040057002923 241565560624026060085504385)
    ·
      refine ⟨181174170468019545064128289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241565560624026060085504385 181174170468019545064128289)
      ·
        refine ⟨135880627851014658798096217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181174170468019545064128289 135880627851014658798096217)
        ·
          refine ⟨101910470888260994098572163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135880627851014658798096217 101910470888260994098572163)
          ·
            refine ⟨152865706332391491147858245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101910470888260994098572163 152865706332391491147858245)
            ·
              refine ⟨28662319937323404590223421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152865706332391491147858245 28662319937323404590223421)
              ·
                refine ⟨10748369976496276721333783, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28662319937323404590223421 10748369976496276721333783)
                ·
                  refine ⟨16122554964744415082000675, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10748369976496276721333783 16122554964744415082000675)
                  ·
                    refine ⟨24183832447116622623001013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16122554964744415082000675 24183832447116622623001013)
                    ·
                      refine ⟨2267234291917183370906345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24183832447116622623001013 2267234291917183370906345)
                      ·
                        rfl

theorem cell23_4415423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 3, 1, 1, 5].length) (baseStart_4415423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415423 prefixEnd_4415423 := by exact prefixLift 4415423
  have htrace : WordTrace (prefixWord ++ tailWord_4415423) baseStart_4415423 baseEnd_4415423 := by
    simpa [prefixWord, tailWord_4415423, baseEnd_4415423] using wordTrace_append hprefix tailTrace_4415423
  have hstable : (prefixWord ++ tailWord_4415423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415423).length < 2 ^ (prefixWord ++ tailWord_4415423).sum := by decide
  have hdescent : baseEnd_4415423 < baseStart_4415423 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415447 : List Nat := [1, 1, 3, 2, 1, 1, 7, 1, 2, 4]
def baseStart_4415447 : Nat := 118140960795 + 4415447 * 2 ^ 59
def prefixEnd_4415447 : Nat := 4983230072969 + 3 ^ 40 * 4415447 * 2
def baseEnd_4415447 : Nat := 755748871817630425668745

theorem tailTrace_4415447 : CollatzResearch.WordTrace tailWord_4415447 prefixEnd_4415447 755748871817630425668745 := by
  unfold tailWord_4415447
  simp only [CollatzResearch.WordTrace]
  refine ⟨161044582434597092155876595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107363054956398061437251063 161044582434597092155876595)
  ·
    refine ⟨241566873651895638233814893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161044582434597092155876595 241566873651895638233814893)
    ·
      refine ⟨90587577619460864337680585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241566873651895638233814893 90587577619460864337680585)
      ·
        refine ⟨67940683214595648253260439, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90587577619460864337680585 67940683214595648253260439)
        ·
          refine ⟨101911024821893472379890659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67940683214595648253260439 101911024821893472379890659)
          ·
            refine ⟨152866537232840208569835989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101911024821893472379890659 152866537232840208569835989)
            ·
              refine ⟨3582809466394692388355531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 152866537232840208569835989 3582809466394692388355531)
              ·
                refine ⟨5374214199592038582533297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582809466394692388355531 5374214199592038582533297)
                ·
                  refine ⟨4030660649694028936899973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5374214199592038582533297 4030660649694028936899973)
                  ·
                    refine ⟨755748871817630425668745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030660649694028936899973 755748871817630425668745)
                    ·
                      rfl

theorem cell23_4415447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 7, 1, 2, 4].length) (baseStart_4415447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415447 prefixEnd_4415447 := by exact prefixLift 4415447
  have htrace : WordTrace (prefixWord ++ tailWord_4415447) baseStart_4415447 baseEnd_4415447 := by
    simpa [prefixWord, tailWord_4415447, baseEnd_4415447] using wordTrace_append hprefix tailTrace_4415447
  have hstable : (prefixWord ++ tailWord_4415447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415447).length < 2 ^ (prefixWord ++ tailWord_4415447).sum := by decide
  have hdescent : baseEnd_4415447 < baseStart_4415447 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415450 : List Nat := [3, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6]
def baseStart_4415450 : Nat := 118140960795 + 4415450 * 2 ^ 59
def prefixEnd_4415450 : Nat := 4983230072969 + 3 ^ 40 * 4415450 * 2
def baseEnd_4415450 : Nat := 2267248155894854765268721

theorem tailTrace_4415450 : CollatzResearch.WordTrace tailWord_4415450 prefixEnd_4415450 2267248155894854765268721 := by
  unfold tailWord_4415450
  simp only [CollatzResearch.WordTrace]
  refine ⟨40261172963396555917058951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107363127902390815778823869 40261172963396555917058951)
  ·
    refine ⟨60391759445094833875588427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40261172963396555917058951 60391759445094833875588427)
    ·
      refine ⟨90587639167642250813382641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60391759445094833875588427 90587639167642250813382641)
      ·
        refine ⟨67940729375731688110036981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90587639167642250813382641 67940729375731688110036981)
        ·
          refine ⟨6369443378974845760315967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 67940729375731688110036981 6369443378974845760315967)
          ·
            refine ⟨9554165068462268640473951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6369443378974845760315967 9554165068462268640473951)
            ·
              refine ⟨14331247602693402960710927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9554165068462268640473951 14331247602693402960710927)
              ·
                refine ⟨21496871404040104441066391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14331247602693402960710927 21496871404040104441066391)
                ·
                  refine ⟨32245307106060156661599587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21496871404040104441066391 32245307106060156661599587)
                  ·
                    refine ⟨48367960659090234992399381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32245307106060156661599587 48367960659090234992399381)
                    ·
                      refine ⟨2267248155894854765268721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48367960659090234992399381 2267248155894854765268721)
                      ·
                        rfl

theorem cell23_4415450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 1, 1, 1, 6].length) (baseStart_4415450 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415450 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415450 prefixEnd_4415450 := by exact prefixLift 4415450
  have htrace : WordTrace (prefixWord ++ tailWord_4415450) baseStart_4415450 baseEnd_4415450 := by
    simpa [prefixWord, tailWord_4415450, baseEnd_4415450] using wordTrace_append hprefix tailTrace_4415450
  have hstable : (prefixWord ++ tailWord_4415450).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415450).length < 2 ^ (prefixWord ++ tailWord_4415450).sum := by decide
  have hdescent : baseEnd_4415450 < baseStart_4415450 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415508 : List Nat := [2, 4, 3, 2, 1, 2, 1, 2, 1, 2, 3]
def baseStart_4415508 : Nat := 118140960795 + 4415508 * 2 ^ 59
def prefixEnd_4415508 : Nat := 4983230072969 + 3 ^ 40 * 4415508 * 2
def baseEnd_4415508 : Nat := 2267277937772815538343455

theorem tailTrace_4415508 : CollatzResearch.WordTrace tailWord_4415508 prefixEnd_4415508 2267277937772815538343455 := by
  unfold tailWord_4415508
  simp only [CollatzResearch.WordTrace]
  refine ⟨80523403643688049786923589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107364538191584066382564785 80523403643688049786923589)
  ·
    refine ⟨15098138183191509335048173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 80523403643688049786923589 15098138183191509335048173)
    ·
      refine ⟨5661801818696816000643065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 15098138183191509335048173 5661801818696816000643065)
      ·
        refine ⟨4246351364022612000482299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5661801818696816000643065 4246351364022612000482299)
        ·
          refine ⟨6369527046033918000723449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246351364022612000482299 6369527046033918000723449)
          ·
            refine ⟨4777145284525438500542587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6369527046033918000723449 4777145284525438500542587)
            ·
              refine ⟨7165717926788157750813881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777145284525438500542587 7165717926788157750813881)
              ·
                refine ⟨5374288445091118313110411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7165717926788157750813881 5374288445091118313110411)
                ·
                  refine ⟨8061432667636677469665617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374288445091118313110411 8061432667636677469665617)
                  ·
                    refine ⟨6046074500727508102249213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8061432667636677469665617 6046074500727508102249213)
                    ·
                      refine ⟨2267277937772815538343455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6046074500727508102249213 2267277937772815538343455)
                      ·
                        rfl

theorem cell23_4415508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 1, 2, 1, 2, 3].length) (baseStart_4415508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415508 prefixEnd_4415508 := by exact prefixLift 4415508
  have htrace : WordTrace (prefixWord ++ tailWord_4415508) baseStart_4415508 baseEnd_4415508 := by
    simpa [prefixWord, tailWord_4415508, baseEnd_4415508] using wordTrace_append hprefix tailTrace_4415508
  have hstable : (prefixWord ++ tailWord_4415508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415508).length < 2 ^ (prefixWord ++ tailWord_4415508).sum := by decide
  have hdescent : baseEnd_4415508 < baseStart_4415508 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415514 : List Nat := [3, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2]
def baseStart_4415514 : Nat := 118140960795 + 4415514 * 2 ^ 59
def prefixEnd_4415514 : Nat := 4983230072969 + 3 ^ 40 * 4415514 * 2
def baseEnd_4415514 : Nat := 2267281018656742514868427

theorem tailTrace_4415514 : CollatzResearch.WordTrace tailWord_4415514 prefixEnd_4415514 2267281018656742514868427 := by
  unfold tailWord_4415514
  simp only [CollatzResearch.WordTrace]
  refine ⟨40261756531338590649641399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107364684083569575065710397 40261756531338590649641399)
  ·
    refine ⟨60392634797007885974462099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40261756531338590649641399 60392634797007885974462099)
    ·
      refine ⟨90588952195511828961693149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60392634797007885974462099 90588952195511828961693149)
      ·
        refine ⟨33970857073316935860634931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90588952195511828961693149 33970857073316935860634931)
        ·
          refine ⟨50956285609975403790952397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33970857073316935860634931 50956285609975403790952397)
          ·
            refine ⟨19108607103740776421607149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50956285609975403790952397 19108607103740776421607149)
            ·
              refine ⟨7165727663902791158102681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19108607103740776421607149 7165727663902791158102681)
              ·
                refine ⟨5374295747927093368577011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7165727663902791158102681 5374295747927093368577011)
                ·
                  refine ⟨8061443621890640052865517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374295747927093368577011 8061443621890640052865517)
                  ·
                    refine ⟨3023041358208990019824569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8061443621890640052865517 3023041358208990019824569)
                    ·
                      refine ⟨2267281018656742514868427, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023041358208990019824569 2267281018656742514868427)
                      ·
                        rfl

theorem cell23_4415514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 3, 2, 1, 3, 2].length) (baseStart_4415514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415514 prefixEnd_4415514 := by exact prefixLift 4415514
  have htrace : WordTrace (prefixWord ++ tailWord_4415514) baseStart_4415514 baseEnd_4415514 := by
    simpa [prefixWord, tailWord_4415514, baseEnd_4415514] using wordTrace_append hprefix tailTrace_4415514
  have hstable : (prefixWord ++ tailWord_4415514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415514).length < 2 ^ (prefixWord ++ tailWord_4415514).sum := by decide
  have hdescent : baseEnd_4415514 < baseStart_4415514 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415543 : List Nat := [1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 7]
def baseStart_4415543 : Nat := 118140960795 + 4415543 * 2 ^ 59
def prefixEnd_4415543 : Nat := 4983230072969 + 3 ^ 40 * 4415543 * 2
def baseEnd_4415543 : Nat := 2267295909595722901405793

theorem tailTrace_4415543 : CollatzResearch.WordTrace tailWord_4415543 prefixEnd_4415543 2267295909595722901405793 := by
  unfold tailWord_4415543
  simp only [CollatzResearch.WordTrace]
  refine ⟨161048083842249300551371283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107365389228166200367580855 161048083842249300551371283)
  ·
    refine ⟨241572125763373950827056925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161048083842249300551371283 241572125763373950827056925)
    ·
      refine ⟨90589547161265231560146347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241572125763373950827056925 90589547161265231560146347)
      ·
        refine ⟨135884320741897847340219521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90589547161265231560146347 135884320741897847340219521)
        ·
          refine ⟨101913240556423385505164641, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135884320741897847340219521 101913240556423385505164641)
          ·
            refine ⟨76434930417317539128873481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101913240556423385505164641 76434930417317539128873481)
            ·
              refine ⟨57326197812988154346655111, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76434930417317539128873481 57326197812988154346655111)
              ·
                refine ⟨85989296719482231519982667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57326197812988154346655111 85989296719482231519982667)
                ·
                  refine ⟨128983945079223347279974001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85989296719482231519982667 128983945079223347279974001)
                  ·
                    refine ⟨96737958809417510459980501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 128983945079223347279974001 96737958809417510459980501)
                    ·
                      refine ⟨2267295909595722901405793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 96737958809417510459980501 2267295909595722901405793)
                      ·
                        rfl

theorem cell23_4415543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 2, 1, 1, 2, 7].length) (baseStart_4415543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415543 prefixEnd_4415543 := by exact prefixLift 4415543
  have htrace : WordTrace (prefixWord ++ tailWord_4415543) baseStart_4415543 baseEnd_4415543 := by
    simpa [prefixWord, tailWord_4415543, baseEnd_4415543] using wordTrace_append hprefix tailTrace_4415543
  have hstable : (prefixWord ++ tailWord_4415543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415543).length < 2 ^ (prefixWord ++ tailWord_4415543).sum := by decide
  have hdescent : baseEnd_4415543 < baseStart_4415543 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415563 : List Nat := [1, 1, 1, 1, 3, 1, 2, 3, 3, 7]
def baseStart_4415563 : Nat := 118140960795 + 4415563 * 2 ^ 59
def prefixEnd_4415563 : Nat := 4983230072969 + 3 ^ 40 * 4415563 * 2
def baseEnd_4415563 : Nat := 755768726402937607718567

theorem tailTrace_4415563 : CollatzResearch.WordTrace tailWord_4415563 prefixEnd_4415563 755768726402937607718567 := by
  unfold tailWord_4415563
  simp only [CollatzResearch.WordTrace]
  refine ⟨161048813302176843967099343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107365875534784562644732895 161048813302176843967099343)
  ·
    refine ⟨241573219953265265950649015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161048813302176843967099343 241573219953265265950649015)
    ·
      refine ⟨362359829929897898925973523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241573219953265265950649015 362359829929897898925973523)
      ·
        refine ⟨543539744894846848388960285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362359829929897898925973523 543539744894846848388960285)
        ·
          refine ⟨203827404335567568145860107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 543539744894846848388960285 203827404335567568145860107)
          ·
            refine ⟨305741106503351352218790161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203827404335567568145860107 305741106503351352218790161)
            ·
              refine ⟨229305829877513514164092621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305741106503351352218790161 229305829877513514164092621)
              ·
                refine ⟨85989686204067567811534733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 229305829877513514164092621 85989686204067567811534733)
                ·
                  refine ⟨32246132326525337929325525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 85989686204067567811534733 32246132326525337929325525)
                  ·
                    refine ⟨755768726402937607718567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32246132326525337929325525 755768726402937607718567)
                    ·
                      rfl

theorem cell23_4415563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 2, 3, 3, 7].length) (baseStart_4415563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415563 prefixEnd_4415563 := by exact prefixLift 4415563
  have htrace : WordTrace (prefixWord ++ tailWord_4415563) baseStart_4415563 baseEnd_4415563 := by
    simpa [prefixWord, tailWord_4415563, baseEnd_4415563] using wordTrace_append hprefix tailTrace_4415563
  have hstable : (prefixWord ++ tailWord_4415563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415563).length < 2 ^ (prefixWord ++ tailWord_4415563).sum := by decide
  have hdescent : baseEnd_4415563 < baseStart_4415563 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415582 : List Nat := [4, 4, 1, 1, 2, 2, 2, 1, 1, 3, 2]
def baseStart_4415582 : Nat := 118140960795 + 4415582 * 2 ^ 59
def prefixEnd_4415582 : Nat := 4983230072969 + 3 ^ 40 * 4415582 * 2
def baseEnd_4415582 : Nat := 2267315935341248248818115

theorem tailTrace_4415582 : CollatzResearch.WordTrace tailWord_4415582 prefixEnd_4415582 2267315935341248248818115 := by
  unfold tailWord_4415582
  simp only [CollatzResearch.WordTrace]
  refine ⟨20131188286138501276505125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107366337526072006808027333 20131188286138501276505125)
  ·
    refine ⟨3774597803650968989344711, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 20131188286138501276505125 3774597803650968989344711)
    ·
      refine ⟨5661896705476453484017067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 3774597803650968989344711 5661896705476453484017067)
      ·
        refine ⟨8492845058214680226025601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 5661896705476453484017067 8492845058214680226025601)
        ·
          refine ⟨6369633793661010169519201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 8492845058214680226025601 6369633793661010169519201)
          ·
            refine ⟨4777225345245757627139401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6369633793661010169519201 4777225345245757627139401)
            ·
              refine ⟨3582919008934318220354551, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4777225345245757627139401 3582919008934318220354551)
              ·
                refine ⟨5374378513401477330531827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3582919008934318220354551 5374378513401477330531827)
                ·
                  refine ⟨8061567770102215995797741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374378513401477330531827 8061567770102215995797741)
                  ·
                    refine ⟨3023087913788330998424153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8061567770102215995797741 3023087913788330998424153)
                    ·
                      refine ⟨2267315935341248248818115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023087913788330998424153 2267315935341248248818115)
                      ·
                        rfl

theorem cell23_4415582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 2, 2, 2, 1, 1, 3, 2].length) (baseStart_4415582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415582 prefixEnd_4415582 := by exact prefixLift 4415582
  have htrace : WordTrace (prefixWord ++ tailWord_4415582) baseStart_4415582 baseEnd_4415582 := by
    simpa [prefixWord, tailWord_4415582, baseEnd_4415582] using wordTrace_append hprefix tailTrace_4415582
  have hstable : (prefixWord ++ tailWord_4415582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415582).length < 2 ^ (prefixWord ++ tailWord_4415582).sum := by decide
  have hdescent : baseEnd_4415582 < baseStart_4415582 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415637 : List Nat := [1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 3]
def baseStart_4415637 : Nat := 118140960795 + 4415637 * 2 ^ 59
def prefixEnd_4415637 : Nat := 4983230072969 + 3 ^ 40 * 4415637 * 2
def baseEnd_4415637 : Nat := 2267344176777245533630361

theorem tailTrace_4415637 : CollatzResearch.WordTrace tailWord_4415637 prefixEnd_4415637 2267344176777245533630361 := by
  unfold tailWord_4415637
  simp only [CollatzResearch.WordTrace]
  refine ⟨161051512303908754605293165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107367674869272503070195443 161051512303908754605293165)
  ·
    refine ⟨60394317113965782976984937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161051512303908754605293165 60394317113965782976984937)
    ·
      refine ⟨45295737835474337232738703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60394317113965782976984937 45295737835474337232738703)
      ·
        refine ⟨67943606753211505849108055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45295737835474337232738703 67943606753211505849108055)
        ·
          refine ⟨101915410129817258773662083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67943606753211505849108055 101915410129817258773662083)
          ·
            refine ⟨152873115194725888160493125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101915410129817258773662083 152873115194725888160493125)
            ·
              refine ⟨28663709099011104030092461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152873115194725888160493125 28663709099011104030092461)
              ·
                refine ⟨10748890912129164011284673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28663709099011104030092461 10748890912129164011284673)
                ·
                  refine ⟨8061668184096873008463505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10748890912129164011284673 8061668184096873008463505)
                  ·
                    refine ⟨6046251138072654756347629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8061668184096873008463505 6046251138072654756347629)
                    ·
                      refine ⟨2267344176777245533630361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6046251138072654756347629 2267344176777245533630361)
                      ·
                        rfl

theorem cell23_4415637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 4, 3, 2, 2, 3].length) (baseStart_4415637 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415637 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415637 prefixEnd_4415637 := by exact prefixLift 4415637
  have htrace : WordTrace (prefixWord ++ tailWord_4415637) baseStart_4415637 baseEnd_4415637 := by
    simpa [prefixWord, tailWord_4415637, baseEnd_4415637] using wordTrace_append hprefix tailTrace_4415637
  have hstable : (prefixWord ++ tailWord_4415637).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415637).length < 2 ^ (prefixWord ++ tailWord_4415637).sum := by decide
  have hdescent : baseEnd_4415637 < baseStart_4415637 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415661 : List Nat := [1, 5, 2, 1, 2, 3, 1, 1, 3, 4]
def baseStart_4415661 : Nat := 118140960795 + 4415661 * 2 ^ 59
def prefixEnd_4415661 : Nat := 4983230072969 + 3 ^ 40 * 4415661 * 2
def baseEnd_4415661 : Nat := 755785500104317813243417

theorem tailTrace_4415661 : CollatzResearch.WordTrace tailWord_4415661 prefixEnd_4415661 755785500104317813243417 := by
  unfold tailWord_4415661
  simp only [CollatzResearch.WordTrace]
  refine ⟨161052387655821806704166837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107368258437214537802777891 161052387655821806704166837)
  ·
    refine ⟨15098661342733294378515641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161052387655821806704166837 15098661342733294378515641)
    ·
      refine ⟨11323996007049970783886731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15098661342733294378515641 11323996007049970783886731)
      ·
        refine ⟨16985994010574956175830097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11323996007049970783886731 16985994010574956175830097)
        ·
          refine ⟨12739495507931217131872573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16985994010574956175830097 12739495507931217131872573)
          ·
            refine ⟨4777310815474206424452215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 12739495507931217131872573 4777310815474206424452215)
            ·
              refine ⟨7165966223211309636678323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777310815474206424452215 7165966223211309636678323)
              ·
                refine ⟨10748949334816964455017485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7165966223211309636678323 10748949334816964455017485)
                ·
                  refine ⟨4030856000556361670631557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10748949334816964455017485 4030856000556361670631557)
                  ·
                    refine ⟨755785500104317813243417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4030856000556361670631557 755785500104317813243417)
                    ·
                      rfl

theorem cell23_4415661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 3, 1, 1, 3, 4].length) (baseStart_4415661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415661 prefixEnd_4415661 := by exact prefixLift 4415661
  have htrace : WordTrace (prefixWord ++ tailWord_4415661) baseStart_4415661 baseEnd_4415661 := by
    simpa [prefixWord, tailWord_4415661, baseEnd_4415661] using wordTrace_append hprefix tailTrace_4415661
  have hstable : (prefixWord ++ tailWord_4415661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415661).length < 2 ^ (prefixWord ++ tailWord_4415661).sum := by decide
  have hdescent : baseEnd_4415661 < baseStart_4415661 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415747 : List Nat := [1, 1, 1, 3, 2, 3, 5, 7]
def baseStart_4415747 : Nat := 118140960795 + 4415747 * 2 ^ 59
def prefixEnd_4415747 : Nat := 4983230072969 + 3 ^ 40 * 4415747 * 2
def baseEnd_4415747 : Nat := 83977802209231114935365

theorem tailTrace_4415747 : CollatzResearch.WordTrace tailWord_4415747 prefixEnd_4415747 83977802209231114935365 := by
  unfold tailWord_4415747
  simp only [CollatzResearch.WordTrace]
  refine ⟨161055524333510243391797495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107370349555673495594531663 161055524333510243391797495)
  ·
    refine ⟨241583286500265365087696243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161055524333510243391797495 241583286500265365087696243)
    ·
      refine ⟨362374929750398047631544365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241583286500265365087696243 362374929750398047631544365)
      ·
        refine ⟨135890598656399267861829137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362374929750398047631544365 135890598656399267861829137)
        ·
          refine ⟨101917948992299450896371853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135890598656399267861829137 101917948992299450896371853)
          ·
            refine ⟨38219230872112294086139445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101917948992299450896371853 38219230872112294086139445)
            ·
              refine ⟨3583052894260527570575573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38219230872112294086139445 3583052894260527570575573)
              ·
                refine ⟨83977802209231114935365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 3583052894260527570575573 83977802209231114935365)
                ·
                  rfl

theorem cell23_4415747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 7].length) (baseStart_4415747 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415747 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415747 prefixEnd_4415747 := by exact prefixLift 4415747
  have htrace : WordTrace (prefixWord ++ tailWord_4415747) baseStart_4415747 baseEnd_4415747 := by
    simpa [prefixWord, tailWord_4415747, baseEnd_4415747] using wordTrace_append hprefix tailTrace_4415747
  have hstable : (prefixWord ++ tailWord_4415747).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415747).length < 2 ^ (prefixWord ++ tailWord_4415747).sum := by decide
  have hdescent : baseEnd_4415747 < baseStart_4415747 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415761 : List Nat := [1, 2, 2, 1, 1, 5, 4, 1, 1, 2, 3]
def baseStart_4415761 : Nat := 118140960795 + 4415761 * 2 ^ 59
def prefixEnd_4415761 : Nat := 4983230072969 + 3 ^ 40 * 4415761 * 2
def baseEnd_4415761 : Nat := 2267407848378403048479791

theorem tailTrace_4415761 : CollatzResearch.WordTrace tailWord_4415761 prefixEnd_4415761 2267407848378403048479791 := by
  unfold tailWord_4415761
  simp only [CollatzResearch.WordTrace]
  refine ⟨161056034955459523782807137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107370689970306349188538091 161056034955459523782807137)
  ·
    refine ⟨120792026216594642837105353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161056034955459523782807137 120792026216594642837105353)
    ·
      refine ⟨90594019662445982127829015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120792026216594642837105353 90594019662445982127829015)
      ·
        refine ⟨135891029493668973191743523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90594019662445982127829015 135891029493668973191743523)
        ·
          refine ⟨203836544240503459787615285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135891029493668973191743523 203836544240503459787615285)
          ·
            refine ⟨19109676022547199355088933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 203836544240503459787615285 19109676022547199355088933)
            ·
              refine ⟨3583064254227599879079175, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 19109676022547199355088933 3583064254227599879079175)
              ·
                refine ⟨5374596381341399818618763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583064254227599879079175 5374596381341399818618763)
                ·
                  refine ⟨8061894572012099727928145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374596381341399818618763 8061894572012099727928145)
                  ·
                    refine ⟨6046420929009074795946109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8061894572012099727928145 6046420929009074795946109)
                    ·
                      refine ⟨2267407848378403048479791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6046420929009074795946109 2267407848378403048479791)
                      ·
                        rfl

theorem cell23_4415761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 4, 1, 1, 2, 3].length) (baseStart_4415761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415761 prefixEnd_4415761 := by exact prefixLift 4415761
  have htrace : WordTrace (prefixWord ++ tailWord_4415761) baseStart_4415761 baseEnd_4415761 := by
    simpa [prefixWord, tailWord_4415761, baseEnd_4415761] using wordTrace_append hprefix tailTrace_4415761
  have hstable : (prefixWord ++ tailWord_4415761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415761).length < 2 ^ (prefixWord ++ tailWord_4415761).sum := by decide
  have hdescent : baseEnd_4415761 < baseStart_4415761 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415809 : List Nat := [1, 2, 5, 2, 3, 1, 1, 3, 1, 2, 2]
def baseStart_4415809 : Nat := 118140960795 + 4415809 * 2 ^ 59
def prefixEnd_4415809 : Nat := 4983230072969 + 3 ^ 40 * 4415809 * 2
def baseEnd_4415809 : Nat := 2267432495449818860679571

theorem tailTrace_4415809 : CollatzResearch.WordTrace tailWord_4415809 prefixEnd_4415809 2267432495449818860679571 := by
  unfold tailWord_4415809
  simp only [CollatzResearch.WordTrace]
  refine ⟨161057785659285627980554481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107371857106190418653702987 161057785659285627980554481)
  ·
    refine ⟨120793339244464220985415861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161057785659285627980554481 120793339244464220985415861)
    ·
      refine ⟨11324375554168520717382737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 120793339244464220985415861 11324375554168520717382737)
      ·
        refine ⟨8493281665626390538037053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11324375554168520717382737 8493281665626390538037053)
        ·
          refine ⟨3184980624609896451763895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8493281665626390538037053 3184980624609896451763895)
          ·
            refine ⟨4777470936914844677645843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3184980624609896451763895 4777470936914844677645843)
            ·
              refine ⟨7166206405372267016468765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777470936914844677645843 7166206405372267016468765)
              ·
                refine ⟨2687327402014600131175787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7166206405372267016468765 2687327402014600131175787)
                ·
                  refine ⟨4030991103021900196763681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2687327402014600131175787 4030991103021900196763681)
                  ·
                    refine ⟨3023243327266425147572761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4030991103021900196763681 3023243327266425147572761)
                    ·
                      refine ⟨2267432495449818860679571, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023243327266425147572761 2267432495449818860679571)
                      ·
                        rfl

theorem cell23_4415809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 1, 3, 1, 2, 2].length) (baseStart_4415809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415809 prefixEnd_4415809 := by exact prefixLift 4415809
  have htrace : WordTrace (prefixWord ++ tailWord_4415809) baseStart_4415809 baseEnd_4415809 := by
    simpa [prefixWord, tailWord_4415809, baseEnd_4415809] using wordTrace_append hprefix tailTrace_4415809
  have hstable : (prefixWord ++ tailWord_4415809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415809).length < 2 ^ (prefixWord ++ tailWord_4415809).sum := by decide
  have hdescent : baseEnd_4415809 < baseStart_4415809 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415817 : List Nat := [1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 3]
def baseStart_4415817 : Nat := 118140960795 + 4415817 * 2 ^ 59
def prefixEnd_4415817 : Nat := 4983230072969 + 3 ^ 40 * 4415817 * 2
def baseEnd_4415817 : Nat := 2267436603295054829379533

theorem tailTrace_4415817 : CollatzResearch.WordTrace tailWord_4415817 prefixEnd_4415817 2267436603295054829379533 := by
  unfold tailWord_4415817
  simp only [CollatzResearch.WordTrace]
  refine ⟨161058077443256645346845705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107372051628837763564563803 161058077443256645346845705)
  ·
    refine ⟨120793558082442484010134279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161058077443256645346845705 120793558082442484010134279)
    ·
      refine ⟨181190337123663726015201419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120793558082442484010134279 181190337123663726015201419)
      ·
        refine ⟨271785505685495589022802129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181190337123663726015201419 271785505685495589022802129)
        ·
          refine ⟨203839129264121691767101597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271785505685495589022802129 203839129264121691767101597)
          ·
            refine ⟨76439673474045634412663099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203839129264121691767101597 76439673474045634412663099)
            ·
              refine ⟨114659510211068451618994649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76439673474045634412663099 114659510211068451618994649)
              ·
                refine ⟨85994632658301338714245987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 114659510211068451618994649 85994632658301338714245987)
                ·
                  refine ⟨128991948987452008071368981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 85994632658301338714245987 128991948987452008071368981)
                  ·
                    refine ⟨6046497608786812878345421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 128991948987452008071368981 6046497608786812878345421)
                    ·
                      refine ⟨2267436603295054829379533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6046497608786812878345421 2267436603295054829379533)
                      ·
                        rfl

theorem cell23_4415817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 1, 2, 1, 6, 3].length) (baseStart_4415817 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415817 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415817 prefixEnd_4415817 := by exact prefixLift 4415817
  have htrace : WordTrace (prefixWord ++ tailWord_4415817) baseStart_4415817 baseEnd_4415817 := by
    simpa [prefixWord, tailWord_4415817, baseEnd_4415817] using wordTrace_append hprefix tailTrace_4415817
  have hstable : (prefixWord ++ tailWord_4415817).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415817).length < 2 ^ (prefixWord ++ tailWord_4415817).sum := by decide
  have hdescent : baseEnd_4415817 < baseStart_4415817 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415827 : List Nat := [1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4]
def baseStart_4415827 : Nat := 118140960795 + 4415827 * 2 ^ 59
def prefixEnd_4415827 : Nat := 4983230072969 + 3 ^ 40 * 4415827 * 2
def baseEnd_4415827 : Nat := 2267441738101599790254487

theorem tailTrace_4415827 : CollatzResearch.WordTrace tailWord_4415827 prefixEnd_4415827 2267441738101599790254487 := by
  unfold tailWord_4415827
  simp only [CollatzResearch.WordTrace]
  refine ⟨161058442173220417054709735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107372294782146944703139823 161058442173220417054709735)
  ·
    refine ⟨241587663259830625582064603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161058442173220417054709735 241587663259830625582064603)
    ·
      refine ⟨362381494889745938373096905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241587663259830625582064603 362381494889745938373096905)
      ·
        refine ⟨271786121167309453779822679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362381494889745938373096905 271786121167309453779822679)
        ·
          refine ⟨407679181750964180669734019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271786121167309453779822679 407679181750964180669734019)
          ·
            refine ⟨611518772626446271004601029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407679181750964180669734019 611518772626446271004601029)
            ·
              refine ⟨114659769867458675813362693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 611518772626446271004601029 114659769867458675813362693)
              ·
                refine ⟨21498706850148501715005505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114659769867458675813362693 21498706850148501715005505)
                ·
                  refine ⟨16124030137611376286254129, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21498706850148501715005505 16124030137611376286254129)
                  ·
                    refine ⟨12093022603208532214690597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16124030137611376286254129 12093022603208532214690597)
                    ·
                      refine ⟨2267441738101599790254487, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12093022603208532214690597 2267441738101599790254487)
                      ·
                        rfl

theorem cell23_4415827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 4, 4, 2, 2, 4].length) (baseStart_4415827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415827 prefixEnd_4415827 := by exact prefixLift 4415827
  have htrace : WordTrace (prefixWord ++ tailWord_4415827) baseStart_4415827 baseEnd_4415827 := by
    simpa [prefixWord, tailWord_4415827, baseEnd_4415827] using wordTrace_append hprefix tailTrace_4415827
  have hstable : (prefixWord ++ tailWord_4415827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415827).length < 2 ^ (prefixWord ++ tailWord_4415827).sum := by decide
  have hdescent : baseEnd_4415827 < baseStart_4415827 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415831 : List Nat := [1, 1, 3, 2, 3, 1, 1, 3, 4, 2, 2]
def baseStart_4415831 : Nat := 118140960795 + 4415831 * 2 ^ 59
def prefixEnd_4415831 : Nat := 4983230072969 + 3 ^ 40 * 4415831 * 2
def baseEnd_4415831 : Nat := 2267443792024217774604469

theorem tailTrace_4415831 : CollatzResearch.WordTrace tailWord_4415831 prefixEnd_4415831 2267443792024217774604469 := by
  unfold tailWord_4415831
  simp only [CollatzResearch.WordTrace]
  refine ⟨161058588065205925737855347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107372392043470617158570231 161058588065205925737855347)
  ·
    refine ⟨241587882097808888606783021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161058588065205925737855347 241587882097808888606783021)
    ·
      refine ⟨90595455786678333227543633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241587882097808888606783021 90595455786678333227543633)
      ·
        refine ⟨67946591840008749920657725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90595455786678333227543633 67946591840008749920657725)
        ·
          refine ⟨25479971940003281220246647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67946591840008749920657725 25479971940003281220246647)
          ·
            refine ⟨38219957910004921830369971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25479971940003281220246647 38219957910004921830369971)
            ·
              refine ⟨57329936865007382745554957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38219957910004921830369971 57329936865007382745554957)
              ·
                refine ⟨21498726324377768529583109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57329936865007382745554957 21498726324377768529583109)
                ·
                  refine ⟨4031011185820831599296833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21498726324377768529583109 4031011185820831599296833)
                  ·
                    refine ⟨3023258389365623699472625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4031011185820831599296833 3023258389365623699472625)
                    ·
                      refine ⟨2267443792024217774604469, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023258389365623699472625 2267443792024217774604469)
                      ·
                        rfl

theorem cell23_4415831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 3, 4, 2, 2].length) (baseStart_4415831 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415831 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415831 prefixEnd_4415831 := by exact prefixLift 4415831
  have htrace : WordTrace (prefixWord ++ tailWord_4415831) baseStart_4415831 baseEnd_4415831 := by
    simpa [prefixWord, tailWord_4415831, baseEnd_4415831] using wordTrace_append hprefix tailTrace_4415831
  have hstable : (prefixWord ++ tailWord_4415831).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415831).length < 2 ^ (prefixWord ++ tailWord_4415831).sum := by decide
  have hdescent : baseEnd_4415831 < baseStart_4415831 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415882 : List Nat := [3, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2]
def baseStart_4415882 : Nat := 118140960795 + 4415882 * 2 ^ 59
def prefixEnd_4415882 : Nat := 4983230072969 + 3 ^ 40 * 4415882 * 2
def baseEnd_4415882 : Nat := 2267469979537597075066735

theorem tailTrace_4415882 : CollatzResearch.WordTrace tailWord_4415882 prefixEnd_4415882 2267469979537597075066735 := by
  unfold tailWord_4415882
  simp only [CollatzResearch.WordTrace]
  refine ⟨40265112047005290361990475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107373632125347440965307933 40265112047005290361990475)
  ·
    refine ⟨60397668070507935542985713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40265112047005290361990475 60397668070507935542985713)
    ·
      refine ⟨45298251052880951657239285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60397668070507935542985713 45298251052880951657239285)
      ·
        refine ⟨4246711036207589217866183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 45298251052880951657239285 4246711036207589217866183)
        ·
          refine ⟨6370066554311383826799275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4246711036207589217866183 6370066554311383826799275)
          ·
            refine ⟨9555099831467075740198913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6370066554311383826799275 9555099831467075740198913)
            ·
              refine ⟨7166324873600306805149185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9555099831467075740198913 7166324873600306805149185)
              ·
                refine ⟨5374743655200230103861889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7166324873600306805149185 5374743655200230103861889)
                ·
                  refine ⟨4031057741400172577896417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5374743655200230103861889 4031057741400172577896417)
                  ·
                    refine ⟨3023293306050129433422313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4031057741400172577896417 3023293306050129433422313)
                    ·
                      refine ⟨2267469979537597075066735, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023293306050129433422313 2267469979537597075066735)
                      ·
                        rfl

theorem cell23_4415882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 2, 2, 2, 2, 2].length) (baseStart_4415882 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415882 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415882 prefixEnd_4415882 := by exact prefixLift 4415882
  have htrace : WordTrace (prefixWord ++ tailWord_4415882) baseStart_4415882 baseEnd_4415882 := by
    simpa [prefixWord, tailWord_4415882, baseEnd_4415882] using wordTrace_append hprefix tailTrace_4415882
  have hstable : (prefixWord ++ tailWord_4415882).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415882).length < 2 ^ (prefixWord ++ tailWord_4415882).sum := by decide
  have hdescent : baseEnd_4415882 < baseStart_4415882 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415884 : List Nat := [2, 2, 1, 2, 1, 4, 2, 2, 2, 5]
def baseStart_4415884 : Nat := 118140960795 + 4415884 * 2 ^ 59
def prefixEnd_4415884 : Nat := 4983230072969 + 3 ^ 40 * 4415884 * 2
def baseEnd_4415884 : Nat := 755823668832968689080575

theorem tailTrace_4415884 : CollatzResearch.WordTrace tailWord_4415884 prefixEnd_4415884 755823668832968689080575 := by
  unfold tailWord_4415884
  simp only [CollatzResearch.WordTrace]
  refine ⟨80530260567006957894767353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107373680756009277193023137 80530260567006957894767353)
  ·
    refine ⟨60397695425255218421075515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80530260567006957894767353 60397695425255218421075515)
    ·
      refine ⟨90596543137882827631613273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60397695425255218421075515 90596543137882827631613273)
      ·
        refine ⟨67947407353412120723709955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90596543137882827631613273 67947407353412120723709955)
        ·
          refine ⟨101921111030118181085564933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67947407353412120723709955 101921111030118181085564933)
          ·
            refine ⟨19110208318147158953543425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 101921111030118181085564933 19110208318147158953543425)
            ·
              refine ⟨14332656238610369215157569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19110208318147158953543425 14332656238610369215157569)
              ·
                refine ⟨10749492178957776911368177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14332656238610369215157569 10749492178957776911368177)
                ·
                  refine ⟨8062119134218332683526133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10749492178957776911368177 8062119134218332683526133)
                  ·
                    refine ⟨755823668832968689080575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8062119134218332683526133 755823668832968689080575)
                    ·
                      rfl

theorem cell23_4415884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 2, 2, 2, 5].length) (baseStart_4415884 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415884 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415884 prefixEnd_4415884 := by exact prefixLift 4415884
  have htrace : WordTrace (prefixWord ++ tailWord_4415884) baseStart_4415884 baseEnd_4415884 := by
    simpa [prefixWord, tailWord_4415884, baseEnd_4415884] using wordTrace_append hprefix tailTrace_4415884
  have hstable : (prefixWord ++ tailWord_4415884).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415884).length < 2 ^ (prefixWord ++ tailWord_4415884).sum := by decide
  have hdescent : baseEnd_4415884 < baseStart_4415884 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415921 : List Nat := [1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 4]
def baseStart_4415921 : Nat := 118140960795 + 4415921 * 2 ^ 59
def prefixEnd_4415921 : Nat := 4983230072969 + 3 ^ 40 * 4415921 * 2
def baseEnd_4415921 : Nat := 2267490005283122422479055

theorem tailTrace_4415921 : CollatzResearch.WordTrace tailWord_4415921 prefixEnd_4415921 2267490005283122422479055 := by
  unfold tailWord_4415921
  simp only [CollatzResearch.WordTrace]
  refine ⟨161061870634879871108631617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107374580423253247405754411 161061870634879871108631617)
  ·
    refine ⟨120796402976159903331473713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161061870634879871108631617 120796402976159903331473713)
    ·
      refine ⟨90597302232119927498605285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120796402976159903331473713 90597302232119927498605285)
      ·
        refine ⟨16986994168522486405988491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90597302232119927498605285 16986994168522486405988491)
        ·
          refine ⟨25480491252783729608982737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16986994168522486405988491 25480491252783729608982737)
          ·
            refine ⟨19110368439587797206737053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25480491252783729608982737 19110368439587797206737053)
            ·
              refine ⟨7166388164845423952526395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19110368439587797206737053 7166388164845423952526395)
              ·
                refine ⟨10749582247268135928789593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7166388164845423952526395 10749582247268135928789593)
                ·
                  refine ⟨8062186685451101946592195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10749582247268135928789593 8062186685451101946592195)
                  ·
                    refine ⟨12093280028176652919888293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8062186685451101946592195 12093280028176652919888293)
                    ·
                      refine ⟨2267490005283122422479055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12093280028176652919888293 2267490005283122422479055)
                      ·
                        rfl

theorem cell23_4415921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_4415921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415921 prefixEnd_4415921 := by exact prefixLift 4415921
  have htrace : WordTrace (prefixWord ++ tailWord_4415921) baseStart_4415921 baseEnd_4415921 := by
    simpa [prefixWord, tailWord_4415921, baseEnd_4415921] using wordTrace_append hprefix tailTrace_4415921
  have hstable : (prefixWord ++ tailWord_4415921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415921).length < 2 ^ (prefixWord ++ tailWord_4415921).sum := by decide
  have hdescent : baseEnd_4415921 < baseStart_4415921 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415934 : List Nat := [4, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6]
def baseStart_4415934 : Nat := 118140960795 + 4415934 * 2 ^ 59
def prefixEnd_4415934 : Nat := 4983230072969 + 3 ^ 40 * 4415934 * 2
def baseEnd_4415934 : Nat := 2267496680531630871616495

theorem tailTrace_4415934 : CollatzResearch.WordTrace tailWord_4415934 prefixEnd_4415934 2267496680531630871616495 := by
  unfold tailWord_4415934
  simp only [CollatzResearch.WordTrace]
  refine ⟨20132793097979096791106857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107374896522555182885903237 20132793097979096791106857)
  ·
    refine ⟨15099594823484322593330143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 20132793097979096791106857 15099594823484322593330143)
    ·
      refine ⟨22649392235226483889995215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15099594823484322593330143 22649392235226483889995215)
      ·
        refine ⟨33974088352839725834992823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22649392235226483889995215 33974088352839725834992823)
        ·
          refine ⟨50961132529259588752489235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33974088352839725834992823 50961132529259588752489235)
          ·
            refine ⟨76441698793889383128733853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50961132529259588752489235 76441698793889383128733853)
            ·
              refine ⟨28665637047708518673275195, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76441698793889383128733853 28665637047708518673275195)
              ·
                refine ⟨42998455571562778009912793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28665637047708518673275195 42998455571562778009912793)
                ·
                  refine ⟨32248841678672083507434595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42998455571562778009912793 32248841678672083507434595)
                  ·
                    refine ⟨48373262518008125261151893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32248841678672083507434595 48373262518008125261151893)
                    ·
                      refine ⟨2267496680531630871616495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48373262518008125261151893 2267496680531630871616495)
                      ·
                        rfl

theorem cell23_4415934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 1, 2, 1, 6].length) (baseStart_4415934 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415934 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415934 prefixEnd_4415934 := by exact prefixLift 4415934
  have htrace : WordTrace (prefixWord ++ tailWord_4415934) baseStart_4415934 baseEnd_4415934 := by
    simpa [prefixWord, tailWord_4415934, baseEnd_4415934] using wordTrace_append hprefix tailTrace_4415934
  have hstable : (prefixWord ++ tailWord_4415934).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415934).length < 2 ^ (prefixWord ++ tailWord_4415934).sum := by decide
  have hdescent : baseEnd_4415934 < baseStart_4415934 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415944 : List Nat := [2, 1, 3, 1, 3, 3, 1, 1, 8]
def baseStart_4415944 : Nat := 118140960795 + 4415944 * 2 ^ 59
def prefixEnd_4415944 : Nat := 4983230072969 + 3 ^ 40 * 4415944 * 2
def baseEnd_4415944 : Nat := 251944646148686203610161

theorem tailTrace_4415944 : CollatzResearch.WordTrace tailWord_4415944 prefixEnd_4415944 251944646148686203610161 := by
  unfold tailWord_4415944
  simp only [CollatzResearch.WordTrace]
  refine ⟨80531354756898273018359443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107375139675864364024479257 80531354756898273018359443)
  ·
    refine ⟨120797032135347409527539165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80531354756898273018359443 120797032135347409527539165)
    ·
      refine ⟨45298887050755278572827187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120797032135347409527539165 45298887050755278572827187)
      ·
        refine ⟨67948330576132917859240781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45298887050755278572827187 67948330576132917859240781)
        ·
          refine ⟨25480623966049844197215293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67948330576132917859240781 25480623966049844197215293)
          ·
            refine ⟨9555233987268691573955735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25480623966049844197215293 9555233987268691573955735)
            ·
              refine ⟨14332850980903037360933603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9555233987268691573955735 14332850980903037360933603)
              ·
                refine ⟨21499276471354556041400405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14332850980903037360933603 21499276471354556041400405)
                ·
                  refine ⟨251944646148686203610161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 21499276471354556041400405 251944646148686203610161)
                  ·
                    rfl

theorem cell23_4415944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 1, 8].length) (baseStart_4415944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415944 prefixEnd_4415944 := by exact prefixLift 4415944
  have htrace : WordTrace (prefixWord ++ tailWord_4415944) baseStart_4415944 baseEnd_4415944 := by
    simpa [prefixWord, tailWord_4415944, baseEnd_4415944] using wordTrace_append hprefix tailTrace_4415944
  have hstable : (prefixWord ++ tailWord_4415944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415944).length < 2 ^ (prefixWord ++ tailWord_4415944).sum := by decide
  have hdescent : baseEnd_4415944 < baseStart_4415944 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415948 : List Nat := [2, 2, 1, 4, 3, 1, 2, 1, 3, 4]
def baseStart_4415948 : Nat := 118140960795 + 4415948 * 2 ^ 59
def prefixEnd_4415948 : Nat := 4983230072969 + 3 ^ 40 * 4415948 * 2
def baseEnd_4415948 : Nat := 755834623086931272280477

theorem tailTrace_4415948 : CollatzResearch.WordTrace tailWord_4415948 prefixEnd_4415948 755834623086931272280477 := by
  unfold tailWord_4415948
  simp only [CollatzResearch.WordTrace]
  refine ⟨80531427702891027359932249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107375236937188036479909665 80531427702891027359932249)
  ·
    refine ⟨60398570777168270519949187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80531427702891027359932249 60398570777168270519949187)
    ·
      refine ⟨90597856165752405779923781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60398570777168270519949187 90597856165752405779923781)
      ·
        refine ⟨16987098031078576083735709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 90597856165752405779923781 16987098031078576083735709)
        ·
          refine ⟨6370161761654466031400891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 16987098031078576083735709 6370161761654466031400891)
          ·
            refine ⟨9555242642481699047101337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6370161761654466031400891 9555242642481699047101337)
            ·
              refine ⟨7166431981861274285326003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 9555242642481699047101337 7166431981861274285326003)
              ·
                refine ⟨10749647972791911427989005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7166431981861274285326003 10749647972791911427989005)
                ·
                  refine ⟨4031117989796966785495877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10749647972791911427989005 4031117989796966785495877)
                  ·
                    refine ⟨755834623086931272280477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4031117989796966785495877 755834623086931272280477)
                    ·
                      rfl

theorem cell23_4415948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 3, 1, 2, 1, 3, 4].length) (baseStart_4415948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415948 prefixEnd_4415948 := by exact prefixLift 4415948
  have htrace : WordTrace (prefixWord ++ tailWord_4415948) baseStart_4415948 baseEnd_4415948 := by
    simpa [prefixWord, tailWord_4415948, baseEnd_4415948] using wordTrace_append hprefix tailTrace_4415948
  have hstable : (prefixWord ++ tailWord_4415948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415948).length < 2 ^ (prefixWord ++ tailWord_4415948).sum := by decide
  have hdescent : baseEnd_4415948 < baseStart_4415948 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4415961 : List Nat := [1, 2, 1, 2, 4, 1, 5, 1, 6]
def baseStart_4415961 : Nat := 118140960795 + 4415961 * 2 ^ 59
def prefixEnd_4415961 : Nat := 4983230072969 + 3 ^ 40 * 4415961 * 2
def baseEnd_4415961 : Nat := 251945616056589140664319

theorem tailTrace_4415961 : CollatzResearch.WordTrace tailWord_4415961 prefixEnd_4415961 251945616056589140664319 := by
  unfold tailWord_4415961
  simp only [CollatzResearch.WordTrace]
  refine ⟨161063329554734957940087737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107375553036489971960058491 161063329554734957940087737)
  ·
    refine ⟨120797497166051218455065803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161063329554734957940087737 120797497166051218455065803)
    ·
      refine ⟨181196245749076827682598705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120797497166051218455065803 181196245749076827682598705)
      ·
        refine ⟨135897184311807620761949029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181196245749076827682598705 135897184311807620761949029)
        ·
          refine ⟨25480722058463928892865443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 135897184311807620761949029 25480722058463928892865443)
          ·
            refine ⟨38221083087695893339298165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25480722058463928892865443 38221083087695893339298165)
            ·
              refine ⟨3583226539471490000559203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38221083087695893339298165 3583226539471490000559203)
              ·
                refine ⟨5374839809207235000838805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583226539471490000559203 5374839809207235000838805)
                ·
                  refine ⟨251945616056589140664319, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 5374839809207235000838805 251945616056589140664319)
                  ·
                    rfl

theorem cell23_4415961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 5, 1, 6].length) (baseStart_4415961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4415961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4415961 prefixEnd_4415961 := by exact prefixLift 4415961
  have htrace : WordTrace (prefixWord ++ tailWord_4415961) baseStart_4415961 baseEnd_4415961 := by
    simpa [prefixWord, tailWord_4415961, baseEnd_4415961] using wordTrace_append hprefix tailTrace_4415961
  have hstable : (prefixWord ++ tailWord_4415961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4415961).length < 2 ^ (prefixWord ++ tailWord_4415961).sum := by decide
  have hdescent : baseEnd_4415961 < baseStart_4415961 := by decide
  rcases family_descends (prefixWord ++ tailWord_4415961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416028 : List Nat := [2, 2, 3, 1, 2, 2, 3, 2, 1, 1, 4]
def baseStart_4416028 : Nat := 118140960795 + 4416028 * 2 ^ 59
def prefixEnd_4416028 : Nat := 4983230072969 + 3 ^ 40 * 4416028 * 2
def baseEnd_4416028 : Nat := 2267544947713153503841063

theorem tailTrace_4416028 : CollatzResearch.WordTrace tailWord_4416028 prefixEnd_4416028 2267544947713153503841063 := by
  unfold tailWord_4416028
  simp only [CollatzResearch.WordTrace]
  refine ⟨80532886622746114191388369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107377182163661485588517825 80532886622746114191388369)
  ·
    refine ⟨60399664967059585643541277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80532886622746114191388369 60399664967059585643541277)
    ·
      refine ⟨22649874362647344616327979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 60399664967059585643541277 22649874362647344616327979)
      ·
        refine ⟨33974811543971016924491969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22649874362647344616327979 33974811543971016924491969)
        ·
          refine ⟨25481108657978262693368977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33974811543971016924491969 25481108657978262693368977)
          ·
            refine ⟨19110831493483697020026733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25481108657978262693368977 19110831493483697020026733)
            ·
              refine ⟨7166561810056386382510025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19110831493483697020026733 7166561810056386382510025)
              ·
                refine ⟨5374921357542289786882519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7166561810056386382510025 5374921357542289786882519)
                ·
                  refine ⟨8062382036313434680323779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5374921357542289786882519 8062382036313434680323779)
                  ·
                    refine ⟨12093573054470152020485669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8062382036313434680323779 12093573054470152020485669)
                    ·
                      refine ⟨2267544947713153503841063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12093573054470152020485669 2267544947713153503841063)
                      ·
                        rfl

theorem cell23_4416028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 3, 2, 1, 1, 4].length) (baseStart_4416028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416028 prefixEnd_4416028 := by exact prefixLift 4416028
  have htrace : WordTrace (prefixWord ++ tailWord_4416028) baseStart_4416028 baseEnd_4416028 := by
    simpa [prefixWord, tailWord_4416028, baseEnd_4416028] using wordTrace_append hprefix tailTrace_4416028
  have hstable : (prefixWord ++ tailWord_4416028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416028).length < 2 ^ (prefixWord ++ tailWord_4416028).sum := by decide
  have hdescent : baseEnd_4416028 < baseStart_4416028 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416064 : List Nat := [2, 1, 1, 2, 2, 2, 3, 1, 2, 7]
def baseStart_4416064 : Nat := 118140960795 + 4416064 * 2 ^ 59
def prefixEnd_4416064 : Nat := 4983230072969 + 3 ^ 40 * 4416064 * 2
def baseEnd_4416064 : Nat := 755854477672238454330299

theorem tailTrace_4416064 : CollatzResearch.WordTrace tailWord_4416064 prefixEnd_4416064 755854477672238454330299 := by
  unfold tailWord_4416064
  simp only [CollatzResearch.WordTrace]
  refine ⟨80533543136680903265543623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107378057515574537687391497 80533543136680903265543623)
  ·
    refine ⟨120800314705021354898315435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80533543136680903265543623 120800314705021354898315435)
    ·
      refine ⟨181200472057532032347473153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120800314705021354898315435 181200472057532032347473153)
      ·
        refine ⟨135900354043149024260604865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 181200472057532032347473153 135900354043149024260604865)
        ·
          refine ⟨101925265532361768195453649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135900354043149024260604865 101925265532361768195453649)
          ·
            refine ⟨76443949149271326146590237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101925265532361768195453649 76443949149271326146590237)
            ·
              refine ⟨28666480930976747304971339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76443949149271326146590237 28666480930976747304971339)
              ·
                refine ⟨42999721396465120957457009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28666480930976747304971339 42999721396465120957457009)
                ·
                  refine ⟨32249791047348840718092757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 42999721396465120957457009 32249791047348840718092757)
                  ·
                    refine ⟨755854477672238454330299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32249791047348840718092757 755854477672238454330299)
                    ·
                      rfl

theorem cell23_4416064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 2, 3, 1, 2, 7].length) (baseStart_4416064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416064 prefixEnd_4416064 := by exact prefixLift 4416064
  have htrace : WordTrace (prefixWord ++ tailWord_4416064) baseStart_4416064 baseEnd_4416064 := by
    simpa [prefixWord, tailWord_4416064, baseEnd_4416064] using wordTrace_append hprefix tailTrace_4416064
  have hstable : (prefixWord ++ tailWord_4416064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416064).length < 2 ^ (prefixWord ++ tailWord_4416064).sum := by decide
  have hdescent : baseEnd_4416064 < baseStart_4416064 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416088 : List Nat := [2, 1, 2, 2, 1, 2, 4, 1, 3, 3, 2]
def baseStart_4416088 : Nat := 118140960795 + 4416088 * 2 ^ 59
def prefixEnd_4416088 : Nat := 4983230072969 + 3 ^ 40 * 4416088 * 2
def baseEnd_4416088 : Nat := 2267575756552423269090787

theorem tailTrace_4416088 : CollatzResearch.WordTrace tailWord_4416088 prefixEnd_4416088 2267575756552423269090787 := by
  unfold tailWord_4416088
  simp only [CollatzResearch.WordTrace]
  refine ⟨80533980812637429314980459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107378641083516572419973945 80533980812637429314980459)
  ·
    refine ⟨120800971218956143972470689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80533980812637429314980459 120800971218956143972470689)
    ·
      refine ⟨90600728414217107979353017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120800971218956143972470689 90600728414217107979353017)
      ·
        refine ⟨67950546310662830984514763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90600728414217107979353017 67950546310662830984514763)
        ·
          refine ⟨101925819465994246476772145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67950546310662830984514763 101925819465994246476772145)
          ·
            refine ⟨76444364599495684857579109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101925819465994246476772145 76444364599495684857579109)
            ·
              refine ⟨14333318362405440910796083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76444364599495684857579109 14333318362405440910796083)
              ·
                refine ⟨21499977543608161366194125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14333318362405440910796083 21499977543608161366194125)
                ·
                  refine ⟨8062491578853060512322797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21499977543608161366194125 8062491578853060512322797)
                  ·
                    refine ⟨3023434342069897692121049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8062491578853060512322797 3023434342069897692121049)
                    ·
                      refine ⟨2267575756552423269090787, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023434342069897692121049 2267575756552423269090787)
                      ·
                        rfl

theorem cell23_4416088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 1, 3, 3, 2].length) (baseStart_4416088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416088 prefixEnd_4416088 := by exact prefixLift 4416088
  have htrace : WordTrace (prefixWord ++ tailWord_4416088) baseStart_4416088 baseEnd_4416088 := by
    simpa [prefixWord, tailWord_4416088, baseEnd_4416088] using wordTrace_append hprefix tailTrace_4416088
  have hstable : (prefixWord ++ tailWord_4416088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416088).length < 2 ^ (prefixWord ++ tailWord_4416088).sum := by decide
  have hdescent : baseEnd_4416088 < baseStart_4416088 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416112 : List Nat := [2, 1, 1, 1, 7, 2, 1, 2, 2, 1, 3]
def baseStart_4416112 : Nat := 118140960795 + 4416112 * 2 ^ 59
def prefixEnd_4416112 : Nat := 4983230072969 + 3 ^ 40 * 4416112 * 2
def baseEnd_4416112 : Nat := 2267588080088131175190677

theorem tailTrace_4416112 : CollatzResearch.WordTrace tailWord_4416112 prefixEnd_4416112 2267588080088131175190677 := by
  unfold tailWord_4416112
  simp only [CollatzResearch.WordTrace]
  refine ⟨80534418488593955364417295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107379224651458607152556393 80534418488593955364417295)
  ·
    refine ⟨120801627732890933046625943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80534418488593955364417295 120801627732890933046625943)
    ·
      refine ⟨181202441599336399569938915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120801627732890933046625943 181202441599336399569938915)
      ·
        refine ⟨271803662399004599354908373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181202441599336399569938915 271803662399004599354908373)
        ·
          refine ⟨6370398337476670297380665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 271803662399004599354908373 6370398337476670297380665)
          ·
            refine ⟨4777798753107502723035499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6370398337476670297380665 4777798753107502723035499)
            ·
              refine ⟨7166698129661254084553249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4777798753107502723035499 7166698129661254084553249)
              ·
                refine ⟨5375023597245940563414937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7166698129661254084553249 5375023597245940563414937)
                ·
                  refine ⟨4031267697934455422561203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5375023597245940563414937 4031267697934455422561203)
                  ·
                    refine ⟨6046901546901683133841805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4031267697934455422561203 6046901546901683133841805)
                    ·
                      refine ⟨2267588080088131175190677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6046901546901683133841805 2267588080088131175190677)
                      ·
                        rfl

theorem cell23_4416112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 1, 2, 2, 1, 3].length) (baseStart_4416112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416112 prefixEnd_4416112 := by exact prefixLift 4416112
  have htrace : WordTrace (prefixWord ++ tailWord_4416112) baseStart_4416112 baseEnd_4416112 := by
    simpa [prefixWord, tailWord_4416112, baseEnd_4416112] using wordTrace_append hprefix tailTrace_4416112
  have hstable : (prefixWord ++ tailWord_4416112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416112).length < 2 ^ (prefixWord ++ tailWord_4416112).sum := by decide
  have hdescent : baseEnd_4416112 < baseStart_4416112 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416131 : List Nat := [1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4]
def baseStart_4416131 : Nat := 118140960795 + 4416131 * 2 ^ 59
def prefixEnd_4416131 : Nat := 4983230072969 + 3 ^ 40 * 4416131 * 2
def baseEnd_4416131 : Nat := 2267597836220566600853089

theorem tailTrace_4416131 : CollatzResearch.WordTrace tailWord_4416131 prefixEnd_4416131 2267597836220566600853089 := by
  unfold tailWord_4416131
  simp only [CollatzResearch.WordTrace]
  refine ⟨161069529964119076973776247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107379686642746051315850831 161069529964119076973776247)
  ·
    refine ⟨241604294946178615460664371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161069529964119076973776247 241604294946178615460664371)
    ·
      refine ⟨362406442419267923190996557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241604294946178615460664371 362406442419267923190996557)
      ·
        refine ⟨135902415907225471196623709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362406442419267923190996557 135902415907225471196623709)
        ·
          refine ⟨50963405965209551698733891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 135902415907225471196623709 50963405965209551698733891)
          ·
            refine ⟨76445108947814327548100837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50963405965209551698733891 76445108947814327548100837)
            ·
              refine ⟨14333457927715186415268907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 76445108947814327548100837 14333457927715186415268907)
              ·
                refine ⟨21500186891572779622903361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14333457927715186415268907 21500186891572779622903361)
                ·
                  refine ⟨16125140168679584717177521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21500186891572779622903361 16125140168679584717177521)
                  ·
                    refine ⟨12093855126509688537883141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16125140168679584717177521 12093855126509688537883141)
                    ·
                      refine ⟨2267597836220566600853089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12093855126509688537883141 2267597836220566600853089)
                      ·
                        rfl

theorem cell23_4416131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 4, 1, 2, 2, 4].length) (baseStart_4416131 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416131 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416131 prefixEnd_4416131 := by exact prefixLift 4416131
  have htrace : WordTrace (prefixWord ++ tailWord_4416131) baseStart_4416131 baseEnd_4416131 := by
    simpa [prefixWord, tailWord_4416131, baseEnd_4416131] using wordTrace_append hprefix tailTrace_4416131
  have hstable : (prefixWord ++ tailWord_4416131).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416131).length < 2 ^ (prefixWord ++ tailWord_4416131).sum := by decide
  have hdescent : baseEnd_4416131 < baseStart_4416131 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416175 : List Nat := [1, 1, 2, 1, 2, 6, 3, 2, 5]
def baseStart_4416175 : Nat := 118140960795 + 4416175 * 2 ^ 59
def prefixEnd_4416175 : Nat := 4983230072969 + 3 ^ 40 * 4416175 * 2
def baseEnd_4416175 : Nat := 251957825485484936522543

theorem tailTrace_4416175 : CollatzResearch.WordTrace tailWord_4416175 prefixEnd_4416175 251957825485484936522543 := by
  unfold tailWord_4416175
  simp only [CollatzResearch.WordTrace]
  refine ⟨161071134775959672488377979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107380756517306448325585319 161071134775959672488377979)
  ·
    refine ⟨241606702163939508732566969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161071134775959672488377979 241606702163939508732566969)
    ·
      refine ⟨181205026622954631549425227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241606702163939508732566969 181205026622954631549425227)
      ·
        refine ⟨271807539934431947324137841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181205026622954631549425227 271807539934431947324137841)
        ·
          refine ⟨203855654950823960493103381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 271807539934431947324137841 203855654950823960493103381)
          ·
            refine ⟨9555733825819873148114221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203855654950823960493103381 9555733825819873148114221)
            ·
              refine ⟨3583400184682452430542833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9555733825819873148114221 3583400184682452430542833)
              ·
                refine ⟨2687550138511839322907125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583400184682452430542833 2687550138511839322907125)
                ·
                  refine ⟨251957825485484936522543, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687550138511839322907125 251957825485484936522543)
                  ·
                    rfl

theorem cell23_4416175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 6, 3, 2, 5].length) (baseStart_4416175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416175 prefixEnd_4416175 := by exact prefixLift 4416175
  have htrace : WordTrace (prefixWord ++ tailWord_4416175) baseStart_4416175 baseEnd_4416175 := by
    simpa [prefixWord, tailWord_4416175, baseEnd_4416175] using wordTrace_append hprefix tailTrace_4416175
  have hstable : (prefixWord ++ tailWord_4416175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416175).length < 2 ^ (prefixWord ++ tailWord_4416175).sum := by decide
  have hdescent : baseEnd_4416175 < baseStart_4416175 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416178 : List Nat := [3, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2]
def baseStart_4416178 : Nat := 118140960795 + 4416178 * 2 ^ 59
def prefixEnd_4416178 : Nat := 4983230072969 + 3 ^ 40 * 4416178 * 2
def baseEnd_4416178 : Nat := 2267621969811327916965373

theorem tailTrace_4416178 : CollatzResearch.WordTrace tailWord_4416178 prefixEnd_4416178 2267621969811327916965373 := by
  unfold tailWord_4416178
  simp only [CollatzResearch.WordTrace]
  refine ⟨40267811048737201000184297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107380829463299202667158125 40267811048737201000184297)
  ·
    refine ⟨30200858286552900750138223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 40267811048737201000184297 30200858286552900750138223)
    ·
      refine ⟨45301287429829351125207335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30200858286552900750138223 45301287429829351125207335)
      ·
        refine ⟨67951931144744026687811003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45301287429829351125207335 67951931144744026687811003)
        ·
          refine ⟨101927896717116040031716505, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67951931144744026687811003 101927896717116040031716505)
          ·
            refine ⟨76445922537837030023787379, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101927896717116040031716505 76445922537837030023787379)
            ·
              refine ⟨114668883806755545035681069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76445922537837030023787379 114668883806755545035681069)
              ·
                refine ⟨43000831427533329388380401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 114668883806755545035681069 43000831427533329388380401)
                ·
                  refine ⟨32250623570649997041285301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 43000831427533329388380401 32250623570649997041285301)
                  ·
                    refine ⟨3023495959748437222620497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32250623570649997041285301 3023495959748437222620497)
                    ·
                      refine ⟨2267621969811327916965373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023495959748437222620497 2267621969811327916965373)
                      ·
                        rfl

theorem cell23_4416178_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 1, 3, 2, 5, 2].length) (baseStart_4416178 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416178 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416178 prefixEnd_4416178 := by exact prefixLift 4416178
  have htrace : WordTrace (prefixWord ++ tailWord_4416178) baseStart_4416178 baseEnd_4416178 := by
    simpa [prefixWord, tailWord_4416178, baseEnd_4416178] using wordTrace_append hprefix tailTrace_4416178
  have hstable : (prefixWord ++ tailWord_4416178).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416178).length < 2 ^ (prefixWord ++ tailWord_4416178).sum := by decide
  have hdescent : baseEnd_4416178 < baseStart_4416178 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416178) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416302 : List Nat := [4, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2]
def baseStart_4416302 : Nat := 118140960795 + 4416302 * 2 ^ 59
def prefixEnd_4416302 : Nat := 4983230072969 + 3 ^ 40 * 4416302 * 2
def baseEnd_4416302 : Nat := 2267685641412485431814803

theorem tailTrace_4416302 : CollatzResearch.WordTrace tailWord_4416302 prefixEnd_4416302 2267685641412485431814803 := by
  unfold tailWord_4416302
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134470855812446647281395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107383844564333048785500773 20134470855812446647281395)
  ·
    refine ⟨30201706283718669970922093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20134470855812446647281395 30201706283718669970922093)
    ·
      refine ⟨11325639856394501239095785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 30201706283718669970922093 11325639856394501239095785)
      ·
        refine ⟨8494229892295875929321839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 11325639856394501239095785 8494229892295875929321839)
        ·
          refine ⟨12741344838443813893982759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 8494229892295875929321839 12741344838443813893982759)
          ·
            refine ⟨19112017257665720840974139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12741344838443813893982759 19112017257665720840974139)
            ·
              refine ⟨28668025886498581261461209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19112017257665720840974139 28668025886498581261461209)
              ·
                refine ⟨21501019414873935946095907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28668025886498581261461209 21501019414873935946095907)
                ·
                  refine ⟨32251529122310903919143861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21501019414873935946095907 32251529122310903919143861)
                  ·
                    refine ⟨3023580855216647242419737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32251529122310903919143861 3023580855216647242419737)
                    ·
                      refine ⟨2267685641412485431814803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023580855216647242419737 2267685641412485431814803)
                      ·
                        rfl

theorem cell23_4416302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 2, 1, 5, 2].length) (baseStart_4416302 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416302 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416302 prefixEnd_4416302 := by exact prefixLift 4416302
  have htrace : WordTrace (prefixWord ++ tailWord_4416302) baseStart_4416302 baseEnd_4416302 := by
    simpa [prefixWord, tailWord_4416302, baseEnd_4416302] using wordTrace_append hprefix tailTrace_4416302
  have hstable : (prefixWord ++ tailWord_4416302).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416302).length < 2 ^ (prefixWord ++ tailWord_4416302).sum := by decide
  have hdescent : baseEnd_4416302 < baseStart_4416302 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416328 : List Nat := [2, 1, 3, 1, 1, 3, 2, 1, 3, 2, 4]
def baseStart_4416328 : Nat := 118140960795 + 4416328 * 2 ^ 59
def prefixEnd_4416328 : Nat := 4983230072969 + 3 ^ 40 * 4416328 * 2
def baseEnd_4416328 : Nat := 2267698991909502330089683

theorem tailTrace_4416328 : CollatzResearch.WordTrace tailWord_4416328 prefixEnd_4416328 2267698991909502330089683 := by
  unfold tailWord_4416328
  simp only [CollatzResearch.WordTrace]
  refine ⟨80538357572202689809348819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107384476762936919745798425 80538357572202689809348819)
  ·
    refine ⟨120807536358304034714023229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80538357572202689809348819 120807536358304034714023229)
    ·
      refine ⟨45302826134364013017758711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120807536358304034714023229 45302826134364013017758711)
      ·
        refine ⟨67954239201546019526638067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45302826134364013017758711 67954239201546019526638067)
        ·
          refine ⟨101931358802319029289957101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67954239201546019526638067 101931358802319029289957101)
          ·
            refine ⟨38224259550869635983733913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101931358802319029289957101 38224259550869635983733913)
            ·
              refine ⟨28668194663152226987800435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38224259550869635983733913 28668194663152226987800435)
              ·
                refine ⟨43002291994728340481700653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28668194663152226987800435 43002291994728340481700653)
                ·
                  refine ⟨16125859498023127680637745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43002291994728340481700653 16125859498023127680637745)
                  ·
                    refine ⟨12094394623517345760478309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16125859498023127680637745 12094394623517345760478309)
                    ·
                      refine ⟨2267698991909502330089683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12094394623517345760478309 2267698991909502330089683)
                      ·
                        rfl

theorem cell23_4416328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 3, 2, 1, 3, 2, 4].length) (baseStart_4416328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416328 prefixEnd_4416328 := by exact prefixLift 4416328
  have htrace : WordTrace (prefixWord ++ tailWord_4416328) baseStart_4416328 baseEnd_4416328 := by
    simpa [prefixWord, tailWord_4416328, baseEnd_4416328] using wordTrace_append hprefix tailTrace_4416328
  have hstable : (prefixWord ++ tailWord_4416328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416328).length < 2 ^ (prefixWord ++ tailWord_4416328).sum := by decide
  have hdescent : baseEnd_4416328 < baseStart_4416328 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416359 : List Nat := [1, 1, 5, 1, 2, 4, 2, 1, 2, 4]
def baseStart_4416359 : Nat := 118140960795 + 4416359 * 2 ^ 59
def prefixEnd_4416359 : Nat := 4983230072969 + 3 ^ 40 * 4416359 * 2
def baseEnd_4416359 : Nat := 755904969936597236267347

theorem tailTrace_4416359 : CollatzResearch.WordTrace tailWord_4416359 prefixEnd_4416359 755904969936597236267347 := by
  unfold tailWord_4416359
  simp only [CollatzResearch.WordTrace]
  refine ⟨161077845807293071913076131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107385230538195381275384087 161077845807293071913076131)
  ·
    refine ⟨241616768710939607869614197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161077845807293071913076131 241616768710939607869614197)
    ·
      refine ⟨22651572066650588237776331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241616768710939607869614197 22651572066650588237776331)
      ·
        refine ⟨33977358099975882356664497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22651572066650588237776331 33977358099975882356664497)
        ·
          refine ⟨25483018574981911767498373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33977358099975882356664497 25483018574981911767498373)
          ·
            refine ⟨4778065982809108456405945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25483018574981911767498373 4778065982809108456405945)
            ·
              refine ⟨3583549487106831342304459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4778065982809108456405945 3583549487106831342304459)
              ·
                refine ⟨5375324230660247013456689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583549487106831342304459 5375324230660247013456689)
                ·
                  refine ⟨4031493172995185260092517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 5375324230660247013456689 4031493172995185260092517)
                  ·
                    refine ⟨755904969936597236267347, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4031493172995185260092517 755904969936597236267347)
                    ·
                      rfl

theorem cell23_4416359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 4, 2, 1, 2, 4].length) (baseStart_4416359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416359 prefixEnd_4416359 := by exact prefixLift 4416359
  have htrace : WordTrace (prefixWord ++ tailWord_4416359) baseStart_4416359 baseEnd_4416359 := by
    simpa [prefixWord, tailWord_4416359, baseEnd_4416359] using wordTrace_append hprefix tailTrace_4416359
  have hstable : (prefixWord ++ tailWord_4416359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416359).length < 2 ^ (prefixWord ++ tailWord_4416359).sum := by decide
  have hdescent : baseEnd_4416359 < baseStart_4416359 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416365 : List Nat := [1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 3]
def baseStart_4416365 : Nat := 118140960795 + 4416365 * 2 ^ 59
def prefixEnd_4416365 : Nat := 4983230072969 + 3 ^ 40 * 4416365 * 2
def baseEnd_4416365 : Nat := 2267717990693718685327013

theorem tailTrace_4416365 : CollatzResearch.WordTrace tailWord_4416365 prefixEnd_4416365 2267717990693718685327013 := by
  unfold tailWord_4416365
  simp only [CollatzResearch.WordTrace]
  refine ⟨161078064645271334937794549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107385376430180889958529699 161078064645271334937794549)
  ·
    refine ⟨15101068560494187650418239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161078064645271334937794549 15101068560494187650418239)
    ·
      refine ⟨22651602840741281475627359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 15101068560494187650418239 22651602840741281475627359)
      ·
        refine ⟨33977404261111922213441039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22651602840741281475627359 33977404261111922213441039)
        ·
          refine ⟨50966106391667883320161559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33977404261111922213441039 50966106391667883320161559)
          ·
            refine ⟨76449159587501824980242339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50966106391667883320161559 76449159587501824980242339)
            ·
              refine ⟨114673739381252737470363509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76449159587501824980242339 114673739381252737470363509)
              ·
                refine ⟨10750663066992444137846579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114673739381252737470363509 10750663066992444137846579)
                ·
                  refine ⟨16125994600488666206769869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10750663066992444137846579 16125994600488666206769869)
                  ·
                    refine ⟨6047247975183249827538701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16125994600488666206769869 6047247975183249827538701)
                    ·
                      refine ⟨2267717990693718685327013, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6047247975183249827538701 2267717990693718685327013)
                      ·
                        rfl

theorem cell23_4416365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 5, 1, 3, 3].length) (baseStart_4416365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416365 prefixEnd_4416365 := by exact prefixLift 4416365
  have htrace : WordTrace (prefixWord ++ tailWord_4416365) baseStart_4416365 baseEnd_4416365 := by
    simpa [prefixWord, tailWord_4416365, baseEnd_4416365] using wordTrace_append hprefix tailTrace_4416365
  have hstable : (prefixWord ++ tailWord_4416365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416365).length < 2 ^ (prefixWord ++ tailWord_4416365).sum := by decide
  have hdescent : baseEnd_4416365 < baseStart_4416365 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416366 : List Nat := [4, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4]
def baseStart_4416366 : Nat := 118140960795 + 4416366 * 2 ^ 59
def prefixEnd_4416366 : Nat := 4983230072969 + 3 ^ 40 * 4416366 * 2
def baseEnd_4416366 : Nat := 2267718504174373181414509

theorem tailTrace_4416366 : CollatzResearch.WordTrace tailWord_4416366 prefixEnd_4416366 2267718504174373181414509 := by
  unfold tailWord_4416366
  simp only [CollatzResearch.WordTrace]
  refine ⟨20134762639783464013572619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107385400745511808072387301 20134762639783464013572619)
  ·
    refine ⟨30202143959675196020358929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20134762639783464013572619 30202143959675196020358929)
    ·
      refine ⟨22651607969756397015269197, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30202143959675196020358929 22651607969756397015269197)
      ·
        refine ⟨8494352988658648880725949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 22651607969756397015269197 8494352988658648880725949)
        ·
          refine ⟨3185382370746993330272231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 8494352988658648880725949 3185382370746993330272231)
          ·
            refine ⟨4778073556120489995408347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3185382370746993330272231 4778073556120489995408347)
            ·
              refine ⟨7167110334180734993112521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778073556120489995408347 7167110334180734993112521)
              ·
                refine ⟨5375332750635551244834391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7167110334180734993112521 5375332750635551244834391)
                ·
                  refine ⟨8062999125953326867251587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5375332750635551244834391 8062999125953326867251587)
                  ·
                    refine ⟨12094498688929990300877381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 8062999125953326867251587 12094498688929990300877381)
                    ·
                      refine ⟨2267718504174373181414509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12094498688929990300877381 2267718504174373181414509)
                      ·
                        rfl

theorem cell23_4416366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 1, 2, 1, 1, 4].length) (baseStart_4416366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416366 prefixEnd_4416366 := by exact prefixLift 4416366
  have htrace : WordTrace (prefixWord ++ tailWord_4416366) baseStart_4416366 baseEnd_4416366 := by
    simpa [prefixWord, tailWord_4416366, baseEnd_4416366] using wordTrace_append hprefix tailTrace_4416366
  have hstable : (prefixWord ++ tailWord_4416366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416366).length < 2 ^ (prefixWord ++ tailWord_4416366).sum := by decide
  have hdescent : baseEnd_4416366 < baseStart_4416366 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416386 : List Nat := [3, 4, 2, 2, 1, 2, 1, 1, 1, 1, 5]
def baseStart_4416386 : Nat := 118140960795 + 4416386 * 2 ^ 59
def prefixEnd_4416386 : Nat := 4983230072969 + 3 ^ 40 * 4416386 * 2
def baseEnd_4416386 : Nat := 2267728773787463103164417

theorem tailTrace_4416386 : CollatzResearch.WordTrace tailWord_4416386 prefixEnd_4416386 2267728773787463103164417 := by
  unfold tailWord_4416386
  simp only [CollatzResearch.WordTrace]
  refine ⟨40269707644548813881077253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107385887052130170349539341 40269707644548813881077253)
  ·
    refine ⟨7550570183352902602701985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 40269707644548813881077253 7550570183352902602701985)
    ·
      refine ⟨5662927637514676952026489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 7550570183352902602701985 5662927637514676952026489)
      ·
        refine ⟨4247195728136007714019867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 5662927637514676952026489 4247195728136007714019867)
        ·
          refine ⟨6370793592204011571029801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247195728136007714019867 6370793592204011571029801)
          ·
            refine ⟨4778095194153008678272351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 6370793592204011571029801 4778095194153008678272351)
            ·
              refine ⟨7167142791229513017408527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778095194153008678272351 7167142791229513017408527)
              ·
                refine ⟨10750714186844269526112791, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167142791229513017408527 10750714186844269526112791)
                ·
                  refine ⟨16126071280266404289169187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10750714186844269526112791 16126071280266404289169187)
                  ·
                    refine ⟨24189106920399606433753781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16126071280266404289169187 24189106920399606433753781)
                    ·
                      refine ⟨2267728773787463103164417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24189106920399606433753781 2267728773787463103164417)
                      ·
                        rfl

theorem cell23_4416386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 2, 1, 2, 1, 1, 1, 1, 5].length) (baseStart_4416386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416386 prefixEnd_4416386 := by exact prefixLift 4416386
  have htrace : WordTrace (prefixWord ++ tailWord_4416386) baseStart_4416386 baseEnd_4416386 := by
    simpa [prefixWord, tailWord_4416386, baseEnd_4416386] using wordTrace_append hprefix tailTrace_4416386
  have hstable : (prefixWord ++ tailWord_4416386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416386).length < 2 ^ (prefixWord ++ tailWord_4416386).sum := by decide
  have hdescent : baseEnd_4416386 < baseStart_4416386 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416415 : List Nat := [1, 1, 2, 5, 2, 2, 1, 1, 2, 6]
def baseStart_4416415 : Nat := 118140960795 + 4416415 * 2 ^ 59
def prefixEnd_4416415 : Nat := 4983230072969 + 3 ^ 40 * 4416415 * 2
def baseEnd_4416415 : Nat := 755914554908814496567261

theorem tailTrace_4416415 : CollatzResearch.WordTrace tailWord_4416415 prefixEnd_4416415 755914554908814496567261 := by
  unfold tailWord_4416415
  simp only [CollatzResearch.WordTrace]
  refine ⟨161079888295090193477114699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107386592196726795651409799 161079888295090193477114699)
  ·
    refine ⟨241619832442635290215672049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161079888295090193477114699 241619832442635290215672049)
    ·
      refine ⟨181214874331976467661754037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241619832442635290215672049 181214874331976467661754037)
      ·
        refine ⟨16988894468622793843289441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 181214874331976467661754037 16988894468622793843289441)
        ·
          refine ⟨12741670851467095382467081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 16988894468622793843289441 12741670851467095382467081)
          ·
            refine ⟨9556253138600321536850311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 12741670851467095382467081 9556253138600321536850311)
            ·
              refine ⟨14334379707900482305275467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9556253138600321536850311 14334379707900482305275467)
              ·
                refine ⟨21501569561850723457913201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14334379707900482305275467 21501569561850723457913201)
                ·
                  refine ⟨16126177171388042593434901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21501569561850723457913201 16126177171388042593434901)
                  ·
                    refine ⟨755914554908814496567261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16126177171388042593434901 755914554908814496567261)
                    ·
                      rfl

theorem cell23_4416415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 2, 1, 1, 2, 6].length) (baseStart_4416415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416415 prefixEnd_4416415 := by exact prefixLift 4416415
  have htrace : WordTrace (prefixWord ++ tailWord_4416415) baseStart_4416415 baseEnd_4416415 := by
    simpa [prefixWord, tailWord_4416415, baseEnd_4416415] using wordTrace_append hprefix tailTrace_4416415
  have hstable : (prefixWord ++ tailWord_4416415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416415).length < 2 ^ (prefixWord ++ tailWord_4416415).sum := by decide
  have hdescent : baseEnd_4416415 < baseStart_4416415 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416428 : List Nat := [2, 2, 1, 1, 1, 1, 2, 6, 7]
def baseStart_4416428 : Nat := 118140960795 + 4416428 * 2 ^ 59
def prefixEnd_4416428 : Nat := 4983230072969 + 3 ^ 40 * 4416428 * 2
def baseEnd_4416428 : Nat := 251972259997216882093247

theorem tailTrace_4416428 : CollatzResearch.WordTrace tailWord_4416428 prefixEnd_4416428 251972259997216882093247 := by
  unfold tailWord_4416428
  simp only [CollatzResearch.WordTrace]
  refine ⟨80540181222021548348668969, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107386908296028731131558625 80540181222021548348668969)
  ·
    refine ⟨60405135916516161261501727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80540181222021548348668969 60405135916516161261501727)
    ·
      refine ⟨90607703874774241892252591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60405135916516161261501727 90607703874774241892252591)
      ·
        refine ⟨135911555812161362838378887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90607703874774241892252591 135911555812161362838378887)
        ·
          refine ⟨203867333718242044257568331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135911555812161362838378887 203867333718242044257568331)
          ·
            refine ⟨305801000577363066386352497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203867333718242044257568331 305801000577363066386352497)
            ·
              refine ⟨229350750433022299789764373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 305801000577363066386352497 229350750433022299789764373)
              ·
                refine ⟨10750816426547920302645205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 229350750433022299789764373 10750816426547920302645205)
                ·
                  refine ⟨251972259997216882093247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 10750816426547920302645205 251972259997216882093247)
                  ·
                    rfl

theorem cell23_4416428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 7].length) (baseStart_4416428 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416428 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416428 prefixEnd_4416428 := by exact prefixLift 4416428
  have htrace : WordTrace (prefixWord ++ tailWord_4416428) baseStart_4416428 baseEnd_4416428 := by
    simpa [prefixWord, tailWord_4416428, baseEnd_4416428] using wordTrace_append hprefix tailTrace_4416428
  have hstable : (prefixWord ++ tailWord_4416428).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416428).length < 2 ^ (prefixWord ++ tailWord_4416428).sum := by decide
  have hdescent : baseEnd_4416428 < baseStart_4416428 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416455 : List Nat := [1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 3]
def baseStart_4416455 : Nat := 118140960795 + 4416455 * 2 ^ 59
def prefixEnd_4416455 : Nat := 4983230072969 + 3 ^ 40 * 4416455 * 2
def baseEnd_4416455 : Nat := 2267764203952623333201599

theorem tailTrace_4416455 : CollatzResearch.WordTrace tailWord_4416455 prefixEnd_4416455 2267764203952623333201599 := by
  unfold tailWord_4416455
  simp only [CollatzResearch.WordTrace]
  refine ⟨161081347214945280308570819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107387564809963520205713879 161081347214945280308570819)
  ·
    refine ⟨241622020822417920462856229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161081347214945280308570819 241622020822417920462856229)
    ·
      refine ⟨45304128904203360086785543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241622020822417920462856229 45304128904203360086785543)
      ·
        refine ⟨67956193356305040130178315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45304128904203360086785543 67956193356305040130178315)
        ·
          refine ⟨101934290034457560195267473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67956193356305040130178315 101934290034457560195267473)
          ·
            refine ⟨76450717525843170146450605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101934290034457560195267473 76450717525843170146450605)
            ·
              refine ⟨28669019072191188804918977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76450717525843170146450605 28669019072191188804918977)
              ·
                refine ⟨21501764304143391603689233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28669019072191188804918977 21501764304143391603689233)
                ·
                  refine ⟨16126323228107543702766925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21501764304143391603689233 16126323228107543702766925)
                  ·
                    refine ⟨6047371210540328888537597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 16126323228107543702766925 6047371210540328888537597)
                    ·
                      refine ⟨2267764203952623333201599, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6047371210540328888537597 2267764203952623333201599)
                      ·
                        rfl

theorem cell23_4416455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 3, 2, 2, 3, 3].length) (baseStart_4416455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416455 prefixEnd_4416455 := by exact prefixLift 4416455
  have htrace : WordTrace (prefixWord ++ tailWord_4416455) baseStart_4416455 baseEnd_4416455 := by
    simpa [prefixWord, tailWord_4416455, baseEnd_4416455] using wordTrace_append hprefix tailTrace_4416455
  have hstable : (prefixWord ++ tailWord_4416455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416455).length < 2 ^ (prefixWord ++ tailWord_4416455).sum := by decide
  have hdescent : baseEnd_4416455 < baseStart_4416455 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416462 : List Nat := [4, 1, 1, 1, 2, 3, 2, 4, 5]
def baseStart_4416462 : Nat := 118140960795 + 4416462 * 2 ^ 59
def prefixEnd_4416462 : Nat := 4983230072969 + 3 ^ 40 * 4416462 * 2
def baseEnd_4416462 : Nat := 251974199813022756201563

theorem tailTrace_4416462 : CollatzResearch.WordTrace tailWord_4416462 prefixEnd_4416462 251974199813022756201563 := by
  unfold tailWord_4416462
  simp only [CollatzResearch.WordTrace]
  refine ⟨20135200315739990063009455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107387735017279947002717093 20135200315739990063009455)
  ·
    refine ⟨30202800473609985094514183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20135200315739990063009455 30202800473609985094514183)
    ·
      refine ⟨45304200710414977641771275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30202800473609985094514183 45304200710414977641771275)
      ·
        refine ⟨67956301065622466462656913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45304200710414977641771275 67956301065622466462656913)
        ·
          refine ⟨50967225799216849846992685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67956301065622466462656913 50967225799216849846992685)
          ·
            refine ⟨19112709674706318692622257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50967225799216849846992685 19112709674706318692622257)
            ·
              refine ⟨14334532256029739019466693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19112709674706318692622257 14334532256029739019466693)
              ·
                refine ⟨2687724798005576066150005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 14334532256029739019466693 2687724798005576066150005)
                ·
                  refine ⟨251974199813022756201563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2687724798005576066150005 251974199813022756201563)
                  ·
                    rfl

theorem cell23_4416462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 3, 2, 4, 5].length) (baseStart_4416462 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416462 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416462 prefixEnd_4416462 := by exact prefixLift 4416462
  have htrace : WordTrace (prefixWord ++ tailWord_4416462) baseStart_4416462 baseEnd_4416462 := by
    simpa [prefixWord, tailWord_4416462, baseEnd_4416462] using wordTrace_append hprefix tailTrace_4416462
  have hstable : (prefixWord ++ tailWord_4416462).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416462).length < 2 ^ (prefixWord ++ tailWord_4416462).sum := by decide
  have hdescent : baseEnd_4416462 < baseStart_4416462 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416495 : List Nat := [1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 4]
def baseStart_4416495 : Nat := 118140960795 + 4416495 * 2 ^ 59
def prefixEnd_4416495 : Nat := 4983230072969 + 3 ^ 40 * 4416495 * 2
def baseEnd_4416495 : Nat := 2267784743178803176701415

theorem tailTrace_4416495 : CollatzResearch.WordTrace tailWord_4416495 prefixEnd_4416495 2267784743178803176701415 := by
  unfold tailWord_4416495
  simp only [CollatzResearch.WordTrace]
  refine ⟨161082806134800367140026939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107388537423200244760017959 161082806134800367140026939)
  ·
    refine ⟨241624209202200550710040409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161082806134800367140026939 241624209202200550710040409)
    ·
      refine ⟨181218156901650413032530307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241624209202200550710040409 181218156901650413032530307)
      ·
        refine ⟨271827235352475619548795461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181218156901650413032530307 271827235352475619548795461)
        ·
          refine ⟨50967606628589178665399149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271827235352475619548795461 50967606628589178665399149)
          ·
            refine ⟨19112852485720941999524681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50967606628589178665399149 19112852485720941999524681)
            ·
              refine ⟨14334639364290706499643511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 19112852485720941999524681 14334639364290706499643511)
              ·
                refine ⟨21501959046436059749465267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14334639364290706499643511 21501959046436059749465267)
                ·
                  refine ⟨32252938569654089624197901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21501959046436059749465267 32252938569654089624197901)
                  ·
                    refine ⟨12094851963620283609074213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 32252938569654089624197901 12094851963620283609074213)
                    ·
                      refine ⟨2267784743178803176701415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12094851963620283609074213 2267784743178803176701415)
                      ·
                        rfl

theorem cell23_4416495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 1, 1, 3, 4].length) (baseStart_4416495 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416495 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416495 prefixEnd_4416495 := by exact prefixLift 4416495
  have htrace : WordTrace (prefixWord ++ tailWord_4416495) baseStart_4416495 baseEnd_4416495 := by
    simpa [prefixWord, tailWord_4416495, baseEnd_4416495] using wordTrace_append hprefix tailTrace_4416495
  have hstable : (prefixWord ++ tailWord_4416495).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416495).length < 2 ^ (prefixWord ++ tailWord_4416495).sum := by decide
  have hdescent : baseEnd_4416495 < baseStart_4416495 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416573 : List Nat := [1, 4, 1, 3, 1, 4, 2, 2, 1, 4]
def baseStart_4416573 : Nat := 118140960795 + 4416573 * 2 ^ 59
def prefixEnd_4416573 : Nat := 4983230072969 + 3 ^ 40 * 4416573 * 2
def baseEnd_4416573 : Nat := 755941598223284623842019

theorem tailTrace_4416573 : CollatzResearch.WordTrace tailWord_4416573 prefixEnd_4416573 755941598223284623842019 := by
  unfold tailWord_4416573
  simp only [CollatzResearch.WordTrace]
  refine ⟨161085651028517786461366373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107390434019011857640910915 161085651028517786461366373)
  ·
    refine ⟨30203559567847084961506195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161085651028517786461366373 30203559567847084961506195)
    ·
      refine ⟨45305339351770627442259293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30203559567847084961506195 45305339351770627442259293)
      ·
        refine ⟨16989502256913985290847235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 45305339351770627442259293 16989502256913985290847235)
        ·
          refine ⟨25484253385370977936270853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16989502256913985290847235 25484253385370977936270853)
          ·
            refine ⟨4778297509757058363050785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 25484253385370977936270853 4778297509757058363050785)
            ·
              refine ⟨3583723132317793772288089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4778297509757058363050785 3583723132317793772288089)
              ·
                refine ⟨2687792349238345329216067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3583723132317793772288089 2687792349238345329216067)
                ·
                  refine ⟨4031688523857517993824101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2687792349238345329216067 4031688523857517993824101)
                  ·
                    refine ⟨755941598223284623842019, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4031688523857517993824101 755941598223284623842019)
                    ·
                      rfl

theorem cell23_4416573_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 4, 2, 2, 1, 4].length) (baseStart_4416573 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416573 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416573 prefixEnd_4416573 := by exact prefixLift 4416573
  have htrace : WordTrace (prefixWord ++ tailWord_4416573) baseStart_4416573 baseEnd_4416573 := by
    simpa [prefixWord, tailWord_4416573, baseEnd_4416573] using wordTrace_append hprefix tailTrace_4416573
  have hstable : (prefixWord ++ tailWord_4416573).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416573).length < 2 ^ (prefixWord ++ tailWord_4416573).sum := by decide
  have hdescent : baseEnd_4416573 < baseStart_4416573 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416573) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416595 : List Nat := [1, 1, 1, 2, 1, 1, 2, 7, 1, 6]
def baseStart_4416595 : Nat := 118140960795 + 4416595 * 2 ^ 59
def prefixEnd_4416595 : Nat := 4983230072969 + 3 ^ 40 * 4416595 * 2
def baseEnd_4416595 : Nat := 755945363748084261816985

theorem tailTrace_4416595 : CollatzResearch.WordTrace tailWord_4416595 prefixEnd_4416595 755945363748084261816985 := by
  unfold tailWord_4416595
  simp only [CollatzResearch.WordTrace]
  refine ⟨161086453434438084218667239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107390968956292056145778159 161086453434438084218667239)
  ·
    refine ⟨241629680151657126328000859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161086453434438084218667239 241629680151657126328000859)
    ·
      refine ⟨362444520227485689492001289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241629680151657126328000859 362444520227485689492001289)
      ·
        refine ⟨271833390170614267119000967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362444520227485689492001289 271833390170614267119000967)
        ·
          refine ⟨407750085255921400678501451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271833390170614267119000967 407750085255921400678501451)
          ·
            refine ⟨611625127883882101017752177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407750085255921400678501451 611625127883882101017752177)
            ·
              refine ⟨458718845912911575763314133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611625127883882101017752177 458718845912911575763314133)
              ·
                refine ⟨10751222951083865056952675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 458718845912911575763314133 10751222951083865056952675)
                ·
                  refine ⟨16126834426625797585429013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10751222951083865056952675 16126834426625797585429013)
                  ·
                    refine ⟨755945363748084261816985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16126834426625797585429013 755945363748084261816985)
                    ·
                      rfl

theorem cell23_4416595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 7, 1, 6].length) (baseStart_4416595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416595 prefixEnd_4416595 := by exact prefixLift 4416595
  have htrace : WordTrace (prefixWord ++ tailWord_4416595) baseStart_4416595 baseEnd_4416595 := by
    simpa [prefixWord, tailWord_4416595, baseEnd_4416595] using wordTrace_append hprefix tailTrace_4416595
  have hstable : (prefixWord ++ tailWord_4416595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416595).length < 2 ^ (prefixWord ++ tailWord_4416595).sum := by decide
  have hdescent : baseEnd_4416595 < baseStart_4416595 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416602 : List Nat := [3, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2]
def baseStart_4416602 : Nat := 118140960795 + 4416602 * 2 ^ 59
def prefixEnd_4416602 : Nat := 4983230072969 + 3 ^ 40 * 4416602 * 2
def baseEnd_4416602 : Nat := 2267839685608834258063423

theorem tailTrace_4416602 : CollatzResearch.WordTrace tailWord_4416602 prefixEnd_4416602 2267839685608834258063423 := by
  unfold tailWord_4416602
  simp only [CollatzResearch.WordTrace]
  refine ⟨40271677186353181103543015, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107391139163608482942781373 40271677186353181103543015)
  ·
    refine ⟨60407515779529771655314523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40271677186353181103543015 60407515779529771655314523)
    ·
      refine ⟨90611273669294657482971785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60407515779529771655314523 90611273669294657482971785)
      ·
        refine ⟨67958455251970993112228839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 90611273669294657482971785 67958455251970993112228839)
        ·
          refine ⟨101937682877956489668343259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67958455251970993112228839 101937682877956489668343259)
          ·
            refine ⟨152906524316934734502514889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101937682877956489668343259 152906524316934734502514889)
            ·
              refine ⟨114679893237701050876886167, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 152906524316934734502514889 114679893237701050876886167)
              ·
                refine ⟨172019839856551576315329251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114679893237701050876886167 172019839856551576315329251)
                ·
                  refine ⟨258029759784827364472993877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172019839856551576315329251 258029759784827364472993877)
                  ·
                    refine ⟨3023786247478445677417897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 258029759784827364472993877 3023786247478445677417897)
                    ·
                      refine ⟨2267839685608834258063423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023786247478445677417897 2267839685608834258063423)
                      ·
                        rfl

theorem cell23_4416602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 1, 1, 8, 2].length) (baseStart_4416602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416602 prefixEnd_4416602 := by exact prefixLift 4416602
  have htrace : WordTrace (prefixWord ++ tailWord_4416602) baseStart_4416602 baseEnd_4416602 := by
    simpa [prefixWord, tailWord_4416602, baseEnd_4416602] using wordTrace_append hprefix tailTrace_4416602
  have hstable : (prefixWord ++ tailWord_4416602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416602).length < 2 ^ (prefixWord ++ tailWord_4416602).sum := by decide
  have hdescent : baseEnd_4416602 < baseStart_4416602 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416612 : List Nat := [2, 3, 1, 1, 2, 1, 1, 4, 4, 4]
def baseStart_4416612 : Nat := 118140960795 + 4416612 * 2 ^ 59
def prefixEnd_4416612 : Nat := 4983230072969 + 3 ^ 40 * 4416612 * 2
def baseEnd_4416612 : Nat := 755948273471793072979459

theorem tailTrace_4416612 : CollatzResearch.WordTrace tailWord_4416612 prefixEnd_4416612 755948273471793072979459 := by
  unfold tailWord_4416612
  simp only [CollatzResearch.WordTrace]
  refine ⟨80543536737688248061018045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107391382316917664081357393 80543536737688248061018045)
  ·
    refine ⟨30203826276633093022881767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 80543536737688248061018045 30203826276633093022881767)
    ·
      refine ⟨45305739414949639534322651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30203826276633093022881767 45305739414949639534322651)
      ·
        refine ⟨67958609122424459301483977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45305739414949639534322651 67958609122424459301483977)
        ·
          refine ⟨50968956841818344476112983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67958609122424459301483977 50968956841818344476112983)
          ·
            refine ⟨76453435262727516714169475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50968956841818344476112983 76453435262727516714169475)
            ·
              refine ⟨114680152894091275071254213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76453435262727516714169475 114680152894091275071254213)
              ·
                refine ⟨21502528667642114075860165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 114680152894091275071254213 21502528667642114075860165)
                ·
                  refine ⟨4031724125182896389223781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21502528667642114075860165 4031724125182896389223781)
                  ·
                    refine ⟨755948273471793072979459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4031724125182896389223781 755948273471793072979459)
                    ·
                      rfl

theorem cell23_4416612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 4, 4, 4].length) (baseStart_4416612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416612 prefixEnd_4416612 := by exact prefixLift 4416612
  have htrace : WordTrace (prefixWord ++ tailWord_4416612) baseStart_4416612 baseEnd_4416612 := by
    simpa [prefixWord, tailWord_4416612, baseEnd_4416612] using wordTrace_append hprefix tailTrace_4416612
  have hstable : (prefixWord ++ tailWord_4416612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416612).length < 2 ^ (prefixWord ++ tailWord_4416612).sum := by decide
  have hdescent : baseEnd_4416612 < baseStart_4416612 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416616 : List Nat := [2, 1, 4, 4, 1, 1, 1, 3, 1, 5]
def baseStart_4416616 : Nat := 118140960795 + 4416616 * 2 ^ 59
def prefixEnd_4416616 : Nat := 4983230072969 + 3 ^ 40 * 4416616 * 2
def baseEnd_4416616 : Nat := 755948958112665734429453

theorem tailTrace_4416616 : CollatzResearch.WordTrace tailWord_4416616 prefixEnd_4416616 755948958112665734429453 := by
  unfold tailWord_4416616
  simp only [CollatzResearch.WordTrace]
  refine ⟨80543609683681002402590851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107391479578241336536787801 80543609683681002402590851)
  ·
    refine ⟨120815414525521503603886277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80543609683681002402590851 120815414525521503603886277)
    ·
      refine ⟨22652890223535281925728677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120815414525521503603886277 22652890223535281925728677)
      ·
        refine ⟨4247416916912865361074127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22652890223535281925728677 4247416916912865361074127)
        ·
          refine ⟨6371125375369298041611191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4247416916912865361074127 6371125375369298041611191)
          ·
            refine ⟨9556688063053947062416787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 6371125375369298041611191 9556688063053947062416787)
            ·
              refine ⟨14335032094580920593625181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9556688063053947062416787 14335032094580920593625181)
              ·
                refine ⟨5375637035467845222609443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 14335032094580920593625181 5375637035467845222609443)
                ·
                  refine ⟨8063455553201767833914165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5375637035467845222609443 8063455553201767833914165)
                  ·
                    refine ⟨755948958112665734429453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8063455553201767833914165 755948958112665734429453)
                    ·
                      rfl

theorem cell23_4416616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 3, 1, 5].length) (baseStart_4416616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416616 prefixEnd_4416616 := by exact prefixLift 4416616
  have htrace : WordTrace (prefixWord ++ tailWord_4416616) baseStart_4416616 baseEnd_4416616 := by
    simpa [prefixWord, tailWord_4416616, baseEnd_4416616] using wordTrace_append hprefix tailTrace_4416616
  have hstable : (prefixWord ++ tailWord_4416616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416616).length < 2 ^ (prefixWord ++ tailWord_4416616).sum := by decide
  have hdescent : baseEnd_4416616 < baseStart_4416616 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416636 : List Nat := [2, 2, 2, 1, 1, 3, 4, 1, 3, 2, 2]
def baseStart_4416636 : Nat := 118140960795 + 4416636 * 2 ^ 59
def prefixEnd_4416636 : Nat := 4983230072969 + 3 ^ 40 * 4416636 * 2
def baseEnd_4416636 : Nat := 2267857143951087125038267

theorem tailTrace_4416636 : CollatzResearch.WordTrace tailWord_4416636 prefixEnd_4416636 2267857143951087125038267 := by
  unfold tailWord_4416636
  simp only [CollatzResearch.WordTrace]
  refine ⟨80543974413644774110454881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107391965884859698813939841 80543974413644774110454881)
  ·
    refine ⟨60407980810233580582841161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80543974413644774110454881 60407980810233580582841161)
    ·
      refine ⟨45305985607675185437130871, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 60407980810233580582841161 45305985607675185437130871)
      ·
        refine ⟨67958978411512778155696307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45305985607675185437130871 67958978411512778155696307)
        ·
          refine ⟨101938467617269167233544461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67958978411512778155696307 101938467617269167233544461)
          ·
            refine ⟨38226925356475937712579173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101938467617269167233544461 38226925356475937712579173)
            ·
              refine ⟨7167548504339238321108595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38226925356475937712579173 7167548504339238321108595)
              ·
                refine ⟨10751322756508857481662893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167548504339238321108595 10751322756508857481662893)
                ·
                  refine ⟨4031746033690821555623585, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 10751322756508857481662893 4031746033690821555623585)
                  ·
                    refine ⟨3023809525268116166717689, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4031746033690821555623585 3023809525268116166717689)
                    ·
                      refine ⟨2267857143951087125038267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023809525268116166717689 2267857143951087125038267)
                      ·
                        rfl

theorem cell23_4416636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 3, 4, 1, 3, 2, 2].length) (baseStart_4416636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416636 prefixEnd_4416636 := by exact prefixLift 4416636
  have htrace : WordTrace (prefixWord ++ tailWord_4416636) baseStart_4416636 baseEnd_4416636 := by
    simpa [prefixWord, tailWord_4416636, baseEnd_4416636] using wordTrace_append hprefix tailTrace_4416636
  have hstable : (prefixWord ++ tailWord_4416636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416636).length < 2 ^ (prefixWord ++ tailWord_4416636).sum := by decide
  have hdescent : baseEnd_4416636 < baseStart_4416636 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416649 : List Nat := [1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 4]
def baseStart_4416649 : Nat := 118140960795 + 4416649 * 2 ^ 59
def prefixEnd_4416649 : Nat := 4983230072969 + 3 ^ 40 * 4416649 * 2
def baseEnd_4416649 : Nat := 2267863819199595574175707

theorem tailTrace_4416649 : CollatzResearch.WordTrace tailWord_4416649 prefixEnd_4416649 2267863819199595574175707 := by
  unfold tailWord_4416649
  simp only [CollatzResearch.WordTrace]
  refine ⟨161088422976242451441133001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107392281984161634294088667 161088422976242451441133001)
  ·
    refine ⟨120816317232181838580849751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161088422976242451441133001 120816317232181838580849751)
    ·
      refine ⟨181224475848272757871274627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120816317232181838580849751 181224475848272757871274627)
      ·
        refine ⟨271836713772409136806911941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181224475848272757871274627 271836713772409136806911941)
        ·
          refine ⟨50969383832326713151295989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 271836713772409136806911941 50969383832326713151295989)
          ·
            refine ⟨4778379734280629357933999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 50969383832326713151295989 4778379734280629357933999)
            ·
              refine ⟨7167569601420944036900999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 4778379734280629357933999 7167569601420944036900999)
              ·
                refine ⟨10751354402131416055351499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167569601420944036900999 10751354402131416055351499)
                ·
                  refine ⟨16127031603197124083027249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10751354402131416055351499 16127031603197124083027249)
                  ·
                    refine ⟨12095273702397843062270437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16127031603197124083027249 12095273702397843062270437)
                    ·
                      refine ⟨2267863819199595574175707, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12095273702397843062270437 2267863819199595574175707)
                      ·
                        rfl

theorem cell23_4416649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 5, 1, 1, 1, 2, 4].length) (baseStart_4416649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416649 prefixEnd_4416649 := by exact prefixLift 4416649
  have htrace : WordTrace (prefixWord ++ tailWord_4416649) baseStart_4416649 baseEnd_4416649 := by
    simpa [prefixWord, tailWord_4416649, baseEnd_4416649] using wordTrace_append hprefix tailTrace_4416649
  have hstable : (prefixWord ++ tailWord_4416649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416649).length < 2 ^ (prefixWord ++ tailWord_4416649).sum := by decide
  have hdescent : baseEnd_4416649 < baseStart_4416649 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416669 : List Nat := [1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 3]
def baseStart_4416669 : Nat := 118140960795 + 4416669 * 2 ^ 59
def prefixEnd_4416669 : Nat := 4983230072969 + 3 ^ 40 * 4416669 * 2
def baseEnd_4416669 : Nat := 2267874088812685495925615

theorem tailTrace_4416669 : CollatzResearch.WordTrace tailWord_4416669 prefixEnd_4416669 2267874088812685495925615 := by
  unfold tailWord_4416669
  simp only [CollatzResearch.WordTrace]
  refine ⟨161089152436169994856861061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107392768290779996571240707 161089152436169994856861061)
  ·
    refine ⟨30204216081781874035661449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161089152436169994856861061 30204216081781874035661449)
    ·
      refine ⟨22653162061336405526746087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 30204216081781874035661449 22653162061336405526746087)
      ·
        refine ⟨33979743092004608290119131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22653162061336405526746087 33979743092004608290119131)
        ·
          refine ⟨50969614638006912435178697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33979743092004608290119131 50969614638006912435178697)
          ·
            refine ⟨38227210978505184326384023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50969614638006912435178697 38227210978505184326384023)
            ·
              refine ⟨57340816467757776489576035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38227210978505184326384023 57340816467757776489576035)
              ·
                refine ⟨86011224701636664734364053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57340816467757776489576035 86011224701636664734364053)
                ·
                  refine ⟨4031776157889218659423315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 86011224701636664734364053 4031776157889218659423315)
                  ·
                    refine ⟨6047664236833827989134973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4031776157889218659423315 6047664236833827989134973)
                    ·
                      refine ⟨2267874088812685495925615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6047664236833827989134973 2267874088812685495925615)
                      ·
                        rfl

theorem cell23_4416669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 2, 1, 1, 6, 1, 3].length) (baseStart_4416669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416669 prefixEnd_4416669 := by exact prefixLift 4416669
  have htrace : WordTrace (prefixWord ++ tailWord_4416669) baseStart_4416669 baseEnd_4416669 := by
    simpa [prefixWord, tailWord_4416669, baseEnd_4416669] using wordTrace_append hprefix tailTrace_4416669
  have hstable : (prefixWord ++ tailWord_4416669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416669).length < 2 ^ (prefixWord ++ tailWord_4416669).sum := by decide
  have hdescent : baseEnd_4416669 < baseStart_4416669 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416675 : List Nat := [1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8]
def baseStart_4416675 : Nat := 118140960795 + 4416675 * 2 ^ 59
def prefixEnd_4416675 : Nat := 4983230072969 + 3 ^ 40 * 4416675 * 2
def baseEnd_4416675 : Nat := 2267877169696612472450587

theorem tailTrace_4416675 : CollatzResearch.WordTrace tailWord_4416675 prefixEnd_4416675 2267877169696612472450587 := by
  unfold tailWord_4416675
  simp only [CollatzResearch.WordTrace]
  refine ⟨161089371274148257881579479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107392914182765505254386319 161089371274148257881579479)
  ·
    refine ⟨241634056911222386822369219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161089371274148257881579479 241634056911222386822369219)
    ·
      refine ⟨362451085366833580233553829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241634056911222386822369219 362451085366833580233553829)
      ·
        refine ⟨67959578506281296293791343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 362451085366833580233553829 67959578506281296293791343)
        ·
          refine ⟨101939367759421944440687015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67959578506281296293791343 101939367759421944440687015)
          ·
            refine ⟨152909051639132916661030523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101939367759421944440687015 152909051639132916661030523)
            ·
              refine ⟨229363577458699374991545785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 152909051639132916661030523 229363577458699374991545785)
              ·
                refine ⟨172022683094024531243659339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 229363577458699374991545785 172022683094024531243659339)
                ·
                  refine ⟨258034024641036796865489009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172022683094024531243659339 258034024641036796865489009)
                  ·
                    refine ⟨193525518480777597649116757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 258034024641036796865489009 193525518480777597649116757)
                    ·
                      refine ⟨2267877169696612472450587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 193525518480777597649116757 2267877169696612472450587)
                      ·
                        rfl

theorem cell23_4416675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 1, 1, 2, 1, 2, 8].length) (baseStart_4416675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416675 prefixEnd_4416675 := by exact prefixLift 4416675
  have htrace : WordTrace (prefixWord ++ tailWord_4416675) baseStart_4416675 baseEnd_4416675 := by
    simpa [prefixWord, tailWord_4416675, baseEnd_4416675] using wordTrace_append hprefix tailTrace_4416675
  have hstable : (prefixWord ++ tailWord_4416675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416675).length < 2 ^ (prefixWord ++ tailWord_4416675).sum := by decide
  have hdescent : baseEnd_4416675 < baseStart_4416675 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416709 : List Nat := [1, 3, 1, 1, 1, 1, 3, 5, 1, 4, 2]
def baseStart_4416709 : Nat := 118140960795 + 4416709 * 2 ^ 59
def prefixEnd_4416709 : Nat := 4983230072969 + 3 ^ 40 * 4416709 * 2
def baseEnd_4416709 : Nat := 2267894628038865339425431

theorem tailTrace_4416709 : CollatzResearch.WordTrace tailWord_4416709 prefixEnd_4416709 2267894628038865339425431 := by
  unfold tailWord_4416709
  simp only [CollatzResearch.WordTrace]
  refine ⟨161090611356025081688317181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107393740904016721125544787 161090611356025081688317181)
  ·
    refine ⟨60408979258509405633118943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161090611356025081688317181 60408979258509405633118943)
    ·
      refine ⟨90613468887764108449678415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60408979258509405633118943 90613468887764108449678415)
      ·
        refine ⟨135920203331646162674517623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90613468887764108449678415 135920203331646162674517623)
        ·
          refine ⟨203880304997469244011776435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135920203331646162674517623 203880304997469244011776435)
          ·
            refine ⟨305820457496203866017664653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 203880304997469244011776435 305820457496203866017664653)
            ·
              refine ⟨114682671561076449756624245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 305820457496203866017664653 114682671561076449756624245)
              ·
                refine ⟨10751500458850917164683523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 114682671561076449756624245 10751500458850917164683523)
                ·
                  refine ⟨16127250688276375747025285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10751500458850917164683523 16127250688276375747025285)
                  ·
                    refine ⟨3023859504051820452567241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 16127250688276375747025285 3023859504051820452567241)
                    ·
                      refine ⟨2267894628038865339425431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023859504051820452567241 2267894628038865339425431)
                      ·
                        rfl

theorem cell23_4416709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 5, 1, 4, 2].length) (baseStart_4416709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416709 prefixEnd_4416709 := by exact prefixLift 4416709
  have htrace : WordTrace (prefixWord ++ tailWord_4416709) baseStart_4416709 baseEnd_4416709 := by
    simpa [prefixWord, tailWord_4416709, baseEnd_4416709] using wordTrace_append hprefix tailTrace_4416709
  have hstable : (prefixWord ++ tailWord_4416709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416709).length < 2 ^ (prefixWord ++ tailWord_4416709).sum := by decide
  have hdescent : baseEnd_4416709 < baseStart_4416709 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416712 : List Nat := [2, 1, 3, 1, 2, 1, 3, 2, 2, 1, 5]
def baseStart_4416712 : Nat := 118140960795 + 4416712 * 2 ^ 59
def prefixEnd_4416712 : Nat := 4983230072969 + 3 ^ 40 * 4416712 * 2
def baseEnd_4416712 : Nat := 2267896168480828827687917

theorem tailTrace_4416712 : CollatzResearch.WordTrace tailWord_4416712 prefixEnd_4416712 2267896168480828827687917 := by
  unfold tailWord_4416712
  simp only [CollatzResearch.WordTrace]
  refine ⟨80545360387507106600338195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107393813850009475467117593 80545360387507106600338195)
  ·
    refine ⟨120818040581260659900507293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80545360387507106600338195 120818040581260659900507293)
    ·
      refine ⟨45306765217972747462690235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 120818040581260659900507293 45306765217972747462690235)
      ·
        refine ⟨67960147826959121194035353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45306765217972747462690235 67960147826959121194035353)
        ·
          refine ⟨50970110870219340895526515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67960147826959121194035353 50970110870219340895526515)
          ·
            refine ⟨76455166305329011343289773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50970110870219340895526515 76455166305329011343289773)
            ·
              refine ⟨28670687364498379253733665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 76455166305329011343289773 28670687364498379253733665)
              ·
                refine ⟨21503015523373784440300249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28670687364498379253733665 21503015523373784440300249)
                ·
                  refine ⟨16127261642530338330225187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21503015523373784440300249 16127261642530338330225187)
                  ·
                    refine ⟨24190892463795507495337781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16127261642530338330225187 24190892463795507495337781)
                    ·
                      refine ⟨2267896168480828827687917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24190892463795507495337781 2267896168480828827687917)
                      ·
                        rfl

theorem cell23_4416712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 1, 3, 2, 2, 1, 5].length) (baseStart_4416712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416712 prefixEnd_4416712 := by exact prefixLift 4416712
  have htrace : WordTrace (prefixWord ++ tailWord_4416712) baseStart_4416712 baseEnd_4416712 := by
    simpa [prefixWord, tailWord_4416712, baseEnd_4416712] using wordTrace_append hprefix tailTrace_4416712
  have hstable : (prefixWord ++ tailWord_4416712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416712).length < 2 ^ (prefixWord ++ tailWord_4416712).sum := by decide
  have hdescent : baseEnd_4416712 < baseStart_4416712 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416762 : List Nat := [3, 1, 1, 1, 1, 4, 2, 2, 1, 7]
def baseStart_4416762 : Nat := 118140960795 + 4416762 * 2 ^ 59
def prefixEnd_4416762 : Nat := 4983230072969 + 3 ^ 40 * 4416762 * 2
def baseEnd_4416762 : Nat := 755973947504517877354229

theorem tailTrace_4416762 : CollatzResearch.WordTrace tailWord_4416762 prefixEnd_4416762 755973947504517877354229 := by
  unfold tailWord_4416762
  simp only [CollatzResearch.WordTrace]
  refine ⟨40273136106208267934999135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 107395029616555381159997693 40273136106208267934999135)
  ·
    refine ⟨60409704159312401902498703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 40273136106208267934999135 60409704159312401902498703)
    ·
      refine ⟨90614556238968602853748055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60409704159312401902498703 90614556238968602853748055)
      ·
        refine ⟨135921834358452904280622083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90614556238968602853748055 135921834358452904280622083)
        ·
          refine ⟨203882751537679356420933125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135921834358452904280622083 203882751537679356420933125)
          ·
            refine ⟨38228015913314879328924961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 203882751537679356420933125 38228015913314879328924961)
            ·
              refine ⟨28671011934986159496693721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38228015913314879328924961 28671011934986159496693721)
              ·
                refine ⟨21503258951239619622520291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28671011934986159496693721 21503258951239619622520291)
                ·
                  refine ⟨32254888426859429433780437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21503258951239619622520291 32254888426859429433780437)
                  ·
                    refine ⟨755973947504517877354229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 32254888426859429433780437 755973947504517877354229)
                    ·
                      rfl

theorem cell23_4416762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 2, 1, 7].length) (baseStart_4416762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416762 prefixEnd_4416762 := by exact prefixLift 4416762
  have htrace : WordTrace (prefixWord ++ tailWord_4416762) baseStart_4416762 baseEnd_4416762 := by
    simpa [prefixWord, tailWord_4416762, baseEnd_4416762] using wordTrace_append hprefix tailTrace_4416762
  have hstable : (prefixWord ++ tailWord_4416762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416762).length < 2 ^ (prefixWord ++ tailWord_4416762).sum := by decide
  have hdescent : baseEnd_4416762 < baseStart_4416762 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416779 : List Nat := [1, 1, 1, 1, 5, 3, 3, 1, 2, 5]
def baseStart_4416779 : Nat := 118140960795 + 4416779 * 2 ^ 59
def prefixEnd_4416779 : Nat := 4983230072969 + 3 ^ 40 * 4416779 * 2
def baseEnd_4416779 : Nat := 755976857228226688516703

theorem tailTrace_4416779 : CollatzResearch.WordTrace tailWord_4416779 prefixEnd_4416779 755976857228226688516703 := by
  unfold tailWord_4416779
  simp only [CollatzResearch.WordTrace]
  refine ⟨161093164465771483643365391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107395442977180989095576927 161093164465771483643365391)
  ·
    refine ⟨241639746698657225465048087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161093164465771483643365391 241639746698657225465048087)
    ·
      refine ⟨362459620047985838197572131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241639746698657225465048087 362459620047985838197572131)
      ·
        refine ⟨543689430071978757296358197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362459620047985838197572131 543689430071978757296358197)
        ·
          refine ⟨50970884069248008496533581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 543689430071978757296358197 50970884069248008496533581)
          ·
            refine ⟨19114081525968003186200093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 50970884069248008496533581 19114081525968003186200093)
            ·
              refine ⟨7167780572238001194825035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 19114081525968003186200093 7167780572238001194825035)
              ·
                refine ⟨10751670858357001792237553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167780572238001194825035 10751670858357001792237553)
                ·
                  refine ⟨8063753143767751344178165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10751670858357001792237553 8063753143767751344178165)
                  ·
                    refine ⟨755976857228226688516703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8063753143767751344178165 755976857228226688516703)
                    ·
                      rfl

theorem cell23_4416779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 3, 3, 1, 2, 5].length) (baseStart_4416779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416779 prefixEnd_4416779 := by exact prefixLift 4416779
  have htrace : WordTrace (prefixWord ++ tailWord_4416779) baseStart_4416779 baseEnd_4416779 := by
    simpa [prefixWord, tailWord_4416779, baseEnd_4416779] using wordTrace_append hprefix tailTrace_4416779
  have hstable : (prefixWord ++ tailWord_4416779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416779).length < 2 ^ (prefixWord ++ tailWord_4416779).sum := by decide
  have hdescent : baseEnd_4416779 < baseStart_4416779 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416812 : List Nat := [2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 6]
def baseStart_4416812 : Nat := 118140960795 + 4416812 * 2 ^ 59
def prefixEnd_4416812 : Nat := 4983230072969 + 3 ^ 40 * 4416812 * 2
def baseEnd_4416812 : Nat := 2267947516546278436437457

theorem tailTrace_4416812 : CollatzResearch.WordTrace tailWord_4416812 prefixEnd_4416812 2267947516546278436437457 := by
  unfold tailWord_4416812
  simp only [CollatzResearch.WordTrace]
  refine ⟨80547184037325965139658345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107396245383101286852877793 80547184037325965139658345)
  ·
    refine ⟨60410388027994473854743759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80547184037325965139658345 60410388027994473854743759)
    ·
      refine ⟨90615582041991710782115639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60410388027994473854743759 90615582041991710782115639)
      ·
        refine ⟨135923373062987566173173459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90615582041991710782115639 135923373062987566173173459)
        ·
          refine ⟨203885059594481349259760189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135923373062987566173173459 203885059594481349259760189)
          ·
            refine ⟨76456897347930505972410071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 203885059594481349259760189 76456897347930505972410071)
            ·
              refine ⟨114685346021895758958615107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76456897347930505972410071 114685346021895758958615107)
              ·
                refine ⟨172028019032843638437922661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114685346021895758958615107 172028019032843638437922661)
                ·
                  refine ⟨32255253568658182207110499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 172028019032843638437922661 32255253568658182207110499)
                  ·
                    refine ⟨48382880352987273310665749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 32255253568658182207110499 48382880352987273310665749)
                    ·
                      refine ⟨2267947516546278436437457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 48382880352987273310665749 2267947516546278436437457)
                      ·
                        rfl

theorem cell23_4416812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 6].length) (baseStart_4416812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416812 prefixEnd_4416812 := by exact prefixLift 4416812
  have htrace : WordTrace (prefixWord ++ tailWord_4416812) baseStart_4416812 baseEnd_4416812 := by
    simpa [prefixWord, tailWord_4416812, baseEnd_4416812] using wordTrace_append hprefix tailTrace_4416812
  have hstable : (prefixWord ++ tailWord_4416812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416812).length < 2 ^ (prefixWord ++ tailWord_4416812).sum := by decide
  have hdescent : baseEnd_4416812 < baseStart_4416812 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416819 : List Nat := [1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 3]
def baseStart_4416819 : Nat := 118140960795 + 4416819 * 2 ^ 59
def prefixEnd_4416819 : Nat := 4983230072969 + 3 ^ 40 * 4416819 * 2
def baseEnd_4416819 : Nat := 2267951110910859909049925

theorem tailTrace_4416819 : CollatzResearch.WordTrace tailWord_4416819 prefixEnd_4416819 2267951110910859909049925 := by
  unfold tailWord_4416819
  simp only [CollatzResearch.WordTrace]
  refine ⟨161094623385626570474821511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107396415590417713649881007 161094623385626570474821511)
  ·
    refine ⟨241641935078439855712232267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161094623385626570474821511 241641935078439855712232267)
    ·
      refine ⟨362462902617659783568348401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241641935078439855712232267 362462902617659783568348401)
      ·
        refine ⟨271847176963244837676261301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362462902617659783568348401 271847176963244837676261301)
        ·
          refine ⟨25485672840304203532149497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 271847176963244837676261301 25485672840304203532149497)
          ·
            refine ⟨19114254630228152649112123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 25485672840304203532149497 19114254630228152649112123)
            ·
              refine ⟨28671381945342228973668185, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19114254630228152649112123 28671381945342228973668185)
              ·
                refine ⟨21503536459006671730251139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28671381945342228973668185 21503536459006671730251139)
                ·
                  refine ⟨32255304688510007595376709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21503536459006671730251139 32255304688510007595376709)
                  ·
                    refine ⟨6047869629095626424133133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32255304688510007595376709 6047869629095626424133133)
                    ·
                      refine ⟨2267951110910859909049925, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6047869629095626424133133 2267951110910859909049925)
                      ·
                        rfl

theorem cell23_4416819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 2, 1, 4, 3].length) (baseStart_4416819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416819 prefixEnd_4416819 := by exact prefixLift 4416819
  have htrace : WordTrace (prefixWord ++ tailWord_4416819) baseStart_4416819 baseEnd_4416819 := by
    simpa [prefixWord, tailWord_4416819, baseEnd_4416819] using wordTrace_append hprefix tailTrace_4416819
  have hstable : (prefixWord ++ tailWord_4416819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416819).length < 2 ^ (prefixWord ++ tailWord_4416819).sum := by decide
  have hdescent : baseEnd_4416819 < baseStart_4416819 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416869 : List Nat := [1, 3, 1, 3, 1, 2, 2, 2, 3, 5]
def baseStart_4416869 : Nat := 118140960795 + 4416869 * 2 ^ 59
def prefixEnd_4416869 : Nat := 4983230072969 + 3 ^ 40 * 4416869 * 2
def baseEnd_4416869 : Nat := 755992261647861571141565

theorem tailTrace_4416869 : CollatzResearch.WordTrace tailWord_4416869 prefixEnd_4416869 755992261647861571141565 := by
  unfold tailWord_4416869
  simp only [CollatzResearch.WordTrace]
  refine ⟨161096447035445429014141661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107397631356963619342761107 161096447035445429014141661)
  ·
    refine ⟨60411167638292035880303123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161096447035445429014141661 60411167638292035880303123)
    ·
      refine ⟨90616751457438053820454685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60411167638292035880303123 90616751457438053820454685)
      ·
        refine ⟨33981281796539270182670507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90616751457438053820454685 33981281796539270182670507)
        ·
          refine ⟨50971922694808905274005761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33981281796539270182670507 50971922694808905274005761)
          ·
            refine ⟨38228942021106678955504321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50971922694808905274005761 38228942021106678955504321)
            ·
              refine ⟨28671706515830009216628241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 38228942021106678955504321 28671706515830009216628241)
              ·
                refine ⟨21503779886872506912471181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 28671706515830009216628241 21503779886872506912471181)
                ·
                  refine ⟨8063917457577190092176693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21503779886872506912471181 8063917457577190092176693)
                  ·
                    refine ⟨755992261647861571141565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8063917457577190092176693 755992261647861571141565)
                    ·
                      rfl

theorem cell23_4416869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 2, 3, 5].length) (baseStart_4416869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416869 prefixEnd_4416869 := by exact prefixLift 4416869
  have htrace : WordTrace (prefixWord ++ tailWord_4416869) baseStart_4416869 baseEnd_4416869 := by
    simpa [prefixWord, tailWord_4416869, baseEnd_4416869] using wordTrace_append hprefix tailTrace_4416869
  have hstable : (prefixWord ++ tailWord_4416869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416869).length < 2 ^ (prefixWord ++ tailWord_4416869).sum := by decide
  have hdescent : baseEnd_4416869 < baseStart_4416869 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416893 : List Nat := [1, 4, 1, 1, 2, 2, 4, 1, 2, 3, 2]
def baseStart_4416893 : Nat := 118140960795 + 4416893 * 2 ^ 59
def prefixEnd_4416893 : Nat := 4983230072969 + 3 ^ 40 * 4416893 * 2
def baseEnd_4416893 : Nat := 2267989108479292619524585

theorem tailTrace_4416893 : CollatzResearch.WordTrace tailWord_4416893 prefixEnd_4416893 2267989108479292619524585 := by
  unfold tailWord_4416893
  simp only [CollatzResearch.WordTrace]
  refine ⟨161097322387358481113015333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107398214924905654075343555 161097322387358481113015333)
  ·
    refine ⟨30205747947629715208690375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161097322387358481113015333 30205747947629715208690375)
    ·
      refine ⟨45308621921444572813035563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30205747947629715208690375 45308621921444572813035563)
      ·
        refine ⟨67962932882166859219553345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45308621921444572813035563 67962932882166859219553345)
        ·
          refine ⟨50972199661625144414665009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67962932882166859219553345 50972199661625144414665009)
          ·
            refine ⟨38229149746218858310998757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50972199661625144414665009 38229149746218858310998757)
            ·
              refine ⟨7167965577416035933312267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38229149746218858310998757 7167965577416035933312267)
              ·
                refine ⟨10751948366124053899968401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 7167965577416035933312267 10751948366124053899968401)
                ·
                  refine ⟨8063961274593040424976301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10751948366124053899968401 8063961274593040424976301)
                  ·
                    refine ⟨3023985477972390159366113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8063961274593040424976301 3023985477972390159366113)
                    ·
                      refine ⟨2267989108479292619524585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3023985477972390159366113 2267989108479292619524585)
                      ·
                        rfl

theorem cell23_4416893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 2, 4, 1, 2, 3, 2].length) (baseStart_4416893 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416893 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416893 prefixEnd_4416893 := by exact prefixLift 4416893
  have htrace : WordTrace (prefixWord ++ tailWord_4416893) baseStart_4416893 baseEnd_4416893 := by
    simpa [prefixWord, tailWord_4416893, baseEnd_4416893] using wordTrace_append hprefix tailTrace_4416893
  have hstable : (prefixWord ++ tailWord_4416893).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416893).length < 2 ^ (prefixWord ++ tailWord_4416893).sum := by decide
  have hdescent : baseEnd_4416893 < baseStart_4416893 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416899 : List Nat := [1, 1, 1, 3, 5, 1, 1, 1, 3, 6]
def baseStart_4416899 : Nat := 118140960795 + 4416899 * 2 ^ 59
def prefixEnd_4416899 : Nat := 4983230072969 + 3 ^ 40 * 4416899 * 2
def baseEnd_4416899 : Nat := 755997396454406532016519

theorem tailTrace_4416899 : CollatzResearch.WordTrace tailWord_4416899 prefixEnd_4416899 755997396454406532016519 := by
  unfold tailWord_4416899
  simp only [CollatzResearch.WordTrace]
  refine ⟨161097541225336744137733751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107398360816891162758489167 161097541225336744137733751)
  ·
    refine ⟨241646311838005116206600627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161097541225336744137733751 241646311838005116206600627)
    ·
      refine ⟨362469467757007674309900941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241646311838005116206600627 362469467757007674309900941)
      ·
        refine ⟨135926050408877877866212853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 362469467757007674309900941 135926050408877877866212853)
        ·
          refine ⟨12743067225832301049957455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 135926050408877877866212853 12743067225832301049957455)
          ·
            refine ⟨19114600838748451574936183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 12743067225832301049957455 19114600838748451574936183)
            ·
              refine ⟨28671901258122677362404275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 19114600838748451574936183 28671901258122677362404275)
              ·
                refine ⟨43007851887184016043606413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 28671901258122677362404275 43007851887184016043606413)
                ·
                  refine ⟨16127944457694006016352405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 43007851887184016043606413 16127944457694006016352405)
                  ·
                    refine ⟨755997396454406532016519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 16127944457694006016352405 755997396454406532016519)
                    ·
                      rfl

theorem cell23_4416899_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 1, 1, 1, 3, 6].length) (baseStart_4416899 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416899 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416899 prefixEnd_4416899 := by exact prefixLift 4416899
  have htrace : WordTrace (prefixWord ++ tailWord_4416899) baseStart_4416899 baseEnd_4416899 := by
    simpa [prefixWord, tailWord_4416899, baseEnd_4416899] using wordTrace_append hprefix tailTrace_4416899
  have hstable : (prefixWord ++ tailWord_4416899).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416899).length < 2 ^ (prefixWord ++ tailWord_4416899).sum := by decide
  have hdescent : baseEnd_4416899 < baseStart_4416899 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416899) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416903 : List Nat := [1, 1, 4, 2, 2, 3, 3, 1, 1, 5]
def baseStart_4416903 : Nat := 118140960795 + 4416903 * 2 ^ 59
def prefixEnd_4416903 : Nat := 4983230072969 + 3 ^ 40 * 4416903 * 2
def baseEnd_4416903 : Nat := 755998081095279193466513

theorem tailTrace_4416903 : CollatzResearch.WordTrace tailWord_4416903 prefixEnd_4416903 755998081095279193466513 := by
  unfold tailWord_4416903
  simp only [CollatzResearch.WordTrace]
  refine ⟨161097687117322252820879363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107398458078214835213919575 161097687117322252820879363)
  ·
    refine ⟨241646530675983379231319045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161097687117322252820879363 241646530675983379231319045)
    ·
      refine ⟨45308724501746883605872321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241646530675983379231319045 45308724501746883605872321)
      ·
        refine ⟨33981543376310162704404241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45308724501746883605872321 33981543376310162704404241)
        ·
          refine ⟨25486157532232622028303181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33981543376310162704404241 25486157532232622028303181)
          ·
            refine ⟨9557309074587233260613693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 25486157532232622028303181 9557309074587233260613693)
            ·
              refine ⟨3583990902970212472730135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 9557309074587233260613693 3583990902970212472730135)
              ·
                refine ⟨5375986354455318709095203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3583990902970212472730135 5375986354455318709095203)
                ·
                  refine ⟨8063979531682978063642805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5375986354455318709095203 8063979531682978063642805)
                  ·
                    refine ⟨755998081095279193466513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 8063979531682978063642805 755998081095279193466513)
                    ·
                      rfl

theorem cell23_4416903_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 1, 1, 5].length) (baseStart_4416903 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416903 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416903 prefixEnd_4416903 := by exact prefixLift 4416903
  have htrace : WordTrace (prefixWord ++ tailWord_4416903) baseStart_4416903 baseEnd_4416903 := by
    simpa [prefixWord, tailWord_4416903, baseEnd_4416903] using wordTrace_append hprefix tailTrace_4416903
  have hstable : (prefixWord ++ tailWord_4416903).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416903).length < 2 ^ (prefixWord ++ tailWord_4416903).sum := by decide
  have hdescent : baseEnd_4416903 < baseStart_4416903 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416903) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416919 : List Nat := [1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 4]
def baseStart_4416919 : Nat := 118140960795 + 4416919 * 2 ^ 59
def prefixEnd_4416919 : Nat := 4983230072969 + 3 ^ 40 * 4416919 * 2
def baseEnd_4416919 : Nat := 2268002458976309517799465

theorem tailTrace_4416919 : CollatzResearch.WordTrace tailWord_4416919 prefixEnd_4416919 2268002458976309517799465 := by
  unfold tailWord_4416919
  simp only [CollatzResearch.WordTrace]
  refine ⟨161098270685264287553461811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107398847123509525035641207 161098270685264287553461811)
  ·
    refine ⟨241647406027896431330192717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161098270685264287553461811 241647406027896431330192717)
    ·
      refine ⟨90617777260461161748822269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 241647406027896431330192717 90617777260461161748822269)
      ·
        refine ⟨33981666472672935655808351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 90617777260461161748822269 33981666472672935655808351)
        ·
          refine ⟨50972499709009403483712527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33981666472672935655808351 50972499709009403483712527)
          ·
            refine ⟨76458749563514105225568791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 50972499709009403483712527 76458749563514105225568791)
            ·
              refine ⟨114688124345271157838353187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76458749563514105225568791 114688124345271157838353187)
              ·
                refine ⟨172032186517906736757529781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114688124345271157838353187 172032186517906736757529781)
                ·
                  refine ⟨16128017486053756571018417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 172032186517906736757529781 16128017486053756571018417)
                  ·
                    refine ⟨12096013114540317428263813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16128017486053756571018417 12096013114540317428263813)
                    ·
                      refine ⟨2268002458976309517799465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12096013114540317428263813 2268002458976309517799465)
                      ·
                        rfl

theorem cell23_4416919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 1, 1, 5, 2, 4].length) (baseStart_4416919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416919 prefixEnd_4416919 := by exact prefixLift 4416919
  have htrace : WordTrace (prefixWord ++ tailWord_4416919) baseStart_4416919 baseEnd_4416919 := by
    simpa [prefixWord, tailWord_4416919, baseEnd_4416919] using wordTrace_append hprefix tailTrace_4416919
  have hstable : (prefixWord ++ tailWord_4416919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416919).length < 2 ^ (prefixWord ++ tailWord_4416919).sum := by decide
  have hdescent : baseEnd_4416919 < baseStart_4416919 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4416957 : List Nat := [1, 4, 1, 2, 2, 1, 4, 3, 1, 2, 2]
def baseStart_4416957 : Nat := 118140960795 + 4416957 * 2 ^ 59
def prefixEnd_4416957 : Nat := 4983230072969 + 3 ^ 40 * 4416957 * 2
def baseEnd_4416957 : Nat := 2268021971241180369124291

theorem tailTrace_4416957 : CollatzResearch.WordTrace tailWord_4416957 prefixEnd_4416957 2268021971241180369124291 := by
  unfold tailWord_4416957
  simp only [CollatzResearch.WordTrace]
  refine ⟨161099656659126620043345125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107399771106084413362230083 161099656659126620043345125)
  ·
    refine ⟨30206185623586241258127211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161099656659126620043345125 30206185623586241258127211)
    ·
      refine ⟨45309278435379361887190817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30206185623586241258127211 45309278435379361887190817)
      ·
        refine ⟨33981958826534521415393113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45309278435379361887190817 33981958826534521415393113)
        ·
          refine ⟨25486469119900891061544835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 33981958826534521415393113 25486469119900891061544835)
          ·
            refine ⟨38229703679851336592317253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25486469119900891061544835 38229703679851336592317253)
            ·
              refine ⟨7168069439972125611059485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38229703679851336592317253 7168069439972125611059485)
              ·
                refine ⟨2688026039989547104147307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 7168069439972125611059485 2688026039989547104147307)
                ·
                  refine ⟨4032039059984320656220961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688026039989547104147307 4032039059984320656220961)
                  ·
                    refine ⟨3024029294988240492165721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4032039059984320656220961 3024029294988240492165721)
                    ·
                      refine ⟨2268021971241180369124291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024029294988240492165721 2268021971241180369124291)
                      ·
                        rfl

theorem cell23_4416957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 4, 3, 1, 2, 2].length) (baseStart_4416957 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4416957 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4416957 prefixEnd_4416957 := by exact prefixLift 4416957
  have htrace : WordTrace (prefixWord ++ tailWord_4416957) baseStart_4416957 baseEnd_4416957 := by
    simpa [prefixWord, tailWord_4416957, baseEnd_4416957] using wordTrace_append hprefix tailTrace_4416957
  have hstable : (prefixWord ++ tailWord_4416957).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4416957).length < 2 ^ (prefixWord ++ tailWord_4416957).sum := by decide
  have hdescent : baseEnd_4416957 < baseStart_4416957 := by decide
  rcases family_descends (prefixWord ++ tailWord_4416957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417000 : List Nat := [2, 1, 4, 1, 1, 2, 4, 2, 1, 3, 2]
def baseStart_4417000 : Nat := 118140960795 + 4417000 * 2 ^ 59
def prefixEnd_4417000 : Nat := 4983230072969 + 3 ^ 40 * 4417000 * 2
def baseEnd_4417000 : Nat := 2268044050909323700886593

theorem tailTrace_4417000 : CollatzResearch.WordTrace tailWord_4417000 prefixEnd_4417000 2268044050909323700886593 := by
  unfold tailWord_4417000
  simp only [CollatzResearch.WordTrace]
  refine ⟨80550612498985419193580227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107400816665313892258106969 80550612498985419193580227)
  ·
    refine ⟨120825918748478128790370341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80550612498985419193580227 120825918748478128790370341)
    ·
      refine ⟨22654859765339649148194439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 120825918748478128790370341 22654859765339649148194439)
      ·
        refine ⟨33982289648009473722291659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 22654859765339649148194439 33982289648009473722291659)
        ·
          refine ⟨50973434472014210583437489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33982289648009473722291659 50973434472014210583437489)
          ·
            refine ⟨38230075854010657937578117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50973434472014210583437489 38230075854010657937578117)
            ·
              refine ⟨7168139222626998363295897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 38230075854010657937578117 7168139222626998363295897)
              ·
                refine ⟨5376104416970248772471923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 7168139222626998363295897 5376104416970248772471923)
                ·
                  refine ⟨8064156625455373158707885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5376104416970248772471923 8064156625455373158707885)
                  ·
                    refine ⟨3024058734545764934515457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8064156625455373158707885 3024058734545764934515457)
                    ·
                      refine ⟨2268044050909323700886593, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024058734545764934515457 2268044050909323700886593)
                      ·
                        rfl

theorem cell23_4417000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 4, 2, 1, 3, 2].length) (baseStart_4417000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417000 prefixEnd_4417000 := by exact prefixLift 4417000
  have htrace : WordTrace (prefixWord ++ tailWord_4417000) baseStart_4417000 baseEnd_4417000 := by
    simpa [prefixWord, tailWord_4417000, baseEnd_4417000] using wordTrace_append hprefix tailTrace_4417000
  have hstable : (prefixWord ++ tailWord_4417000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417000).length < 2 ^ (prefixWord ++ tailWord_4417000).sum := by decide
  have hdescent : baseEnd_4417000 < baseStart_4417000 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417016 : List Nat := [2, 1, 2, 1, 1, 6, 1, 1, 2, 1, 5]
def baseStart_4417016 : Nat := 118140960795 + 4417016 * 2 ^ 59
def prefixEnd_4417016 : Nat := 4983230072969 + 3 ^ 40 * 4417016 * 2
def baseEnd_4417016 : Nat := 2268052266599795638286519

theorem tailTrace_4417016 : CollatzResearch.WordTrace tailWord_4417016 prefixEnd_4417016 2268052266599795638286519 := by
  unfold tailWord_4417016
  simp only [CollatzResearch.WordTrace]
  refine ⟨80550904282956436559871451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107401205710608582079828601 80550904282956436559871451)
  ·
    refine ⟨120826356424434654839807177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 80550904282956436559871451 120826356424434654839807177)
    ·
      refine ⟨90619767318325991129855383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 120826356424434654839807177 90619767318325991129855383)
      ·
        refine ⟨135929650977488986694783075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90619767318325991129855383 135929650977488986694783075)
        ·
          refine ⟨203894476466233480042174613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 135929650977488986694783075 203894476466233480042174613)
          ·
            refine ⟨9557553584354694376976935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 203894476466233480042174613 9557553584354694376976935)
            ·
              refine ⟨14336330376532041565465403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9557553584354694376976935 14336330376532041565465403)
              ·
                refine ⟨21504495564798062348198105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14336330376532041565465403 21504495564798062348198105)
                ·
                  refine ⟨16128371673598546761148579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 21504495564798062348198105 16128371673598546761148579)
                  ·
                    refine ⟨24192557510397820141722869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16128371673598546761148579 24192557510397820141722869)
                    ·
                      refine ⟨2268052266599795638286519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24192557510397820141722869 2268052266599795638286519)
                      ·
                        rfl

theorem cell23_4417016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 6, 1, 1, 2, 1, 5].length) (baseStart_4417016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417016 prefixEnd_4417016 := by exact prefixLift 4417016
  have htrace : WordTrace (prefixWord ++ tailWord_4417016) baseStart_4417016 baseEnd_4417016 := by
    simpa [prefixWord, tailWord_4417016, baseEnd_4417016] using wordTrace_append hprefix tailTrace_4417016
  have hstable : (prefixWord ++ tailWord_4417016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417016).length < 2 ^ (prefixWord ++ tailWord_4417016).sum := by decide
  have hdescent : baseEnd_4417016 < baseStart_4417016 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417029 : List Nat := [1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9]
def baseStart_4417029 : Nat := 118140960795 + 4417029 * 2 ^ 59
def prefixEnd_4417029 : Nat := 4983230072969 + 3 ^ 40 * 4417029 * 2
def baseEnd_4417029 : Nat := 2268058941848304087423959

theorem tailTrace_4417029 : CollatzResearch.WordTrace tailWord_4417029 prefixEnd_4417029 2268058941848304087423959 := by
  unfold tailWord_4417029
  simp only [CollatzResearch.WordTrace]
  refine ⟨161102282714865776339966141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107401521809910517559977427 161102282714865776339966141)
  ·
    refine ⟨60413356018074666127487303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 161102282714865776339966141 60413356018074666127487303)
    ·
      refine ⟨90620034027111999191230955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60413356018074666127487303 90620034027111999191230955)
      ·
        refine ⟨135930051040667998786846433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90620034027111999191230955 135930051040667998786846433)
        ·
          refine ⟨101947538280500999090134825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135930051040667998786846433 101947538280500999090134825)
          ·
            refine ⟨76460653710375749317601119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101947538280500999090134825 76460653710375749317601119)
            ·
              refine ⟨114690980565563623976401679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 76460653710375749317601119 114690980565563623976401679)
              ·
                refine ⟨172036470848345435964602519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 114690980565563623976401679 172036470848345435964602519)
                ·
                  refine ⟨258054706272518153946903779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 172036470848345435964602519 258054706272518153946903779)
                  ·
                    refine ⟨387082059408777230920355669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 258054706272518153946903779 387082059408777230920355669)
                    ·
                      refine ⟨2268058941848304087423959, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 387082059408777230920355669 2268058941848304087423959)
                      ·
                        rfl

theorem cell23_4417029_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 1, 1, 1, 1, 9].length) (baseStart_4417029 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417029 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417029 prefixEnd_4417029 := by exact prefixLift 4417029
  have htrace : WordTrace (prefixWord ++ tailWord_4417029) baseStart_4417029 baseEnd_4417029 := by
    simpa [prefixWord, tailWord_4417029, baseEnd_4417029] using wordTrace_append hprefix tailTrace_4417029
  have hstable : (prefixWord ++ tailWord_4417029).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417029).length < 2 ^ (prefixWord ++ tailWord_4417029).sum := by decide
  have hdescent : baseEnd_4417029 < baseStart_4417029 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417029) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417123 : List Nat := [1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 3]
def baseStart_4417123 : Nat := 118140960795 + 4417123 * 2 ^ 59
def prefixEnd_4417123 : Nat := 4983230072969 + 3 ^ 40 * 4417123 * 2
def baseEnd_4417123 : Nat := 2268107209029826719648527

theorem tailTrace_4417123 : CollatzResearch.WordTrace tailWord_4417123 prefixEnd_4417123 2268107209029826719648527 := by
  unfold tailWord_4417123
  simp only [CollatzResearch.WordTrace]
  refine ⟨161105711176525230393888023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107403807451016820262592015 161105711176525230393888023)
  ·
    refine ⟨241658566764787845590832035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161105711176525230393888023 241658566764787845590832035)
    ·
      refine ⟨362487850147181768386248053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241658566764787845590832035 362487850147181768386248053)
      ·
        refine ⟨33983235951298290786210755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 362487850147181768386248053 33983235951298290786210755)
        ·
          refine ⟨50974853926947436179316133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33983235951298290786210755 50974853926947436179316133)
          ·
            refine ⟨9557785111302644283621775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 50974853926947436179316133 9557785111302644283621775)
            ·
              refine ⟨14336677666953966425432663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 9557785111302644283621775 14336677666953966425432663)
              ·
                refine ⟨21505016500430949638148995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14336677666953966425432663 21505016500430949638148995)
                ·
                  refine ⟨32257524750646424457223493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 21505016500430949638148995 32257524750646424457223493)
                  ·
                    refine ⟨6048285890746204585729405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 32257524750646424457223493 6048285890746204585729405)
                    ·
                      refine ⟨2268107209029826719648527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6048285890746204585729405 2268107209029826719648527)
                      ·
                        rfl

theorem cell23_4417123_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 4, 1, 1, 1, 4, 3].length) (baseStart_4417123 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417123 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417123 prefixEnd_4417123 := by exact prefixLift 4417123
  have htrace : WordTrace (prefixWord ++ tailWord_4417123) baseStart_4417123 baseEnd_4417123 := by
    simpa [prefixWord, tailWord_4417123, baseEnd_4417123] using wordTrace_append hprefix tailTrace_4417123
  have hstable : (prefixWord ++ tailWord_4417123).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417123).length < 2 ^ (prefixWord ++ tailWord_4417123).sum := by decide
  have hdescent : baseEnd_4417123 < baseStart_4417123 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417123) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417163 : List Nat := [1, 1, 1, 1, 4, 1, 3, 1, 3, 5, 2]
def baseStart_4417163 : Nat := 118140960795 + 4417163 * 2 ^ 59
def prefixEnd_4417163 : Nat := 4983230072969 + 3 ^ 40 * 4417163 * 2
def baseEnd_4417163 : Nat := 2268127748256006563148343

theorem tailTrace_4417163 : CollatzResearch.WordTrace tailWord_4417163 prefixEnd_4417163 2268127748256006563148343 := by
  unfold tailWord_4417163
  simp only [CollatzResearch.WordTrace]
  refine ⟨161107170096380317225344143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107404780064253544816896095 161107170096380317225344143)
  ·
    refine ⟨241660755144570475838016215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161107170096380317225344143 241660755144570475838016215)
    ·
      refine ⟨362491132716855713757024323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241660755144570475838016215 362491132716855713757024323)
      ·
        refine ⟨543736699075283570635536485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 362491132716855713757024323 543736699075283570635536485)
        ·
          refine ⟨101950631076615669494163091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 543736699075283570635536485 101950631076615669494163091)
          ·
            refine ⟨152925946614923504241244637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101950631076615669494163091 152925946614923504241244637)
            ·
              refine ⟨57347229980596314090466739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 152925946614923504241244637 57347229980596314090466739)
              ·
                refine ⟨86020844970894471135700109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 57347229980596314090466739 86020844970894471135700109)
                ·
                  refine ⟨32257816864085426675887541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 86020844970894471135700109 32257816864085426675887541)
                  ·
                    refine ⟨3024170331008008750864457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 32257816864085426675887541 3024170331008008750864457)
                    ·
                      refine ⟨2268127748256006563148343, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024170331008008750864457 2268127748256006563148343)
                      ·
                        rfl

theorem cell23_4417163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 1, 3, 5, 2].length) (baseStart_4417163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417163 prefixEnd_4417163 := by exact prefixLift 4417163
  have htrace : WordTrace (prefixWord ++ tailWord_4417163) baseStart_4417163 baseEnd_4417163 := by
    simpa [prefixWord, tailWord_4417163, baseEnd_4417163] using wordTrace_append hprefix tailTrace_4417163
  have hstable : (prefixWord ++ tailWord_4417163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417163).length < 2 ^ (prefixWord ++ tailWord_4417163).sum := by decide
  have hdescent : baseEnd_4417163 < baseStart_4417163 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417193 : List Nat := [1, 2, 1, 1, 1, 1, 2, 2, 4, 6, 2]
def baseStart_4417193 : Nat := 118140960795 + 4417193 * 2 ^ 59
def prefixEnd_4417193 : Nat := 4983230072969 + 3 ^ 40 * 4417193 * 2
def baseEnd_4417193 : Nat := 2268143152675641445773205

theorem tailTrace_4417193 : CollatzResearch.WordTrace tailWord_4417193 prefixEnd_4417193 2268143152675641445773205 := by
  unfold tailWord_4417193
  simp only [CollatzResearch.WordTrace]
  refine ⟨161108264286271632348936233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107405509524181088232624155 161108264286271632348936233)
  ·
    refine ⟨120831198214703724261702175, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 161108264286271632348936233 120831198214703724261702175)
    ·
      refine ⟨181246797322055586392553263, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 120831198214703724261702175 181246797322055586392553263)
      ·
        refine ⟨271870195983083379588829895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 181246797322055586392553263 271870195983083379588829895)
        ·
          refine ⟨407805293974625069383244843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 271870195983083379588829895 407805293974625069383244843)
          ·
            refine ⟨611707940961937604074867265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 407805293974625069383244843 611707940961937604074867265)
            ·
              refine ⟨458780955721453203056150449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 611707940961937604074867265 458780955721453203056150449)
              ·
                refine ⟨344085716791089902292112837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 458780955721453203056150449 344085716791089902292112837)
                ·
                  refine ⟨64516071898329356679771157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 344085716791089902292112837 64516071898329356679771157)
                  ·
                    refine ⟨3024190870234188594364273, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 64516071898329356679771157 3024190870234188594364273)
                    ·
                      refine ⟨2268143152675641445773205, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024190870234188594364273 2268143152675641445773205)
                      ·
                        rfl

theorem cell23_4417193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 2, 4, 6, 2].length) (baseStart_4417193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417193 prefixEnd_4417193 := by exact prefixLift 4417193
  have htrace : WordTrace (prefixWord ++ tailWord_4417193) baseStart_4417193 baseEnd_4417193 := by
    simpa [prefixWord, tailWord_4417193, baseEnd_4417193] using wordTrace_append hprefix tailTrace_4417193
  have hstable : (prefixWord ++ tailWord_4417193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417193).length < 2 ^ (prefixWord ++ tailWord_4417193).sum := by decide
  have hdescent : baseEnd_4417193 < baseStart_4417193 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417197 : List Nat := [1, 5, 2, 1, 1, 1, 3, 2, 2, 3, 2]
def baseStart_4417197 : Nat := 118140960795 + 4417197 * 2 ^ 59
def prefixEnd_4417197 : Nat := 4983230072969 + 3 ^ 40 * 4417197 * 2
def baseEnd_4417197 : Nat := 2268145206598259430123187

theorem tailTrace_4417197 : CollatzResearch.WordTrace tailWord_4417197 prefixEnd_4417197 2268145206598259430123187 := by
  unfold tailWord_4417197
  simp only [CollatzResearch.WordTrace]
  refine ⟨161108410178257141032081845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107405606785504760688054563 161108410178257141032081845)
  ·
    refine ⟨15103913454211606971757673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 161108410178257141032081845 15103913454211606971757673)
    ·
      refine ⟨11327935090658705228818255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 15103913454211606971757673 11327935090658705228818255)
      ·
        refine ⟨16991902635988057843227383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 11327935090658705228818255 16991902635988057843227383)
        ·
          refine ⟨25487853953982086764841075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 16991902635988057843227383 25487853953982086764841075)
          ·
            refine ⟨38231780930973130147261613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25487853953982086764841075 38231780930973130147261613)
            ·
              refine ⟨14336917849114923805223105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38231780930973130147261613 14336917849114923805223105)
              ·
                refine ⟨10752688386836192853917329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 14336917849114923805223105 10752688386836192853917329)
                ·
                  refine ⟨8064516290127144640437997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 10752688386836192853917329 8064516290127144640437997)
                  ·
                    refine ⟨3024193608797679240164249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 8064516290127144640437997 3024193608797679240164249)
                    ·
                      refine ⟨2268145206598259430123187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 3024193608797679240164249 2268145206598259430123187)
                      ·
                        rfl

theorem cell23_4417197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 3, 2, 2, 3, 2].length) (baseStart_4417197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417197 prefixEnd_4417197 := by exact prefixLift 4417197
  have htrace : WordTrace (prefixWord ++ tailWord_4417197) baseStart_4417197 baseEnd_4417197 := by
    simpa [prefixWord, tailWord_4417197, baseEnd_4417197] using wordTrace_append hprefix tailTrace_4417197
  have hstable : (prefixWord ++ tailWord_4417197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417197).length < 2 ^ (prefixWord ++ tailWord_4417197).sum := by decide
  have hdescent : baseEnd_4417197 < baseStart_4417197 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417203 : List Nat := [1, 1, 1, 2, 3, 3, 1, 3, 4, 4]
def baseStart_4417203 : Nat := 118140960795 + 4417203 * 2 ^ 59
def prefixEnd_4417203 : Nat := 4983230072969 + 3 ^ 40 * 4417203 * 2
def baseEnd_4417203 : Nat := 756049429160728802216053

theorem tailTrace_4417203 : CollatzResearch.WordTrace tailWord_4417203 prefixEnd_4417203 756049429160728802216053 := by
  unfold tailWord_4417203
  simp only [CollatzResearch.WordTrace]
  refine ⟨161108629016235404056800263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107405752677490269371200175 161108629016235404056800263)
  ·
    refine ⟨241662943524353106085200395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161108629016235404056800263 241662943524353106085200395)
    ·
      refine ⟨362494415286529659127800593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 241662943524353106085200395 362494415286529659127800593)
      ·
        refine ⟨271870811464897244345850445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 362494415286529659127800593 271870811464897244345850445)
        ·
          refine ⟨101951554299336466629693917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 271870811464897244345850445 101951554299336466629693917)
          ·
            refine ⟨38231832862251174986135219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 101951554299336466629693917 38231832862251174986135219)
            ·
              refine ⟨57347749293376762479202829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38231832862251174986135219 57347749293376762479202829)
              ·
                refine ⟨21505405985016285929701061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57347749293376762479202829 21505405985016285929701061)
                ·
                  refine ⟨4032263622190553611818949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21505405985016285929701061 4032263622190553611818949)
                  ·
                    refine ⟨756049429160728802216053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4032263622190553611818949 756049429160728802216053)
                    ·
                      rfl

theorem cell23_4417203_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 3, 4, 4].length) (baseStart_4417203 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417203 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417203 prefixEnd_4417203 := by exact prefixLift 4417203
  have htrace : WordTrace (prefixWord ++ tailWord_4417203) baseStart_4417203 baseEnd_4417203 := by
    simpa [prefixWord, tailWord_4417203, baseEnd_4417203] using wordTrace_append hprefix tailTrace_4417203
  have hstable : (prefixWord ++ tailWord_4417203).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417203).length < 2 ^ (prefixWord ++ tailWord_4417203).sum := by decide
  have hdescent : baseEnd_4417203 < baseStart_4417203 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417203) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417213 : List Nat := [1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 5]
def baseStart_4417213 : Nat := 118140960795 + 4417213 * 2 ^ 59
def prefixEnd_4417213 : Nat := 4983230072969 + 3 ^ 40 * 4417213 * 2
def baseEnd_4417213 : Nat := 2268153422288731367523113

theorem tailTrace_4417213 : CollatzResearch.WordTrace tailWord_4417213 prefixEnd_4417213 2268153422288731367523113 := by
  unfold tailWord_4417213
  simp only [CollatzResearch.WordTrace]
  refine ⟨161108993746199175764664293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107405995830799450509776195 161108993746199175764664293)
  ·
    refine ⟨30207936327412345455874555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 161108993746199175764664293 30207936327412345455874555)
    ·
      refine ⟨45311904491118518183811833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30207936327412345455874555 45311904491118518183811833)
      ·
        refine ⟨33983928368338888637858875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 45311904491118518183811833 33983928368338888637858875)
        ·
          refine ⟨50975892552508332956788313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 33983928368338888637858875 50975892552508332956788313)
          ·
            refine ⟨38231919414381249717591235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50975892552508332956788313 38231919414381249717591235)
            ·
              refine ⟨57347879121571874576386853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 38231919414381249717591235 57347879121571874576386853)
              ·
                refine ⟨10752727335294726483072535, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 57347879121571874576386853 10752727335294726483072535)
                ·
                  refine ⟨16129091002942089724608803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10752727335294726483072535 16129091002942089724608803)
                  ·
                    refine ⟨24193636504413134586913205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 16129091002942089724608803 24193636504413134586913205)
                    ·
                      refine ⟨2268153422288731367523113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 24193636504413134586913205 2268153422288731367523113)
                      ·
                        rfl

theorem cell23_4417213_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 4, 1, 1, 5].length) (baseStart_4417213 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417213 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417213 prefixEnd_4417213 := by exact prefixLift 4417213
  have htrace : WordTrace (prefixWord ++ tailWord_4417213) baseStart_4417213 baseEnd_4417213 := by
    simpa [prefixWord, tailWord_4417213, baseEnd_4417213] using wordTrace_append hprefix tailTrace_4417213
  have hstable : (prefixWord ++ tailWord_4417213).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417213).length < 2 ^ (prefixWord ++ tailWord_4417213).sum := by decide
  have hdescent : baseEnd_4417213 < baseStart_4417213 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417213) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417223 : List Nat := [1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 4]
def baseStart_4417223 : Nat := 118140960795 + 4417223 * 2 ^ 59
def prefixEnd_4417223 : Nat := 4983230072969 + 3 ^ 40 * 4417223 * 2
def baseEnd_4417223 : Nat := 2268158557095276328398067

theorem tailTrace_4417223 : CollatzResearch.WordTrace tailWord_4417223 prefixEnd_4417223 2268158557095276328398067 := by
  unfold tailWord_4417223
  simp only [CollatzResearch.WordTrace]
  refine ⟨161109358476162947472528323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107406238984108631648352215 161109358476162947472528323)
  ·
    refine ⟨241664037714244421208792485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161109358476162947472528323 241664037714244421208792485)
    ·
      refine ⟨45312007071420828976648591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 241664037714244421208792485 45312007071420828976648591)
      ·
        refine ⟨67968010607131243464972887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45312007071420828976648591 67968010607131243464972887)
        ·
          refine ⟨101952015910696865197459331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 67968010607131243464972887 101952015910696865197459331)
          ·
            refine ⟨152928023866045297796188997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 101952015910696865197459331 152928023866045297796188997)
            ·
              refine ⟨28674004474883493336785437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 152928023866045297796188997 28674004474883493336785437)
              ·
                refine ⟨10752751678081310001294539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 28674004474883493336785437 10752751678081310001294539)
                ·
                  refine ⟨16129127517121965001941809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 10752751678081310001294539 16129127517121965001941809)
                  ·
                    refine ⟨12096845637841473751456357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 16129127517121965001941809 12096845637841473751456357)
                    ·
                      refine ⟨2268158557095276328398067, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 12096845637841473751456357 2268158557095276328398067)
                      ·
                        rfl

theorem cell23_4417223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_4417223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417223 prefixEnd_4417223 := by exact prefixLift 4417223
  have htrace : WordTrace (prefixWord ++ tailWord_4417223) baseStart_4417223 baseEnd_4417223 := by
    simpa [prefixWord, tailWord_4417223, baseEnd_4417223] using wordTrace_append hprefix tailTrace_4417223
  have hstable : (prefixWord ++ tailWord_4417223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417223).length < 2 ^ (prefixWord ++ tailWord_4417223).sum := by decide
  have hdescent : baseEnd_4417223 < baseStart_4417223 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417230 : List Nat := [4, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3]
def baseStart_4417230 : Nat := 118140960795 + 4417230 * 2 ^ 59
def prefixEnd_4417230 : Nat := 4983230072969 + 3 ^ 40 * 4417230 * 2
def baseEnd_4417230 : Nat := 2268162151459857801010535

theorem tailTrace_4417230 : CollatzResearch.WordTrace tailWord_4417230 prefixEnd_4417230 2268162151459857801010535 := by
  unfold tailWord_4417230
  simp only [CollatzResearch.WordTrace]
  refine ⟨20138701723392198458504143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 107406409191425058445355429 20138701723392198458504143)
  ·
    refine ⟨30208052585088297687756215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 20138701723392198458504143 30208052585088297687756215)
    ·
      refine ⟨45312078877632446531634323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 30208052585088297687756215 45312078877632446531634323)
      ·
        refine ⟨67968118316448669797451485, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 45312078877632446531634323 67968118316448669797451485)
        ·
          refine ⟨25488044368668251174044307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 67968118316448669797451485 25488044368668251174044307)
          ·
            refine ⟨38232066553002376761066461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 25488044368668251174044307 38232066553002376761066461)
            ·
              refine ⟨14337024957375891285399923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 38232066553002376761066461 14337024957375891285399923)
              ·
                refine ⟨21505537436063836928099885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 14337024957375891285399923 21505537436063836928099885)
                ·
                  refine ⟨8064576538523938848037457, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 21505537436063836928099885 8064576538523938848037457)
                  ·
                    refine ⟨6048432403892954136028093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8064576538523938848037457 6048432403892954136028093)
                    ·
                      refine ⟨2268162151459857801010535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6048432403892954136028093 2268162151459857801010535)
                      ·
                        rfl

theorem cell23_4417230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 3, 1, 3, 2, 3].length) (baseStart_4417230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417230 prefixEnd_4417230 := by exact prefixLift 4417230
  have htrace : WordTrace (prefixWord ++ tailWord_4417230) baseStart_4417230 baseEnd_4417230 := by
    simpa [prefixWord, tailWord_4417230, baseEnd_4417230] using wordTrace_append hprefix tailTrace_4417230
  have hstable : (prefixWord ++ tailWord_4417230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417230).length < 2 ^ (prefixWord ++ tailWord_4417230).sum := by decide
  have hdescent : baseEnd_4417230 < baseStart_4417230 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417247 : List Nat := [1, 1, 2, 3, 2, 2, 5, 1, 1, 2, 3]
def baseStart_4417247 : Nat := 118140960795 + 4417247 * 2 ^ 59
def prefixEnd_4417247 : Nat := 4983230072969 + 3 ^ 40 * 4417247 * 2
def baseEnd_4417247 : Nat := 2268170880630984234497957

theorem tailTrace_4417247 : CollatzResearch.WordTrace tailWord_4417247 prefixEnd_4417247 2268170880630984234497957 := by
  unfold tailWord_4417247
  simp only [CollatzResearch.WordTrace]
  refine ⟨161110233828075999571401995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107406822552050666380934663 161110233828075999571401995)
  ·
    refine ⟨241665350742113999357102993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161110233828075999571401995 241665350742113999357102993)
    ·
      refine ⟨181249013056585499517827245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 241665350742113999357102993 181249013056585499517827245)
      ·
        refine ⟨67968379896219562319185217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 181249013056585499517827245 67968379896219562319185217)
        ·
          refine ⟨50976284922164671739388913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 67968379896219562319185217 50976284922164671739388913)
          ·
            refine ⟨38232213691623503804541685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 50976284922164671739388913 38232213691623503804541685)
            ·
              refine ⟨3584270033589703481675783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 38232213691623503804541685 3584270033589703481675783)
              ·
                refine ⟨5376405050384555222513675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 3584270033589703481675783 5376405050384555222513675)
                ·
                  refine ⟨8064607575576832833770513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 5376405050384555222513675 8064607575576832833770513)
                  ·
                    refine ⟨6048455681682624625327885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 8064607575576832833770513 6048455681682624625327885)
                    ·
                      refine ⟨2268170880630984234497957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6048455681682624625327885 2268170880630984234497957)
                      ·
                        rfl

theorem cell23_4417247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 5, 1, 1, 2, 3].length) (baseStart_4417247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417247 prefixEnd_4417247 := by exact prefixLift 4417247
  have htrace : WordTrace (prefixWord ++ tailWord_4417247) baseStart_4417247 baseEnd_4417247 := by
    simpa [prefixWord, tailWord_4417247, baseEnd_4417247] using wordTrace_append hprefix tailTrace_4417247
  have hstable : (prefixWord ++ tailWord_4417247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417247).length < 2 ^ (prefixWord ++ tailWord_4417247).sum := by decide
  have hdescent : baseEnd_4417247 < baseStart_4417247 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417255 : List Nat := [1, 1, 5, 4, 2, 1, 2, 2, 1, 1, 3]
def baseStart_4417255 : Nat := 118140960795 + 4417255 * 2 ^ 59
def prefixEnd_4417255 : Nat := 4983230072969 + 3 ^ 40 * 4417255 * 2
def baseEnd_4417255 : Nat := 2268174988476220203197921

theorem tailTrace_4417255 : CollatzResearch.WordTrace tailWord_4417255 prefixEnd_4417255 2268174988476220203197921 := by
  unfold tailWord_4417255
  simp only [CollatzResearch.WordTrace]
  refine ⟨161110525612047016937693219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 107407017074698011291795479 161110525612047016937693219)
  ·
    refine ⟨241665788418070525406539829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 161110525612047016937693219 241665788418070525406539829)
    ·
      refine ⟨22656167664194111756863109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 241665788418070525406539829 22656167664194111756863109)
      ·
        refine ⟨4248031437036395954411833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 22656167664194111756863109 4248031437036395954411833)
        ·
          refine ⟨3186023577777296965808875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4248031437036395954411833 3186023577777296965808875)
          ·
            refine ⟨4779035366665945448713313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3186023577777296965808875 4779035366665945448713313)
            ·
              refine ⟨3584276524999459086534985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 4779035366665945448713313 3584276524999459086534985)
              ·
                refine ⟨2688207393749594314901239, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 3584276524999459086534985 2688207393749594314901239)
                ·
                  refine ⟨4032311090624391472351859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2688207393749594314901239 4032311090624391472351859)
                  ·
                    refine ⟨6048466635936587208527789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4032311090624391472351859 6048466635936587208527789)
                    ·
                      refine ⟨2268174988476220203197921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6048466635936587208527789 2268174988476220203197921)
                      ·
                        rfl

theorem cell23_4417255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 2, 1, 2, 2, 1, 1, 3].length) (baseStart_4417255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417255 prefixEnd_4417255 := by exact prefixLift 4417255
  have htrace : WordTrace (prefixWord ++ tailWord_4417255) baseStart_4417255 baseEnd_4417255 := by
    simpa [prefixWord, tailWord_4417255, baseEnd_4417255] using wordTrace_append hprefix tailTrace_4417255
  have hstable : (prefixWord ++ tailWord_4417255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417255).length < 2 ^ (prefixWord ++ tailWord_4417255).sum := by decide
  have hdescent : baseEnd_4417255 < baseStart_4417255 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_4417260 : List Nat := [2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 3]
def baseStart_4417260 : Nat := 118140960795 + 4417260 * 2 ^ 59
def prefixEnd_4417260 : Nat := 4983230072969 + 3 ^ 40 * 4417260 * 2
def baseEnd_4417260 : Nat := 2268177555879492683635397

theorem tailTrace_4417260 : CollatzResearch.WordTrace tailWord_4417260 prefixEnd_4417260 2268177555879492683635397 := by
  unfold tailWord_4417260
  simp only [CollatzResearch.WordTrace]
  refine ⟨80555353988514451395812617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 107407138651352601861083489 80555353988514451395812617)
  ·
    refine ⟨60416515491385838546859463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 80555353988514451395812617 60416515491385838546859463)
    ·
      refine ⟨90624773237078757820289195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 60416515491385838546859463 90624773237078757820289195)
      ·
        refine ⟨135937159855618136730433793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 90624773237078757820289195 135937159855618136730433793)
        ·
          refine ⟨101952869891713602547825345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 135937159855618136730433793 101952869891713602547825345)
          ·
            refine ⟨76464652418785201910869009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 101952869891713602547825345 76464652418785201910869009)
            ·
              refine ⟨57348489314088901433151757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 76464652418785201910869009 57348489314088901433151757)
              ·
                refine ⟨21505683492783338037431909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 57348489314088901433151757 21505683492783338037431909)
                ·
                  refine ⟨4032315654896875882018483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 21505683492783338037431909 4032315654896875882018483)
                  ·
                    refine ⟨6048473482345313823027725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4032315654896875882018483 6048473482345313823027725)
                    ·
                      refine ⟨2268177555879492683635397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 6048473482345313823027725 2268177555879492683635397)
                      ·
                        rfl

theorem cell23_4417260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 4, 1, 3].length) (baseStart_4417260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_4417260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_4417260 prefixEnd_4417260 := by exact prefixLift 4417260
  have htrace : WordTrace (prefixWord ++ tailWord_4417260) baseStart_4417260 baseEnd_4417260 := by
    simpa [prefixWord, tailWord_4417260, baseEnd_4417260] using wordTrace_append hprefix tailTrace_4417260
  have hstable : (prefixWord ++ tailWord_4417260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_4417260).length < 2 ^ (prefixWord ++ tailWord_4417260).sum := by decide
  have hdescent : baseEnd_4417260 < baseStart_4417260 := by decide
  rcases family_descends (prefixWord ++ tailWord_4417260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
