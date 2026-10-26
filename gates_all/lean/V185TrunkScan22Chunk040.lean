import V185TrunkScan22Chunk039

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_358224 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 2, 5]
def baseStart_358224 : Nat := 118140960795 + 358224 * 2 ^ 59
def prefixEnd_358224 : Nat := 4983230072969 + 3 ^ 40 * 358224 * 2
def baseEnd_358224 : Nat := 122627395984207787101709

theorem tailTrace_358224 : CollatzResearch.WordTrace tailWord_358224 prefixEnd_358224 122627395984207787101709 := by
  unfold tailWord_358224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6532751327111551316768863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8710335102815401755691817 6532751327111551316768863)
  ·
    refine ⟨9799126990667326975153295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6532751327111551316768863 9799126990667326975153295)
    ·
      refine ⟨14698690486000990462729943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9799126990667326975153295 14698690486000990462729943)
      ·
        refine ⟨22048035729001485694094915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14698690486000990462729943 22048035729001485694094915)
        ·
          refine ⟨33072053593502228541142373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22048035729001485694094915 33072053593502228541142373)
          ·
            refine ⟨6201010048781667851464195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33072053593502228541142373 6201010048781667851464195)
            ·
              refine ⟨9301515073172501777196293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6201010048781667851464195 9301515073172501777196293)
              ·
                refine ⟨1744034076219844083224305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9301515073172501777196293 1744034076219844083224305)
                ·
                  refine ⟨1308025557164883062418229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1744034076219844083224305 1308025557164883062418229)
                  ·
                    refine ⟨122627395984207787101709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1308025557164883062418229 122627395984207787101709)
                    ·
                      rfl

theorem cell22_358224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 5].length) (baseStart_358224 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358224 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358224 prefixEnd_358224 := by exact prefixLift 358224
  have htrace : WordTrace (prefixWord ++ tailWord_358224) baseStart_358224 baseEnd_358224 := by
    simpa [prefixWord, tailWord_358224, baseEnd_358224] using wordTrace_append hprefix tailTrace_358224
  have hstable : (prefixWord ++ tailWord_358224).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358224).length < 2 ^ (prefixWord ++ tailWord_358224).sum := by decide
  have hdescent : baseEnd_358224 < baseStart_358224 := by decide
  rcases family_descends (prefixWord ++ tailWord_358224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358226 : List Nat := [3, 2, 2, 1, 1, 3, 1, 4, 5]
def baseStart_358226 : Nat := 118140960795 + 358226 * 2 ^ 59
def prefixEnd_358226 : Nat := 4983230072969 + 3 ^ 40 * 358226 * 2
def baseEnd_358226 : Nat := 40876026875026816183901

theorem tailTrace_358226 : CollatzResearch.WordTrace tailWord_358226 prefixEnd_358226 40876026875026816183901 := by
  unfold tailWord_358226
  simp only [CollatzResearch.WordTrace]
  refine ⟨3266393900053964243777633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8710383733477237983407021 3266393900053964243777633)
  ·
    refine ⟨2449795425040473182833225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3266393900053964243777633 2449795425040473182833225)
    ·
      refine ⟨1837346568780354887124919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2449795425040473182833225 1837346568780354887124919)
      ·
        refine ⟨2756019853170532330687379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837346568780354887124919 2756019853170532330687379)
        ·
          refine ⟨4134029779755798496031069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2756019853170532330687379 4134029779755798496031069)
          ·
            refine ⟨1550261167408424436011651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4134029779755798496031069 1550261167408424436011651)
            ·
              refine ⟨2325391751112636654017477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550261167408424436011651 2325391751112636654017477)
              ·
                refine ⟨436010953333619372628277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2325391751112636654017477 436010953333619372628277)
                ·
                  refine ⟨40876026875026816183901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436010953333619372628277 40876026875026816183901)
                  ·
                    rfl

theorem cell22_358226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 1, 3, 1, 4, 5].length) (baseStart_358226 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358226 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358226 prefixEnd_358226 := by exact prefixLift 358226
  have htrace : WordTrace (prefixWord ++ tailWord_358226) baseStart_358226 baseEnd_358226 := by
    simpa [prefixWord, tailWord_358226, baseEnd_358226] using wordTrace_append hprefix tailTrace_358226
  have hstable : (prefixWord ++ tailWord_358226).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358226).length < 2 ^ (prefixWord ++ tailWord_358226).sum := by decide
  have hdescent : baseEnd_358226 < baseStart_358226 := by decide
  rcases family_descends (prefixWord ++ tailWord_358226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358256 : List Nat := [2, 1, 1, 1, 4, 1, 1, 6, 1, 4]
def baseStart_358256 : Nat := 118140960795 + 358256 * 2 ^ 59
def prefixEnd_358256 : Nat := 4983230072969 + 3 ^ 40 * 358256 * 2
def baseEnd_358256 : Nat := 122638350238170370301611

theorem tailTrace_358256 : CollatzResearch.WordTrace tailWord_358256 prefixEnd_358256 122638350238170370301611 := by
  unfold tailWord_358256
  simp only [CollatzResearch.WordTrace]
  refine ⟨6533334895053586049351311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8711113193404781399135081 6533334895053586049351311)
  ·
    refine ⟨9800002342580379074026967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6533334895053586049351311 9800002342580379074026967)
    ·
      refine ⟨14700003513870568611040451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9800002342580379074026967 14700003513870568611040451)
      ·
        refine ⟨22050005270805852916560677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14700003513870568611040451 22050005270805852916560677)
        ·
          refine ⟨4134375988276097421855127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22050005270805852916560677 4134375988276097421855127)
          ·
            refine ⟨6201563982414146132782691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4134375988276097421855127 6201563982414146132782691)
            ·
              refine ⟨9302345973621219199174037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6201563982414146132782691 9302345973621219199174037)
              ·
                refine ⟨436047467513494649961283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9302345973621219199174037 436047467513494649961283)
                ·
                  refine ⟨654071201270241974941925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436047467513494649961283 654071201270241974941925)
                  ·
                    refine ⟨122638350238170370301611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654071201270241974941925 122638350238170370301611)
                    ·
                      rfl

theorem cell22_358256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 6, 1, 4].length) (baseStart_358256 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358256 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358256 prefixEnd_358256 := by exact prefixLift 358256
  have htrace : WordTrace (prefixWord ++ tailWord_358256) baseStart_358256 baseEnd_358256 := by
    simpa [prefixWord, tailWord_358256, baseEnd_358256] using wordTrace_append hprefix tailTrace_358256
  have hstable : (prefixWord ++ tailWord_358256).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358256).length < 2 ^ (prefixWord ++ tailWord_358256).sum := by decide
  have hdescent : baseEnd_358256 < baseStart_358256 := by decide
  rcases family_descends (prefixWord ++ tailWord_358256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358294 : List Nat := [5, 3, 1, 1, 2, 1, 3, 1, 5]
def baseStart_358294 : Nat := 118140960795 + 358294 * 2 ^ 59
def prefixEnd_358294 : Nat := 4983230072969 + 3 ^ 40 * 358294 * 2
def baseEnd_358294 : Nat := 40883786138250312617165

theorem tailTrace_358294 : CollatzResearch.WordTrace tailWord_358294 prefixEnd_358294 40883786138250312617165 := by
  unfold tailWord_358294
  simp only [CollatzResearch.WordTrace]
  refine ⟨816753485248094036786621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8712037175979669725723957 816753485248094036786621)
  ·
    refine ⟨306282556968035263794983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 816753485248094036786621 306282556968035263794983)
    ·
      refine ⟨459423835452052895692475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306282556968035263794983 459423835452052895692475)
      ·
        refine ⟨689135753178079343538713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459423835452052895692475 689135753178079343538713)
        ·
          refine ⟨516851814883559507654035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689135753178079343538713 516851814883559507654035)
          ·
            refine ⟨775277722325339261481053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 516851814883559507654035 775277722325339261481053)
            ·
              refine ⟨290729145872002223055395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 775277722325339261481053 290729145872002223055395)
              ·
                refine ⟨436093718808003334583093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290729145872002223055395 436093718808003334583093)
                ·
                  refine ⟨40883786138250312617165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436093718808003334583093 40883786138250312617165)
                  ·
                    rfl

theorem cell22_358294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 1, 3, 1, 5].length) (baseStart_358294 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358294 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358294 prefixEnd_358294 := by exact prefixLift 358294
  have htrace : WordTrace (prefixWord ++ tailWord_358294) baseStart_358294 baseEnd_358294 := by
    simpa [prefixWord, tailWord_358294, baseEnd_358294] using wordTrace_append hprefix tailTrace_358294
  have hstable : (prefixWord ++ tailWord_358294).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358294).length < 2 ^ (prefixWord ++ tailWord_358294).sum := by decide
  have hdescent : baseEnd_358294 < baseStart_358294 := by decide
  rcases family_descends (prefixWord ++ tailWord_358294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358301 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 1, 6]
def baseStart_358301 : Nat := 118140960795 + 358301 * 2 ^ 59
def prefixEnd_358301 : Nat := 4983230072969 + 3 ^ 40 * 358301 * 2
def baseEnd_358301 : Nat := 122653754657805252926473

theorem tailTrace_358301 : CollatzResearch.WordTrace tailWord_358301 prefixEnd_358301 122653754657805252926473 := by
  unfold tailWord_358301
  simp only [CollatzResearch.WordTrace]
  refine ⟨13068311074944144784090757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8712207383296096522727171 13068311074944144784090757)
  ·
    refine ⟨2450308326552027147017017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13068311074944144784090757 2450308326552027147017017)
    ·
      refine ⟨1837731244914020360262763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2450308326552027147017017 1837731244914020360262763)
      ·
        refine ⟨2756596867371030540394145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1837731244914020360262763 2756596867371030540394145)
        ·
          refine ⟨2067447650528272905295609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2756596867371030540394145 2067447650528272905295609)
          ·
            refine ⟨1550585737896204678971707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2067447650528272905295609 1550585737896204678971707)
            ·
              refine ⟨2325878606844307018457561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1550585737896204678971707 2325878606844307018457561)
              ·
                refine ⟨1744408955133230263843171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2325878606844307018457561 1744408955133230263843171)
                ·
                  refine ⟨2616613432699845395764757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1744408955133230263843171 2616613432699845395764757)
                  ·
                    refine ⟨122653754657805252926473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2616613432699845395764757 122653754657805252926473)
                    ·
                      rfl

theorem cell22_358301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 6].length) (baseStart_358301 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358301 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358301 prefixEnd_358301 := by exact prefixLift 358301
  have htrace : WordTrace (prefixWord ++ tailWord_358301) baseStart_358301 baseEnd_358301 := by
    simpa [prefixWord, tailWord_358301, baseEnd_358301] using wordTrace_append hprefix tailTrace_358301
  have hstable : (prefixWord ++ tailWord_358301).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358301).length < 2 ^ (prefixWord ++ tailWord_358301).sum := by decide
  have hdescent : baseEnd_358301 < baseStart_358301 := by decide
  rcases family_descends (prefixWord ++ tailWord_358301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358331 : List Nat := [1, 1, 1, 1, 1, 2, 2, 3, 7, 3]
def baseStart_358331 : Nat := 118140960795 + 358331 * 2 ^ 59
def prefixEnd_358331 : Nat := 4983230072969 + 3 ^ 40 * 358331 * 2
def baseEnd_358331 : Nat := 122664024270895174676381

theorem tailTrace_358331 : CollatzResearch.WordTrace tailWord_358331 prefixEnd_358331 122664024270895174676381 := by
  unfold tailWord_358331
  simp only [CollatzResearch.WordTrace]
  refine ⟨13069405264835459907682847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8712936843223639938455231 13069405264835459907682847)
  ·
    refine ⟨19604107897253189861524271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13069405264835459907682847 19604107897253189861524271)
    ·
      refine ⟨29406161845879784792286407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19604107897253189861524271 29406161845879784792286407)
      ·
        refine ⟨44109242768819677188429611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29406161845879784792286407 44109242768819677188429611)
        ·
          refine ⟨66163864153229515782644417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44109242768819677188429611 66163864153229515782644417)
          ·
            refine ⟨49622898114922136836983313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66163864153229515782644417 49622898114922136836983313)
            ·
              refine ⟨37217173586191602627737485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 49622898114922136836983313 37217173586191602627737485)
              ·
                refine ⟨13956440094821850985401557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 37217173586191602627737485 13956440094821850985401557)
                ·
                  refine ⟨327104064722387132470349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 13956440094821850985401557 327104064722387132470349)
                  ·
                    refine ⟨122664024270895174676381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327104064722387132470349 122664024270895174676381)
                    ·
                      rfl

theorem cell22_358331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 2, 3, 7, 3].length) (baseStart_358331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358331 prefixEnd_358331 := by exact prefixLift 358331
  have htrace : WordTrace (prefixWord ++ tailWord_358331) baseStart_358331 baseEnd_358331 := by
    simpa [prefixWord, tailWord_358331, baseEnd_358331] using wordTrace_append hprefix tailTrace_358331
  have hstable : (prefixWord ++ tailWord_358331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358331).length < 2 ^ (prefixWord ++ tailWord_358331).sum := by decide
  have hdescent : baseEnd_358331 < baseStart_358331 := by decide
  rcases family_descends (prefixWord ++ tailWord_358331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358354 : List Nat := [3, 2, 2, 3, 2, 2, 2, 1, 2, 3]
def baseStart_358354 : Nat := 118140960795 + 358354 * 2 ^ 59
def prefixEnd_358354 : Nat := 4983230072969 + 3 ^ 40 * 358354 * 2
def baseEnd_358354 : Nat := 122671897640930781351311

theorem tailTrace_358354 : CollatzResearch.WordTrace tailWord_358354 prefixEnd_358354 122671897640930781351311 := by
  unfold tailWord_358354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3267561035938033708942529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8713496095834756557180077 3267561035938033708942529)
  ·
    refine ⟨2450670776953525281706897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3267561035938033708942529 2450670776953525281706897)
    ·
      refine ⟨1838003082715143961280173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2450670776953525281706897 1838003082715143961280173)
      ·
        refine ⟨689251156018178985480065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1838003082715143961280173 689251156018178985480065)
        ·
          refine ⟨516938367013634239110049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 689251156018178985480065 516938367013634239110049)
          ·
            refine ⟨387703775260225679332537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 516938367013634239110049 387703775260225679332537)
            ·
              refine ⟨290777831445169259499403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387703775260225679332537 290777831445169259499403)
              ·
                refine ⟨436166747167753889249105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290777831445169259499403 436166747167753889249105)
                ·
                  refine ⟨327125060375815416936829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436166747167753889249105 327125060375815416936829)
                  ·
                    refine ⟨122671897640930781351311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327125060375815416936829 122671897640930781351311)
                    ·
                      rfl

theorem cell22_358354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 2, 2, 2, 1, 2, 3].length) (baseStart_358354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358354 prefixEnd_358354 := by exact prefixLift 358354
  have htrace : WordTrace (prefixWord ++ tailWord_358354) baseStart_358354 baseEnd_358354 := by
    simpa [prefixWord, tailWord_358354, baseEnd_358354] using wordTrace_append hprefix tailTrace_358354
  have hstable : (prefixWord ++ tailWord_358354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358354).length < 2 ^ (prefixWord ++ tailWord_358354).sum := by decide
  have hdescent : baseEnd_358354 < baseStart_358354 := by decide
  rcases family_descends (prefixWord ++ tailWord_358354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358376 : List Nat := [2, 1, 4, 1, 1, 1, 1, 2, 4, 5]
def baseStart_358376 : Nat := 118140960795 + 358376 * 2 ^ 59
def prefixEnd_358376 : Nat := 4983230072969 + 3 ^ 40 * 358376 * 2
def baseEnd_358376 : Nat := 122679428690530057301243

theorem tailTrace_358376 : CollatzResearch.WordTrace tailWord_358376 prefixEnd_358376 122679428690530057301243 := by
  unfold tailWord_358376
  simp only [CollatzResearch.WordTrace]
  refine ⟨6535523274836216296535491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8714031033114955062047321 6535523274836216296535491)
  ·
    refine ⟨9803284912254324444803237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6535523274836216296535491 9803284912254324444803237)
    ·
      refine ⟨1838115921047685833400607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9803284912254324444803237 1838115921047685833400607)
      ·
        refine ⟨2757173881571528750100911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838115921047685833400607 2757173881571528750100911)
        ·
          refine ⟨4135760822357293125151367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757173881571528750100911 4135760822357293125151367)
          ·
            refine ⟨6203641233535939687727051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4135760822357293125151367 6203641233535939687727051)
            ·
              refine ⟨9305461850303909531590577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6203641233535939687727051 9305461850303909531590577)
              ·
                refine ⟨6979096387727932148692933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9305461850303909531590577 6979096387727932148692933)
                ·
                  refine ⟨1308580572698987277879925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6979096387727932148692933 1308580572698987277879925)
                  ·
                    refine ⟨122679428690530057301243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1308580572698987277879925 122679428690530057301243)
                    ·
                      rfl

theorem cell22_358376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 1, 2, 4, 5].length) (baseStart_358376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358376 prefixEnd_358376 := by exact prefixLift 358376
  have htrace : WordTrace (prefixWord ++ tailWord_358376) baseStart_358376 baseEnd_358376 := by
    simpa [prefixWord, tailWord_358376, baseEnd_358376] using wordTrace_append hprefix tailTrace_358376
  have hstable : (prefixWord ++ tailWord_358376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358376).length < 2 ^ (prefixWord ++ tailWord_358376).sum := by decide
  have hdescent : baseEnd_358376 < baseStart_358376 := by decide
  rcases family_descends (prefixWord ++ tailWord_358376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358442 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 1, 4]
def baseStart_358442 : Nat := 118140960795 + 358442 * 2 ^ 59
def prefixEnd_358442 : Nat := 4983230072969 + 3 ^ 40 * 358442 * 2
def baseEnd_358442 : Nat := 122702021839327885151041

theorem tailTrace_358442 : CollatzResearch.WordTrace tailWord_358442 prefixEnd_358442 122702021839327885151041 := by
  unfold tailWord_358442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3268363441858331466243395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8715635844955550576649053 3268363441858331466243395)
  ·
    refine ⟨4902545162787497199365093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3268363441858331466243395 4902545162787497199365093)
    ·
      refine ⟨919227218022655724880955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4902545162787497199365093 919227218022655724880955)
      ·
        refine ⟨1378840827033983587321433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919227218022655724880955 1378840827033983587321433)
        ·
          refine ⟨1034130620275487690491075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1378840827033983587321433 1034130620275487690491075)
          ·
            refine ⟨1551195930413231535736613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034130620275487690491075 1551195930413231535736613)
            ·
              refine ⟨290849236952480912950615, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1551195930413231535736613 290849236952480912950615)
              ·
                refine ⟨436273855428721369425923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 290849236952480912950615 436273855428721369425923)
                ·
                  refine ⟨654410783143082054138885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436273855428721369425923 654410783143082054138885)
                  ·
                    refine ⟨122702021839327885151041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654410783143082054138885 122702021839327885151041)
                    ·
                      rfl

theorem cell22_358442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_358442 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358442 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358442 prefixEnd_358442 := by exact prefixLift 358442
  have htrace : WordTrace (prefixWord ++ tailWord_358442) baseStart_358442 baseEnd_358442 := by
    simpa [prefixWord, tailWord_358442, baseEnd_358442] using wordTrace_append hprefix tailTrace_358442
  have hstable : (prefixWord ++ tailWord_358442).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358442).length < 2 ^ (prefixWord ++ tailWord_358442).sum := by decide
  have hdescent : baseEnd_358442 < baseStart_358442 := by decide
  rcases family_descends (prefixWord ++ tailWord_358442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358453 : List Nat := [1, 3, 3, 1, 1, 1, 2, 4, 2, 4]
def baseStart_358453 : Nat := 118140960795 + 358453 * 2 ^ 59
def prefixEnd_358453 : Nat := 4983230072969 + 3 ^ 40 * 358453 * 2
def baseEnd_358453 : Nat := 122705787364127523126007

theorem tailTrace_358453 : CollatzResearch.WordTrace tailWord_358453 prefixEnd_358453 122705787364127523126007 := by
  unfold tailWord_358453
  simp only [CollatzResearch.WordTrace]
  refine ⟨13073854970393474743624013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8715903313595649829082675 13073854970393474743624013)
  ·
    refine ⟨4902695613897553028859005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13073854970393474743624013 4902695613897553028859005)
    ·
      refine ⟨1838510855211582385822127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4902695613897553028859005 1838510855211582385822127)
      ·
        refine ⟨2757766282817373578733191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1838510855211582385822127 2757766282817373578733191)
        ·
          refine ⟨4136649424226060368099787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2757766282817373578733191 4136649424226060368099787)
          ·
            refine ⟨6204974136339090552149681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4136649424226060368099787 6204974136339090552149681)
            ·
              refine ⟨4653730602254317914112261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6204974136339090552149681 4653730602254317914112261)
              ·
                refine ⟨872574487922684608896049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4653730602254317914112261 872574487922684608896049)
                ·
                  refine ⟨654430865942013456672037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 872574487922684608896049 654430865942013456672037)
                  ·
                    refine ⟨122705787364127523126007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654430865942013456672037 122705787364127523126007)
                    ·
                      rfl

theorem cell22_358453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 4, 2, 4].length) (baseStart_358453 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358453 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358453 prefixEnd_358453 := by exact prefixLift 358453
  have htrace : WordTrace (prefixWord ++ tailWord_358453) baseStart_358453 baseEnd_358453 := by
    simpa [prefixWord, tailWord_358453, baseEnd_358453] using wordTrace_append hprefix tailTrace_358453
  have hstable : (prefixWord ++ tailWord_358453).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358453).length < 2 ^ (prefixWord ++ tailWord_358453).sum := by decide
  have hdescent : baseEnd_358453 < baseStart_358453 := by decide
  rcases family_descends (prefixWord ++ tailWord_358453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358455 : List Nat := [1, 1, 3, 1, 2, 2, 5, 2, 2, 3]
def baseStart_358455 : Nat := 118140960795 + 358455 * 2 ^ 59
def prefixEnd_358455 : Nat := 4983230072969 + 3 ^ 40 * 358455 * 2
def baseEnd_358455 : Nat := 122706472005000184576001

theorem tailTrace_358455 : CollatzResearch.WordTrace tailWord_358455 prefixEnd_358455 122706472005000184576001 := by
  unfold tailWord_358455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13073927916386229085196819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8715951944257486056797879 13073927916386229085196819)
  ·
    refine ⟨19610891874579343627795229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13073927916386229085196819 19610891874579343627795229)
    ·
      refine ⟨7354084452967253860423211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19610891874579343627795229 7354084452967253860423211)
      ·
        refine ⟨11031126679450880790634817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7354084452967253860423211 11031126679450880790634817)
        ·
          refine ⟨8273345009588160592976113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11031126679450880790634817 8273345009588160592976113)
          ·
            refine ⟨6205008757191120444732085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8273345009588160592976113 6205008757191120444732085)
            ·
              refine ⟨581719570986667541693633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6205008757191120444732085 581719570986667541693633)
              ·
                refine ⟨436289678240000656270225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 581719570986667541693633 436289678240000656270225)
                ·
                  refine ⟨327217258680000492202669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436289678240000656270225 327217258680000492202669)
                  ·
                    refine ⟨122706472005000184576001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327217258680000492202669 122706472005000184576001)
                    ·
                      rfl

theorem cell22_358455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 2, 5, 2, 2, 3].length) (baseStart_358455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358455 prefixEnd_358455 := by exact prefixLift 358455
  have htrace : WordTrace (prefixWord ++ tailWord_358455) baseStart_358455 baseEnd_358455 := by
    simpa [prefixWord, tailWord_358455, baseEnd_358455] using wordTrace_append hprefix tailTrace_358455
  have hstable : (prefixWord ++ tailWord_358455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358455).length < 2 ^ (prefixWord ++ tailWord_358455).sum := by decide
  have hdescent : baseEnd_358455 < baseStart_358455 := by decide
  rcases family_descends (prefixWord ++ tailWord_358455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358470 : List Nat := [6, 1, 1, 1, 1, 1, 1, 1, 3, 6]
def baseStart_358470 : Nat := 118140960795 + 358470 * 2 ^ 59
def prefixEnd_358470 : Nat := 4983230072969 + 3 ^ 40 * 358470 * 2
def baseEnd_358470 : Nat := 122711606811545145450955

theorem tailTrace_358470 : CollatzResearch.WordTrace tailWord_358470 prefixEnd_358470 122711606811545145450955 := by
  unfold tailWord_358470
  simp only [CollatzResearch.WordTrace]
  refine ⟨408577344104121457718527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8716316674221257764661909 408577344104121457718527)
  ·
    refine ⟨612866016156182186577791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 408577344104121457718527 612866016156182186577791)
    ·
      refine ⟨919299024234273279866687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 612866016156182186577791 919299024234273279866687)
      ·
        refine ⟨1378948536351409919800031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 919299024234273279866687 1378948536351409919800031)
        ·
          refine ⟨2068422804527114879700047, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1378948536351409919800031 2068422804527114879700047)
          ·
            refine ⟨3102634206790672319550071, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2068422804527114879700047 3102634206790672319550071)
            ·
              refine ⟨4653951310186008479325107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3102634206790672319550071 4653951310186008479325107)
              ·
                refine ⟨6980926965279012718987661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4653951310186008479325107 6980926965279012718987661)
                ·
                  refine ⟨2617847611979629769620373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6980926965279012718987661 2617847611979629769620373)
                  ·
                    refine ⟨122711606811545145450955, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2617847611979629769620373 122711606811545145450955)
                    ·
                      rfl

theorem cell22_358470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 1, 1, 3, 6].length) (baseStart_358470 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358470 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358470 prefixEnd_358470 := by exact prefixLift 358470
  have htrace : WordTrace (prefixWord ++ tailWord_358470) baseStart_358470 baseEnd_358470 := by
    simpa [prefixWord, tailWord_358470, baseEnd_358470] using wordTrace_append hprefix tailTrace_358470
  have hstable : (prefixWord ++ tailWord_358470).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358470).length < 2 ^ (prefixWord ++ tailWord_358470).sum := by decide
  have hdescent : baseEnd_358470 < baseStart_358470 := by decide
  rcases family_descends (prefixWord ++ tailWord_358470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358485 : List Nat := [1, 3, 2, 2, 1, 5, 2, 6]
def baseStart_358485 : Nat := 118140960795 + 358485 * 2 ^ 59
def prefixEnd_358485 : Nat := 4983230072969 + 3 ^ 40 * 358485 * 2
def baseEnd_358485 : Nat := 13635193513121122925101

theorem tailTrace_358485 : CollatzResearch.WordTrace tailWord_358485 prefixEnd_358485 13635193513121122925101 := by
  unfold tailWord_358485
  simp only [CollatzResearch.WordTrace]
  refine ⟨13075022106277544208788909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8716681404185029472525939 13075022106277544208788909)
  ·
    refine ⟨4903133289854079078295841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13075022106277544208788909 4903133289854079078295841)
    ·
      refine ⟨3677349967390559308721881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4903133289854079078295841 3677349967390559308721881)
      ·
        refine ⟨2758012475542919481541411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3677349967390559308721881 2758012475542919481541411)
        ·
          refine ⟨4137018713314379222312117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2758012475542919481541411 4137018713314379222312117)
          ·
            refine ⟨387845504373223052091761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4137018713314379222312117 387845504373223052091761)
            ·
              refine ⟨290884128279917289068821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 387845504373223052091761 290884128279917289068821)
              ·
                refine ⟨13635193513121122925101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 290884128279917289068821 13635193513121122925101)
                ·
                  rfl

theorem cell22_358485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 5, 2, 6].length) (baseStart_358485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358485 prefixEnd_358485 := by exact prefixLift 358485
  have htrace : WordTrace (prefixWord ++ tailWord_358485) baseStart_358485 baseEnd_358485 := by
    simpa [prefixWord, tailWord_358485, baseEnd_358485] using wordTrace_append hprefix tailTrace_358485
  have hstable : (prefixWord ++ tailWord_358485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358485).length < 2 ^ (prefixWord ++ tailWord_358485).sum := by decide
  have hdescent : baseEnd_358485 < baseStart_358485 := by decide
  rcases family_descends (prefixWord ++ tailWord_358485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358513 : List Nat := [1, 2, 2, 2, 1, 1, 4, 4, 5]
def baseStart_358513 : Nat := 118140960795 + 358513 * 2 ^ 59
def prefixEnd_358513 : Nat := 4983230072969 + 3 ^ 40 * 358513 * 2
def baseEnd_358513 : Nat := 40908775530102455541941

theorem tailTrace_358513 : CollatzResearch.WordTrace tailWord_358513 prefixEnd_358513 40908775530102455541941 := by
  unfold tailWord_358513
  simp only [CollatzResearch.WordTrace]
  refine ⟨13076043350176104990808193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8717362233450736660538795 13076043350176104990808193)
  ·
    refine ⟨9807032512632078743106145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13076043350176104990808193 9807032512632078743106145)
    ·
      refine ⟨7355274384474059057329609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9807032512632078743106145 7355274384474059057329609)
      ·
        refine ⟨5516455788355544292997207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7355274384474059057329609 5516455788355544292997207)
        ·
          refine ⟨8274683682533316439495811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5516455788355544292997207 8274683682533316439495811)
          ·
            refine ⟨12412025523799974659243717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8274683682533316439495811 12412025523799974659243717)
            ·
              refine ⟨2327254785712495248608197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 12412025523799974659243717 2327254785712495248608197)
              ·
                refine ⟨436360272321092859114037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2327254785712495248608197 436360272321092859114037)
                ·
                  refine ⟨40908775530102455541941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436360272321092859114037 40908775530102455541941)
                  ·
                    rfl

theorem cell22_358513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 4, 4, 5].length) (baseStart_358513 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358513 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358513 prefixEnd_358513 := by exact prefixLift 358513
  have htrace : WordTrace (prefixWord ++ tailWord_358513) baseStart_358513 baseEnd_358513 := by
    simpa [prefixWord, tailWord_358513, baseEnd_358513] using wordTrace_append hprefix tailTrace_358513
  have hstable : (prefixWord ++ tailWord_358513).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358513).length < 2 ^ (prefixWord ++ tailWord_358513).sum := by decide
  have hdescent : baseEnd_358513 < baseStart_358513 := by decide
  rcases family_descends (prefixWord ++ tailWord_358513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358594 : List Nat := [3, 5, 1, 1, 1, 1, 2, 1, 3, 4]
def baseStart_358594 : Nat := 118140960795 + 358594 * 2 ^ 59
def prefixEnd_358594 : Nat := 4983230072969 + 3 ^ 40 * 358594 * 2
def baseEnd_358594 : Nat := 122754054545650155350575

theorem tailTrace_358594 : CollatzResearch.WordTrace tailWord_358594 prefixEnd_358594 122754054545650155350575 := by
  unfold tailWord_358594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3269749415720663956126709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8719331775255103883004557 3269749415720663956126709)
  ·
    refine ⟨306539007723812245886879, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3269749415720663956126709 306539007723812245886879)
    ·
      refine ⟨459808511585718368830319, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 306539007723812245886879 459808511585718368830319)
      ·
        refine ⟨689712767378577553245479, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459808511585718368830319 689712767378577553245479)
        ·
          refine ⟨1034569151067866329868219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689712767378577553245479 1034569151067866329868219)
          ·
            refine ⟨1551853726601799494802329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034569151067866329868219 1551853726601799494802329)
            ·
              refine ⟨1163890294951349621101747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1551853726601799494802329 1163890294951349621101747)
              ·
                refine ⟨1745835442427024431652621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1163890294951349621101747 1745835442427024431652621)
                ·
                  refine ⟨654688290910134161869733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1745835442427024431652621 654688290910134161869733)
                  ·
                    refine ⟨122754054545650155350575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654688290910134161869733 122754054545650155350575)
                    ·
                      rfl

theorem cell22_358594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 1, 2, 1, 3, 4].length) (baseStart_358594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358594 prefixEnd_358594 := by exact prefixLift 358594
  have htrace : WordTrace (prefixWord ++ tailWord_358594) baseStart_358594 baseEnd_358594 := by
    simpa [prefixWord, tailWord_358594, baseEnd_358594] using wordTrace_append hprefix tailTrace_358594
  have hstable : (prefixWord ++ tailWord_358594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358594).length < 2 ^ (prefixWord ++ tailWord_358594).sum := by decide
  have hdescent : baseEnd_358594 < baseStart_358594 := by decide
  rcases family_descends (prefixWord ++ tailWord_358594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358626 : List Nat := [3, 3, 4, 1, 1, 1, 2, 1, 6]
def baseStart_358626 : Nat := 118140960795 + 358626 * 2 ^ 59
def prefixEnd_358626 : Nat := 4983230072969 + 3 ^ 40 * 358626 * 2
def baseEnd_358626 : Nat := 40921669599870912850159

theorem tailTrace_358626 : CollatzResearch.WordTrace tailWord_358626 prefixEnd_358626 40921669599870912850159 := by
  unfold tailWord_358626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3270041199691681322417933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8720109865844483526447821 3270041199691681322417933)
  ·
    refine ⟨1226265449884380495906725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3270041199691681322417933 1226265449884380495906725)
    ·
      refine ⟨229924771853321342982511, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1226265449884380495906725 229924771853321342982511)
      ·
        refine ⟨344887157779982014473767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 229924771853321342982511 344887157779982014473767)
        ·
          refine ⟨517330736669973021710651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 344887157779982014473767 517330736669973021710651)
          ·
            refine ⟨775996105004959532565977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517330736669973021710651 775996105004959532565977)
            ·
              refine ⟨581997078753719649424483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 775996105004959532565977 581997078753719649424483)
              ·
                refine ⟨872995618130579474136725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 581997078753719649424483 872995618130579474136725)
                ·
                  refine ⟨40921669599870912850159, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 872995618130579474136725 40921669599870912850159)
                  ·
                    rfl

theorem cell22_358626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 4, 1, 1, 1, 2, 1, 6].length) (baseStart_358626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358626 prefixEnd_358626 := by exact prefixLift 358626
  have htrace : WordTrace (prefixWord ++ tailWord_358626) baseStart_358626 baseEnd_358626 := by
    simpa [prefixWord, tailWord_358626, baseEnd_358626] using wordTrace_append hprefix tailTrace_358626
  have hstable : (prefixWord ++ tailWord_358626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358626).length < 2 ^ (prefixWord ++ tailWord_358626).sum := by decide
  have hdescent : baseEnd_358626 < baseStart_358626 := by decide
  rcases family_descends (prefixWord ++ tailWord_358626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358652 : List Nat := [2, 2, 2, 1, 4, 1, 2, 2, 3, 3]
def baseStart_358652 : Nat := 118140960795 + 358652 * 2 ^ 59
def prefixEnd_358652 : Nat := 4983230072969 + 3 ^ 40 * 358652 * 2
def baseEnd_358652 : Nat := 122773909130957337400397

theorem tailTrace_358652 : CollatzResearch.WordTrace tailWord_358652 prefixEnd_358652 122773909130957337400397 := by
  unfold tailWord_358652
  simp only [CollatzResearch.WordTrace]
  refine ⟨6540556548336265865059105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8720742064448354486745473 6540556548336265865059105)
  ·
    refine ⟨4905417411252199398794329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6540556548336265865059105 4905417411252199398794329)
    ·
      refine ⟨3679063058439149549095747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4905417411252199398794329 3679063058439149549095747)
      ·
        refine ⟨5518594587658724323643621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679063058439149549095747 5518594587658724323643621)
        ·
          refine ⟨1034736485186010810683179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5518594587658724323643621 1034736485186010810683179)
          ·
            refine ⟨1552104727779016216024769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034736485186010810683179 1552104727779016216024769)
            ·
              refine ⟨1164078545834262162018577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1552104727779016216024769 1164078545834262162018577)
              ·
                refine ⟨873058909375696621513933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164078545834262162018577 873058909375696621513933)
                ·
                  refine ⟨327397091015886233067725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873058909375696621513933 327397091015886233067725)
                  ·
                    refine ⟨122773909130957337400397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327397091015886233067725 122773909130957337400397)
                    ·
                      rfl

theorem cell22_358652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 2, 3, 3].length) (baseStart_358652 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358652 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358652 prefixEnd_358652 := by exact prefixLift 358652
  have htrace : WordTrace (prefixWord ++ tailWord_358652) baseStart_358652 baseEnd_358652 := by
    simpa [prefixWord, tailWord_358652, baseEnd_358652] using wordTrace_append hprefix tailTrace_358652
  have hstable : (prefixWord ++ tailWord_358652).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358652).length < 2 ^ (prefixWord ++ tailWord_358652).sum := by decide
  have hdescent : baseEnd_358652 < baseStart_358652 := by decide
  rcases family_descends (prefixWord ++ tailWord_358652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358686 : List Nat := [4, 3, 2, 1, 1, 1, 3, 1, 3, 3]
def baseStart_358686 : Nat := 118140960795 + 358686 * 2 ^ 59
def prefixEnd_358686 : Nat := 4983230072969 + 3 ^ 40 * 358686 * 2
def baseEnd_358686 : Nat := 122785548025792582050293

theorem tailTrace_358686 : CollatzResearch.WordTrace tailWord_358686 prefixEnd_358686 122785548025792582050293 := by
  unfold tailWord_358686
  simp only [CollatzResearch.WordTrace]
  refine ⟨1635294147318669442106989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8721568785699570357903941 1635294147318669442106989)
  ·
    refine ⟨613235305244501040790121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1635294147318669442106989 613235305244501040790121)
    ·
      refine ⟨459926478933375780592591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 613235305244501040790121 459926478933375780592591)
      ·
        refine ⟨689889718400063670888887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 459926478933375780592591 689889718400063670888887)
        ·
          refine ⟨1034834577600095506333331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 689889718400063670888887 1034834577600095506333331)
          ·
            refine ⟨1552251866400143259499997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1034834577600095506333331 1552251866400143259499997)
            ·
              refine ⟨582094449900053722312499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1552251866400143259499997 582094449900053722312499)
              ·
                refine ⟨873141674850080583468749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582094449900053722312499 873141674850080583468749)
                ·
                  refine ⟨327428128068780218800781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 873141674850080583468749 327428128068780218800781)
                  ·
                    refine ⟨122785548025792582050293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327428128068780218800781 122785548025792582050293)
                    ·
                      rfl

theorem cell22_358686_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 3, 1, 3, 3].length) (baseStart_358686 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358686 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358686 prefixEnd_358686 := by exact prefixLift 358686
  have htrace : WordTrace (prefixWord ++ tailWord_358686) baseStart_358686 baseEnd_358686 := by
    simpa [prefixWord, tailWord_358686, baseEnd_358686] using wordTrace_append hprefix tailTrace_358686
  have hstable : (prefixWord ++ tailWord_358686).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358686).length < 2 ^ (prefixWord ++ tailWord_358686).sum := by decide
  have hdescent : baseEnd_358686 < baseStart_358686 := by decide
  rcases family_descends (prefixWord ++ tailWord_358686) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358712 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 1, 4]
def baseStart_358712 : Nat := 118140960795 + 358712 * 2 ^ 59
def prefixEnd_358712 : Nat := 4983230072969 + 3 ^ 40 * 358712 * 2
def baseEnd_358712 : Nat := 122794448357137180900213

theorem tailTrace_358712 : CollatzResearch.WordTrace tailWord_358712 prefixEnd_358712 122794448357137180900213 := by
  unfold tailWord_358712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6541650738227580988651195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8722200984303441318201593 6541650738227580988651195)
  ·
    refine ⟨9812476107341371482976793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6541650738227580988651195 9812476107341371482976793)
    ·
      refine ⟨7359357080506028612232595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9812476107341371482976793 7359357080506028612232595)
      ·
        refine ⟨11039035620759042918348893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7359357080506028612232595 11039035620759042918348893)
        ·
          refine ⟨4139638357784641094380835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11039035620759042918348893 4139638357784641094380835)
          ·
            refine ⟨6209457536676961641571253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4139638357784641094380835 6209457536676961641571253)
            ·
              refine ⟨582136644063465153897305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6209457536676961641571253 582136644063465153897305)
              ·
                refine ⟨436602483047598865422979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582136644063465153897305 436602483047598865422979)
                ·
                  refine ⟨654903724571398298134469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436602483047598865422979 654903724571398298134469)
                  ·
                    refine ⟨122794448357137180900213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 654903724571398298134469 122794448357137180900213)
                    ·
                      rfl

theorem cell22_358712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 4].length) (baseStart_358712 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358712 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358712 prefixEnd_358712 := by exact prefixLift 358712
  have htrace : WordTrace (prefixWord ++ tailWord_358712) baseStart_358712 baseEnd_358712 := by
    simpa [prefixWord, tailWord_358712, baseEnd_358712] using wordTrace_append hprefix tailTrace_358712
  have hstable : (prefixWord ++ tailWord_358712).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358712).length < 2 ^ (prefixWord ++ tailWord_358712).sum := by decide
  have hdescent : baseEnd_358712 < baseStart_358712 := by decide
  rcases family_descends (prefixWord ++ tailWord_358712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358727 : List Nat := [1, 1, 4, 1, 2, 2, 2, 5, 4]
def baseStart_358727 : Nat := 118140960795 + 358727 * 2 ^ 59
def prefixEnd_358727 : Nat := 4983230072969 + 3 ^ 40 * 358727 * 2
def baseEnd_358727 : Nat := 40933194387894047258389

theorem tailTrace_358727 : CollatzResearch.WordTrace tailWord_358727 prefixEnd_358727 40933194387894047258389 := by
  unfold tailWord_358727
  simp only [CollatzResearch.WordTrace]
  refine ⟨13083848571400819539098435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8722565714267213026065623 13083848571400819539098435)
  ·
    refine ⟨19625772857101229308647653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13083848571400819539098435 19625772857101229308647653)
    ·
      refine ⟨3679832410706480495371435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19625772857101229308647653 3679832410706480495371435)
      ·
        refine ⟨5519748616059720743057153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3679832410706480495371435 5519748616059720743057153)
        ·
          refine ⟨4139811462044790557292865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5519748616059720743057153 4139811462044790557292865)
          ·
            refine ⟨3104858596533592917969649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4139811462044790557292865 3104858596533592917969649)
            ·
              refine ⟨2328643947400194688477237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3104858596533592917969649 2328643947400194688477237)
              ·
                refine ⟨218310370068768252044741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2328643947400194688477237 218310370068768252044741)
                ·
                  refine ⟨40933194387894047258389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218310370068768252044741 40933194387894047258389)
                  ·
                    rfl

theorem cell22_358727_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 2, 5, 4].length) (baseStart_358727 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358727 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358727 prefixEnd_358727 := by exact prefixLift 358727
  have htrace : WordTrace (prefixWord ++ tailWord_358727) baseStart_358727 baseEnd_358727 := by
    simpa [prefixWord, tailWord_358727, baseEnd_358727] using wordTrace_append hprefix tailTrace_358727
  have hstable : (prefixWord ++ tailWord_358727).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358727).length < 2 ^ (prefixWord ++ tailWord_358727).sum := by decide
  have hdescent : baseEnd_358727 < baseStart_358727 := by decide
  rcases family_descends (prefixWord ++ tailWord_358727) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358759 : List Nat := [1, 1, 5, 1, 3, 1, 2, 3, 2, 3]
def baseStart_358759 : Nat := 118140960795 + 358759 * 2 ^ 59
def prefixEnd_358759 : Nat := 4983230072969 + 3 ^ 40 * 358759 * 2
def baseEnd_358759 : Nat := 122810537417644724975069

theorem tailTrace_358759 : CollatzResearch.WordTrace tailWord_358759 prefixEnd_358759 122810537417644724975069 := by
  unfold tailWord_358759
  simp only [CollatzResearch.WordTrace]
  refine ⟨13085015707284889004263331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8723343804856592669508887 13085015707284889004263331)
  ·
    refine ⟨19627523560927333506394997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13085015707284889004263331 19627523560927333506394997)
    ·
      refine ⟨1840080333836937516224531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19627523560927333506394997 1840080333836937516224531)
      ·
        refine ⟨2760120500755406274336797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840080333836937516224531 2760120500755406274336797)
        ·
          refine ⟨1035045187783277352876299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2760120500755406274336797 1035045187783277352876299)
          ·
            refine ⟨1552567781674916029314449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035045187783277352876299 1552567781674916029314449)
            ·
              refine ⟨1164425836256187021985837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1552567781674916029314449 1164425836256187021985837)
              ·
                refine ⟨436659688596070133244689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1164425836256187021985837 436659688596070133244689)
                ·
                  refine ⟨327494766447052599933517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 436659688596070133244689 327494766447052599933517)
                  ·
                    refine ⟨122810537417644724975069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327494766447052599933517 122810537417644724975069)
                    ·
                      rfl

theorem cell22_358759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 3, 1, 2, 3, 2, 3].length) (baseStart_358759 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358759 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358759 prefixEnd_358759 := by exact prefixLift 358759
  have htrace : WordTrace (prefixWord ++ tailWord_358759) baseStart_358759 baseEnd_358759 := by
    simpa [prefixWord, tailWord_358759, baseEnd_358759] using wordTrace_append hprefix tailTrace_358759
  have hstable : (prefixWord ++ tailWord_358759).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358759).length < 2 ^ (prefixWord ++ tailWord_358759).sum := by decide
  have hdescent : baseEnd_358759 < baseStart_358759 := by decide
  rcases family_descends (prefixWord ++ tailWord_358759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358894 : List Nat := [4, 1, 2, 1, 2, 3, 1, 2, 1, 5]
def baseStart_358894 : Nat := 118140960795 + 358894 * 2 ^ 59
def prefixEnd_358894 : Nat := 4983230072969 + 3 ^ 40 * 358894 * 2
def baseEnd_358894 : Nat := 122856750676549372849655

theorem tailTrace_358894 : CollatzResearch.WordTrace tailWord_358894 prefixEnd_358894 122856750676549372849655 := by
  unfold tailWord_358894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1636242445224475882553467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8726626374530538040285157 1636242445224475882553467)
  ·
    refine ⟨2454363667836713823830201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1636242445224475882553467 2454363667836713823830201)
    ·
      refine ⟨1840772750877535367872651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2454363667836713823830201 1840772750877535367872651)
      ·
        refine ⟨2761159126316303051808977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840772750877535367872651 2761159126316303051808977)
        ·
          refine ⟨2070869344737227288856733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2761159126316303051808977 2070869344737227288856733)
          ·
            refine ⟨776576004276460233321275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2070869344737227288856733 776576004276460233321275)
            ·
              refine ⟨1164864006414690349981913, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 776576004276460233321275 1164864006414690349981913)
              ·
                refine ⟨873648004811017762486435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1164864006414690349981913 873648004811017762486435)
                ·
                  refine ⟨1310472007216526643729653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 873648004811017762486435 1310472007216526643729653)
                  ·
                    refine ⟨122856750676549372849655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1310472007216526643729653 122856750676549372849655)
                    ·
                      rfl

theorem cell22_358894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 1, 2, 1, 5].length) (baseStart_358894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358894 prefixEnd_358894 := by exact prefixLift 358894
  have htrace : WordTrace (prefixWord ++ tailWord_358894) baseStart_358894 baseEnd_358894 := by
    simpa [prefixWord, tailWord_358894, baseEnd_358894] using wordTrace_append hprefix tailTrace_358894
  have hstable : (prefixWord ++ tailWord_358894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358894).length < 2 ^ (prefixWord ++ tailWord_358894).sum := by decide
  have hdescent : baseEnd_358894 < baseStart_358894 := by decide
  rcases family_descends (prefixWord ++ tailWord_358894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358898 : List Nat := [3, 2, 1, 4, 2, 1, 3, 1, 1, 4]
def baseStart_358898 : Nat := 118140960795 + 358898 * 2 ^ 59
def prefixEnd_358898 : Nat := 4983230072969 + 3 ^ 40 * 358898 * 2
def baseEnd_358898 : Nat := 122858119958294695749643

theorem tailTrace_358898 : CollatzResearch.WordTrace tailWord_358898 prefixEnd_358898 122858119958294695749643 := by
  unfold tailWord_358898
  simp only [CollatzResearch.WordTrace]
  refine ⟨3272521363445328935893337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8726723635854210495715565 3272521363445328935893337)
  ·
    refine ⟨2454391022583996701920003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3272521363445328935893337 2454391022583996701920003)
    ·
      refine ⟨3681586533875995052880005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454391022583996701920003 3681586533875995052880005)
      ·
        refine ⟨690297475101749072415001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3681586533875995052880005 690297475101749072415001)
        ·
          refine ⟨517723106326311804311251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 690297475101749072415001 517723106326311804311251)
          ·
            refine ⟨776584659489467706466877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 517723106326311804311251 776584659489467706466877)
            ·
              refine ⟨291219247308550389925079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776584659489467706466877 291219247308550389925079)
              ·
                refine ⟨436828870962825584887619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291219247308550389925079 436828870962825584887619)
                ·
                  refine ⟨655243306444238377331429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 436828870962825584887619 655243306444238377331429)
                  ·
                    refine ⟨122858119958294695749643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655243306444238377331429 122858119958294695749643)
                    ·
                      rfl

theorem cell22_358898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 4, 2, 1, 3, 1, 1, 4].length) (baseStart_358898 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358898 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358898 prefixEnd_358898 := by exact prefixLift 358898
  have htrace : WordTrace (prefixWord ++ tailWord_358898) baseStart_358898 baseEnd_358898 := by
    simpa [prefixWord, tailWord_358898, baseEnd_358898] using wordTrace_append hprefix tailTrace_358898
  have hstable : (prefixWord ++ tailWord_358898).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358898).length < 2 ^ (prefixWord ++ tailWord_358898).sum := by decide
  have hdescent : baseEnd_358898 < baseStart_358898 := by decide
  rcases family_descends (prefixWord ++ tailWord_358898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358913 : List Nat := [1, 2, 4, 1, 3, 3, 2, 2, 4]
def baseStart_358913 : Nat := 118140960795 + 358913 * 2 ^ 59
def prefixEnd_358913 : Nat := 4983230072969 + 3 ^ 40 * 358913 * 2
def baseEnd_358913 : Nat := 40954418254946552208199

theorem tailTrace_358913 : CollatzResearch.WordTrace tailWord_358913 prefixEnd_358913 40954418254946552208199 := by
  unfold tailWord_358913
  simp only [CollatzResearch.WordTrace]
  refine ⟨13090632548726973305369393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8727088365817982203579595 13090632548726973305369393)
  ·
    refine ⟨9817974411545229979027045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13090632548726973305369393 9817974411545229979027045)
    ·
      refine ⟨1840870202164730621067571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9817974411545229979027045 1840870202164730621067571)
      ·
        refine ⟨2761305303247095931601357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1840870202164730621067571 2761305303247095931601357)
        ·
          refine ⟨1035489488717660974350509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2761305303247095931601357 1035489488717660974350509)
          ·
            refine ⟨388308558269122865381441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1035489488717660974350509 388308558269122865381441)
            ·
              refine ⟨291231418701842149036081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 388308558269122865381441 291231418701842149036081)
              ·
                refine ⟨218423564026381611777061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291231418701842149036081 218423564026381611777061)
                ·
                  refine ⟨40954418254946552208199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218423564026381611777061 40954418254946552208199)
                  ·
                    rfl

theorem cell22_358913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 3, 3, 2, 2, 4].length) (baseStart_358913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358913 prefixEnd_358913 := by exact prefixLift 358913
  have htrace : WordTrace (prefixWord ++ tailWord_358913) baseStart_358913 baseEnd_358913 := by
    simpa [prefixWord, tailWord_358913, baseEnd_358913] using wordTrace_append hprefix tailTrace_358913
  have hstable : (prefixWord ++ tailWord_358913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358913).length < 2 ^ (prefixWord ++ tailWord_358913).sum := by decide
  have hdescent : baseEnd_358913 < baseStart_358913 := by decide
  rcases family_descends (prefixWord ++ tailWord_358913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358924 : List Nat := [2, 2, 1, 2, 4, 3, 1, 7]
def baseStart_358924 : Nat := 118140960795 + 358924 * 2 ^ 59
def prefixEnd_358924 : Nat := 4983230072969 + 3 ^ 40 * 358924 * 2
def baseEnd_358924 : Nat := 13651891143293254955507

theorem tailTrace_358924 : CollatzResearch.WordTrace tailWord_358924 prefixEnd_358924 13651891143293254955507 := by
  unfold tailWord_358924
  simp only [CollatzResearch.WordTrace]
  refine ⟨6545516875843561092009913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8727355834458081456013217 6545516875843561092009913)
  ·
    refine ⟨4909137656882670819007435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6545516875843561092009913 4909137656882670819007435)
    ·
      refine ⟨7363706485324006228511153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4909137656882670819007435 7363706485324006228511153)
      ·
        refine ⟨5522779863993004671383365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7363706485324006228511153 5522779863993004671383365)
        ·
          refine ⟨1035521224498688375884381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5522779863993004671383365 1035521224498688375884381)
          ·
            refine ⟨388320459187008140956643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1035521224498688375884381 388320459187008140956643)
            ·
              refine ⟨582480688780512211434965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388320459187008140956643 582480688780512211434965)
              ·
                refine ⟨13651891143293254955507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 582480688780512211434965 13651891143293254955507)
                ·
                  rfl

theorem cell22_358924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 1, 7].length) (baseStart_358924 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358924 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358924 prefixEnd_358924 := by exact prefixLift 358924
  have htrace : WordTrace (prefixWord ++ tailWord_358924) baseStart_358924 baseEnd_358924 := by
    simpa [prefixWord, tailWord_358924, baseEnd_358924] using wordTrace_append hprefix tailTrace_358924
  have hstable : (prefixWord ++ tailWord_358924).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358924).length < 2 ^ (prefixWord ++ tailWord_358924).sum := by decide
  have hdescent : baseEnd_358924 < baseStart_358924 := by decide
  rcases family_descends (prefixWord ++ tailWord_358924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358967 : List Nat := [1, 1, 3, 1, 2, 3, 1, 1, 4, 5]
def baseStart_358967 : Nat := 118140960795 + 358967 * 2 ^ 59
def prefixEnd_358967 : Nat := 4983230072969 + 3 ^ 40 * 358967 * 2
def baseEnd_358967 : Nat := 122881740068401515774431

theorem tailTrace_358967 : CollatzResearch.WordTrace tailWord_358967 prefixEnd_358967 122881740068401515774431 := by
  unfold tailWord_358967
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092602090531340527835155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8728401393687560351890103 13092602090531340527835155)
  ·
    refine ⟨19638903135797010791752733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13092602090531340527835155 19638903135797010791752733)
    ·
      refine ⟨7364588675923879046907275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19638903135797010791752733 7364588675923879046907275)
      ·
        refine ⟨11046883013885818570360913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7364588675923879046907275 11046883013885818570360913)
        ·
          refine ⟨8285162260414363927770685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11046883013885818570360913 8285162260414363927770685)
          ·
            refine ⟨3106935847655386472914007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8285162260414363927770685 3106935847655386472914007)
            ·
              refine ⟨4660403771483079709371011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3106935847655386472914007 4660403771483079709371011)
              ·
                refine ⟨6990605657224619564056517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4660403771483079709371011 6990605657224619564056517)
                ·
                  refine ⟨1310738560729616168260597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6990605657224619564056517 1310738560729616168260597)
                  ·
                    refine ⟨122881740068401515774431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1310738560729616168260597 122881740068401515774431)
                    ·
                      rfl

theorem cell22_358967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 1, 4, 5].length) (baseStart_358967 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358967 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358967 prefixEnd_358967 := by exact prefixLift 358967
  have htrace : WordTrace (prefixWord ++ tailWord_358967) baseStart_358967 baseEnd_358967 := by
    simpa [prefixWord, tailWord_358967, baseEnd_358967] using wordTrace_append hprefix tailTrace_358967
  have hstable : (prefixWord ++ tailWord_358967).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358967).length < 2 ^ (prefixWord ++ tailWord_358967).sum := by decide
  have hdescent : baseEnd_358967 < baseStart_358967 := by decide
  rcases family_descends (prefixWord ++ tailWord_358967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358973 : List Nat := [1, 4, 1, 3, 2, 1, 2, 4, 1, 3]
def baseStart_358973 : Nat := 118140960795 + 358973 * 2 ^ 59
def prefixEnd_358973 : Nat := 4983230072969 + 3 ^ 40 * 358973 * 2
def baseEnd_358973 : Nat := 122883793991019500124413

theorem tailTrace_358973 : CollatzResearch.WordTrace tailWord_358973 prefixEnd_358973 122883793991019500124413 := by
  unfold tailWord_358973
  simp only [CollatzResearch.WordTrace]
  refine ⟨13092820928509603552553573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8728547285673069035035715 13092820928509603552553573)
  ·
    refine ⟨2454903924095550666103795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13092820928509603552553573 2454903924095550666103795)
    ·
      refine ⟨3682355886143325999155693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2454903924095550666103795 3682355886143325999155693)
      ·
        refine ⟨1380883457303747249683385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3682355886143325999155693 1380883457303747249683385)
        ·
          refine ⟨1035662592977810437262539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1380883457303747249683385 1035662592977810437262539)
          ·
            refine ⟨1553493889466715655893809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1035662592977810437262539 1553493889466715655893809)
            ·
              refine ⟨1165120417100036741920357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1553493889466715655893809 1165120417100036741920357)
              ·
                refine ⟨218460078206256889110067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1165120417100036741920357 218460078206256889110067)
                ·
                  refine ⟨327690117309385333665101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218460078206256889110067 327690117309385333665101)
                  ·
                    refine ⟨122883793991019500124413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327690117309385333665101 122883793991019500124413)
                    ·
                      rfl

theorem cell22_358973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 2, 1, 2, 4, 1, 3].length) (baseStart_358973 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358973 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358973 prefixEnd_358973 := by exact prefixLift 358973
  have htrace : WordTrace (prefixWord ++ tailWord_358973) baseStart_358973 baseEnd_358973 := by
    simpa [prefixWord, tailWord_358973, baseEnd_358973] using wordTrace_append hprefix tailTrace_358973
  have hstable : (prefixWord ++ tailWord_358973).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358973).length < 2 ^ (prefixWord ++ tailWord_358973).sum := by decide
  have hdescent : baseEnd_358973 < baseStart_358973 := by decide
  rcases family_descends (prefixWord ++ tailWord_358973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_358986 : List Nat := [3, 1, 2, 1, 1, 5, 3, 1, 5]
def baseStart_358986 : Nat := 118140960795 + 358986 * 2 ^ 59
def prefixEnd_358986 : Nat := 4983230072969 + 3 ^ 40 * 358986 * 2
def baseEnd_358986 : Nat := 40962748052230599849791

theorem tailTrace_358986 : CollatzResearch.WordTrace tailWord_358986 prefixEnd_358986 40962748052230599849791 := by
  unfold tailWord_358986
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273323769365626693194203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8728863384975004515184541 3273323769365626693194203)
  ·
    refine ⟨4909985654048440039791305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273323769365626693194203 4909985654048440039791305)
    ·
      refine ⟨3682489240536330029843479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4909985654048440039791305 3682489240536330029843479)
      ·
        refine ⟨5523733860804495044765219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3682489240536330029843479 5523733860804495044765219)
        ·
          refine ⟨8285600791206742567147829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5523733860804495044765219 8285600791206742567147829)
          ·
            refine ⟨776775074175632115670109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8285600791206742567147829 776775074175632115670109)
            ·
              refine ⟨291290652815862043376291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 776775074175632115670109 291290652815862043376291)
              ·
                refine ⟨436935979223793065064437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291290652815862043376291 436935979223793065064437)
                ·
                  refine ⟨40962748052230599849791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 436935979223793065064437 40962748052230599849791)
                  ·
                    rfl

theorem cell22_358986_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 5, 3, 1, 5].length) (baseStart_358986 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_358986 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_358986 prefixEnd_358986 := by exact prefixLift 358986
  have htrace : WordTrace (prefixWord ++ tailWord_358986) baseStart_358986 baseEnd_358986 := by
    simpa [prefixWord, tailWord_358986, baseEnd_358986] using wordTrace_append hprefix tailTrace_358986
  have hstable : (prefixWord ++ tailWord_358986).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_358986).length < 2 ^ (prefixWord ++ tailWord_358986).sum := by decide
  have hdescent : baseEnd_358986 < baseStart_358986 := by decide
  rcases family_descends (prefixWord ++ tailWord_358986) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359027 : List Nat := [1, 1, 1, 2, 2, 1, 1, 4, 3, 6]
def baseStart_359027 : Nat := 118140960795 + 359027 * 2 ^ 59
def prefixEnd_359027 : Nat := 4983230072969 + 3 ^ 40 * 359027 * 2
def baseEnd_359027 : Nat := 122902279294581359274247

theorem tailTrace_359027 : CollatzResearch.WordTrace tailWord_359027 prefixEnd_359027 122902279294581359274247 := by
  unfold tailWord_359027
  simp only [CollatzResearch.WordTrace]
  refine ⟨13094790470313970775019335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8729860313542647183346223 13094790470313970775019335)
  ·
    refine ⟨19642185705470956162529003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13094790470313970775019335 19642185705470956162529003)
    ·
      refine ⟨29463278558206434243793505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19642185705470956162529003 29463278558206434243793505)
      ·
        refine ⟨22097458918654825682845129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29463278558206434243793505 22097458918654825682845129)
        ·
          refine ⟨16573094188991119262133847, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22097458918654825682845129 16573094188991119262133847)
          ·
            refine ⟨24859641283486678893200771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16573094188991119262133847 24859641283486678893200771)
            ·
              refine ⟨37289461925230018339801157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24859641283486678893200771 37289461925230018339801157)
              ·
                refine ⟨6991774110980628438712717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37289461925230018339801157 6991774110980628438712717)
                ·
                  refine ⟨2621915291617735664517269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6991774110980628438712717 2621915291617735664517269)
                  ·
                    refine ⟨122902279294581359274247, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2621915291617735664517269 122902279294581359274247)
                    ·
                      rfl

theorem cell22_359027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 1, 4, 3, 6].length) (baseStart_359027 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359027 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359027 prefixEnd_359027 := by exact prefixLift 359027
  have htrace : WordTrace (prefixWord ++ tailWord_359027) baseStart_359027 baseEnd_359027 := by
    simpa [prefixWord, tailWord_359027, baseEnd_359027] using wordTrace_append hprefix tailTrace_359027
  have hstable : (prefixWord ++ tailWord_359027).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359027).length < 2 ^ (prefixWord ++ tailWord_359027).sum := by decide
  have hdescent : baseEnd_359027 < baseStart_359027 := by decide
  rcases family_descends (prefixWord ++ tailWord_359027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359050 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 1, 4]
def baseStart_359050 : Nat := 118140960795 + 359050 * 2 ^ 59
def prefixEnd_359050 : Nat := 4983230072969 + 3 ^ 40 * 359050 * 2
def baseEnd_359050 : Nat := 122910152664616965949177

theorem tailTrace_359050 : CollatzResearch.WordTrace tailWord_359050 prefixEnd_359050 122910152664616965949177 := by
  unfold tailWord_359050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3273907337307661425776651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8730419566153763802071069 3273907337307661425776651)
  ·
    refine ⟨4910861005961492138664977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3273907337307661425776651 4910861005961492138664977)
    ·
      refine ⟨3683145754471119103998733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4910861005961492138664977 3683145754471119103998733)
      ·
        refine ⟨1381179657926669663999525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3683145754471119103998733 1381179657926669663999525)
        ·
          refine ⟨258971185861250561999911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1381179657926669663999525 258971185861250561999911)
          ·
            refine ⟨388456778791875842999867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 258971185861250561999911 388456778791875842999867)
            ·
              refine ⟨582685168187813764499801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 388456778791875842999867 582685168187813764499801)
              ·
                refine ⟨437013876140860323374851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 582685168187813764499801 437013876140860323374851)
                ·
                  refine ⟨655520814211290485062277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437013876140860323374851 655520814211290485062277)
                  ·
                    refine ⟨122910152664616965949177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655520814211290485062277 122910152664616965949177)
                    ·
                      rfl

theorem cell22_359050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 4].length) (baseStart_359050 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359050 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359050 prefixEnd_359050 := by exact prefixLift 359050
  have htrace : WordTrace (prefixWord ++ tailWord_359050) baseStart_359050 baseEnd_359050 := by
    simpa [prefixWord, tailWord_359050, baseEnd_359050] using wordTrace_append hprefix tailTrace_359050
  have hstable : (prefixWord ++ tailWord_359050).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359050).length < 2 ^ (prefixWord ++ tailWord_359050).sum := by decide
  have hdescent : baseEnd_359050 < baseStart_359050 := by decide
  rcases family_descends (prefixWord ++ tailWord_359050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359108 : List Nat := [2, 3, 3, 1, 1, 3, 1, 2, 3, 3]
def baseStart_359108 : Nat := 118140960795 + 359108 * 2 ^ 59
def prefixEnd_359108 : Nat := 4983230072969 + 3 ^ 40 * 359108 * 2
def baseEnd_359108 : Nat := 122930007249924147998999

theorem tailTrace_359108 : CollatzResearch.WordTrace tailWord_359108 prefixEnd_359108 122930007249924147998999 := by
  unfold tailWord_359108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6548872391510260804358989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8731829855347014405811985 6548872391510260804358989)
  ·
    refine ⟨2455827146816347801634621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6548872391510260804358989 2455827146816347801634621)
    ·
      refine ⟨920935180056130425612983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2455827146816347801634621 920935180056130425612983)
      ·
        refine ⟨1381402770084195638419475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 920935180056130425612983 1381402770084195638419475)
        ·
          refine ⟨2072104155126293457629213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381402770084195638419475 2072104155126293457629213)
          ·
            refine ⟨777039058172360046610955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2072104155126293457629213 777039058172360046610955)
            ·
              refine ⟨1165558587258540069916433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 777039058172360046610955 1165558587258540069916433)
              ·
                refine ⟨874168940443905052437325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1165558587258540069916433 874168940443905052437325)
                ·
                  refine ⟨327813352666464394663997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 874168940443905052437325 327813352666464394663997)
                  ·
                    refine ⟨122930007249924147998999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 327813352666464394663997 122930007249924147998999)
                    ·
                      rfl

theorem cell22_359108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 3, 1, 2, 3, 3].length) (baseStart_359108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359108 prefixEnd_359108 := by exact prefixLift 359108
  have htrace : WordTrace (prefixWord ++ tailWord_359108) baseStart_359108 baseEnd_359108 := by
    simpa [prefixWord, tailWord_359108, baseEnd_359108] using wordTrace_append hprefix tailTrace_359108
  have hstable : (prefixWord ++ tailWord_359108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359108).length < 2 ^ (prefixWord ++ tailWord_359108).sum := by decide
  have hdescent : baseEnd_359108 < baseStart_359108 := by decide
  rcases family_descends (prefixWord ++ tailWord_359108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359196 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 4, 4]
def baseStart_359196 : Nat := 118140960795 + 359196 * 2 ^ 59
def prefixEnd_359196 : Nat := 4983230072969 + 3 ^ 40 * 359196 * 2
def baseEnd_359196 : Nat := 122960131448321251798729

theorem tailTrace_359196 : CollatzResearch.WordTrace tailWord_359196 prefixEnd_359196 122960131448321251798729 := by
  unfold tailWord_359196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550477203350856318960721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8733969604467808425280961 6550477203350856318960721)
  ·
    refine ⟨4912857902513142239220541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6550477203350856318960721 4912857902513142239220541)
    ·
      refine ⟨1842321713442428339707703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4912857902513142239220541 1842321713442428339707703)
      ·
        refine ⟨2763482570163642509561555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842321713442428339707703 2763482570163642509561555)
        ·
          refine ⟨4145223855245463764342333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2763482570163642509561555 4145223855245463764342333)
          ·
            refine ⟨1554458945717048911628375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4145223855245463764342333 1554458945717048911628375)
            ·
              refine ⟨2331688418575573367442563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554458945717048911628375 2331688418575573367442563)
              ·
                refine ⟨3497532627863360051163845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2331688418575573367442563 3497532627863360051163845)
                ·
                  refine ⟨655787367724380009593221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3497532627863360051163845 655787367724380009593221)
                  ·
                    refine ⟨122960131448321251798729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655787367724380009593221 122960131448321251798729)
                    ·
                      rfl

theorem cell22_359196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 4].length) (baseStart_359196 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359196 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359196 prefixEnd_359196 := by exact prefixLift 359196
  have htrace : WordTrace (prefixWord ++ tailWord_359196) baseStart_359196 baseEnd_359196 := by
    simpa [prefixWord, tailWord_359196, baseEnd_359196] using wordTrace_append hprefix tailTrace_359196
  have hstable : (prefixWord ++ tailWord_359196).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359196).length < 2 ^ (prefixWord ++ tailWord_359196).sum := by decide
  have hdescent : baseEnd_359196 < baseStart_359196 := by decide
  rcases family_descends (prefixWord ++ tailWord_359196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359200 : List Nat := [2, 1, 1, 5, 1, 3, 3, 2, 4]
def baseStart_359200 : Nat := 118140960795 + 359200 * 2 ^ 59
def prefixEnd_359200 : Nat := 4983230072969 + 3 ^ 40 * 359200 * 2
def baseEnd_359200 : Nat := 40987166910022191566239

theorem tailTrace_359200 : CollatzResearch.WordTrace tailWord_359200 prefixEnd_359200 40987166910022191566239 := by
  unfold tailWord_359200
  simp only [CollatzResearch.WordTrace]
  refine ⟨6550550149343610660533527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8734066865791480880711369 6550550149343610660533527)
  ·
    refine ⟨9825825224015415990800291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6550550149343610660533527 9825825224015415990800291)
    ·
      refine ⟨14738737836023123986200437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9825825224015415990800291 14738737836023123986200437)
      ·
        refine ⟨1381756672127167873706291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14738737836023123986200437 1381756672127167873706291)
        ·
          refine ⟨2072635008190751810559437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1381756672127167873706291 2072635008190751810559437)
          ·
            refine ⟨777238128071531928959789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2072635008190751810559437 777238128071531928959789)
            ·
              refine ⟨291464298026824473359921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 777238128071531928959789 291464298026824473359921)
              ·
                refine ⟨218598223520118355019941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 291464298026824473359921 218598223520118355019941)
                ·
                  refine ⟨40987166910022191566239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 218598223520118355019941 40987166910022191566239)
                  ·
                    rfl

theorem cell22_359200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 3, 3, 2, 4].length) (baseStart_359200 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359200 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359200 prefixEnd_359200 := by exact prefixLift 359200
  have htrace : WordTrace (prefixWord ++ tailWord_359200) baseStart_359200 baseEnd_359200 := by
    simpa [prefixWord, tailWord_359200, baseEnd_359200] using wordTrace_append hprefix tailTrace_359200
  have hstable : (prefixWord ++ tailWord_359200).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359200).length < 2 ^ (prefixWord ++ tailWord_359200).sum := by decide
  have hdescent : baseEnd_359200 < baseStart_359200 := by decide
  rcases family_descends (prefixWord ++ tailWord_359200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359230 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 2, 4]
def baseStart_359230 : Nat := 118140960795 + 359230 * 2 ^ 59
def prefixEnd_359230 : Nat := 4983230072969 + 3 ^ 40 * 359230 * 2
def baseEnd_359230 : Nat := 122971770343156496448625

theorem tailTrace_359230 : CollatzResearch.WordTrace tailWord_359230 prefixEnd_359230 122971770343156496448625 := by
  unfold tailWord_359230
  simp only [CollatzResearch.WordTrace]
  refine ⟨1637774311072317055582393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8734796325719024296439429 1637774311072317055582393)
  ·
    refine ⟨1228330733304237791686795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1637774311072317055582393 1228330733304237791686795)
    ·
      refine ⟨1842496099956356687530193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1228330733304237791686795 1842496099956356687530193)
      ·
        refine ⟨1381872074967267515647645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1842496099956356687530193 1381872074967267515647645)
        ·
          refine ⟨518202028112725318367867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1381872074967267515647645 518202028112725318367867)
          ·
            refine ⟨777303042169087977551801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 518202028112725318367867 777303042169087977551801)
            ·
              refine ⟨582977281626815983163851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777303042169087977551801 582977281626815983163851)
              ·
                refine ⟨874465922440223974745777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 582977281626815983163851 874465922440223974745777)
                ·
                  refine ⟨655849441830167981059333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 874465922440223974745777 655849441830167981059333)
                  ·
                    refine ⟨122971770343156496448625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 655849441830167981059333 122971770343156496448625)
                    ·
                      rfl

theorem cell22_359230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 4].length) (baseStart_359230 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359230 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359230 prefixEnd_359230 := by exact prefixLift 359230
  have htrace : WordTrace (prefixWord ++ tailWord_359230) baseStart_359230 baseEnd_359230 := by
    simpa [prefixWord, tailWord_359230, baseEnd_359230] using wordTrace_append hprefix tailTrace_359230
  have hstable : (prefixWord ++ tailWord_359230).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359230).length < 2 ^ (prefixWord ++ tailWord_359230).sum := by decide
  have hdescent : baseEnd_359230 < baseStart_359230 := by decide
  rcases family_descends (prefixWord ++ tailWord_359230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359271 : List Nat := [1, 1, 5, 1, 2, 2, 1, 1, 1, 7]
def baseStart_359271 : Nat := 118140960795 + 359271 * 2 ^ 59
def prefixEnd_359271 : Nat := 4983230072969 + 3 ^ 40 * 359271 * 2
def baseEnd_359271 : Nat := 122985805481046056173499

theorem tailTrace_359271 : CollatzResearch.WordTrace tailWord_359271 prefixEnd_359271 122985805481046056173499 := by
  unfold tailWord_359271
  simp only [CollatzResearch.WordTrace]
  refine ⟨13103689881430000446901667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8735793254286666964601111 13103689881430000446901667)
  ·
    refine ⟨19655534822145000670352501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13103689881430000446901667 19655534822145000670352501)
    ·
      refine ⟨1842706389576093812845547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19655534822145000670352501 1842706389576093812845547)
      ·
        refine ⟨2764059584364140719268321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1842706389576093812845547 2764059584364140719268321)
        ·
          refine ⟨2073044688273105539451241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2764059584364140719268321 2073044688273105539451241)
          ·
            refine ⟨1554783516204829154588431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2073044688273105539451241 1554783516204829154588431)
            ·
              refine ⟨2332175274307243731882647, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1554783516204829154588431 2332175274307243731882647)
              ·
                refine ⟨3498262911460865597823971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2332175274307243731882647 3498262911460865597823971)
                ·
                  refine ⟨5247394367191298396735957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3498262911460865597823971 5247394367191298396735957)
                  ·
                    refine ⟨122985805481046056173499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5247394367191298396735957 122985805481046056173499)
                    ·
                      rfl

theorem cell22_359271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 1, 1, 1, 7].length) (baseStart_359271 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359271 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359271 prefixEnd_359271 := by exact prefixLift 359271
  have htrace : WordTrace (prefixWord ++ tailWord_359271) baseStart_359271 baseEnd_359271 := by
    simpa [prefixWord, tailWord_359271, baseEnd_359271] using wordTrace_append hprefix tailTrace_359271
  have hstable : (prefixWord ++ tailWord_359271).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359271).length < 2 ^ (prefixWord ++ tailWord_359271).sum := by decide
  have hdescent : baseEnd_359271 < baseStart_359271 := by decide
  rcases family_descends (prefixWord ++ tailWord_359271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359331 : List Nat := [1, 1, 1, 4, 1, 2, 3, 2, 1, 6]
def baseStart_359331 : Nat := 118140960795 + 359331 * 2 ^ 59
def prefixEnd_359331 : Nat := 4983230072969 + 3 ^ 40 * 359331 * 2
def baseEnd_359331 : Nat := 123006344707225899673315

theorem tailTrace_359331 : CollatzResearch.WordTrace tailWord_359331 prefixEnd_359331 123006344707225899673315 := by
  unfold tailWord_359331
  simp only [CollatzResearch.WordTrace]
  refine ⟨13105878261212630694085847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8737252174141753796057231 13105878261212630694085847)
  ·
    refine ⟨19658817391818946041128771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13105878261212630694085847 19658817391818946041128771)
    ·
      refine ⟨29488226087728419061693157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19658817391818946041128771 29488226087728419061693157)
      ·
        refine ⟨5529042391449078574067467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29488226087728419061693157 5529042391449078574067467)
        ·
          refine ⟨8293563587173617861101201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5529042391449078574067467 8293563587173617861101201)
          ·
            refine ⟨6220172690380213395825901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8293563587173617861101201 6220172690380213395825901)
            ·
              refine ⟨2332564758892580023434713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6220172690380213395825901 2332564758892580023434713)
              ·
                refine ⟨1749423569169435017576035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2332564758892580023434713 1749423569169435017576035)
                ·
                  refine ⟨2624135353754152526364053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1749423569169435017576035 2624135353754152526364053)
                  ·
                    refine ⟨123006344707225899673315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2624135353754152526364053 123006344707225899673315)
                    ·
                      rfl

theorem cell22_359331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 3, 2, 1, 6].length) (baseStart_359331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359331 prefixEnd_359331 := by exact prefixLift 359331
  have htrace : WordTrace (prefixWord ++ tailWord_359331) baseStart_359331 baseEnd_359331 := by
    simpa [prefixWord, tailWord_359331, baseEnd_359331] using wordTrace_append hprefix tailTrace_359331
  have hstable : (prefixWord ++ tailWord_359331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359331).length < 2 ^ (prefixWord ++ tailWord_359331).sum := by decide
  have hdescent : baseEnd_359331 < baseStart_359331 := by decide
  rcases family_descends (prefixWord ++ tailWord_359331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359376 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 2, 6]
def baseStart_359376 : Nat := 118140960795 + 359376 * 2 ^ 59
def prefixEnd_359376 : Nat := 4983230072969 + 3 ^ 40 * 359376 * 2
def baseEnd_359376 : Nat := 123021749126860782298177

theorem tailTrace_359376 : CollatzResearch.WordTrace tailWord_359376 prefixEnd_359376 123021749126860782298177 := by
  unfold tailWord_359376
  simp only [CollatzResearch.WordTrace]
  refine ⟨6553759773024801689736991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8738346364033068919649321 6553759773024801689736991)
  ·
    refine ⟨9830639659537202534605487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6553759773024801689736991 9830639659537202534605487)
    ·
      refine ⟨14745959489305803801908231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9830639659537202534605487 14745959489305803801908231)
      ·
        refine ⟨22118939233958705702862347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14745959489305803801908231 22118939233958705702862347)
        ·
          refine ⟨33178408850938058554293521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22118939233958705702862347 33178408850938058554293521)
          ·
            refine ⟨24883806638203543915720141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33178408850938058554293521 24883806638203543915720141)
            ·
              refine ⟨9331427489326328968395053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 24883806638203543915720141 9331427489326328968395053)
              ·
                refine ⟨3499285308497373363148145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9331427489326328968395053 3499285308497373363148145)
                ·
                  refine ⟨2624463981373030022361109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3499285308497373363148145 2624463981373030022361109)
                  ·
                    refine ⟨123021749126860782298177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2624463981373030022361109 123021749126860782298177)
                    ·
                      rfl

theorem cell22_359376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 6].length) (baseStart_359376 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359376 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359376 prefixEnd_359376 := by exact prefixLift 359376
  have htrace : WordTrace (prefixWord ++ tailWord_359376) baseStart_359376 baseEnd_359376 := by
    simpa [prefixWord, tailWord_359376, baseEnd_359376] using wordTrace_append hprefix tailTrace_359376
  have hstable : (prefixWord ++ tailWord_359376).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359376).length < 2 ^ (prefixWord ++ tailWord_359376).sum := by decide
  have hdescent : baseEnd_359376 < baseStart_359376 := by decide
  rcases family_descends (prefixWord ++ tailWord_359376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359425 : List Nat := [1, 2, 4, 1, 2, 3, 2, 2, 5]
def baseStart_359425 : Nat := 118140960795 + 359425 * 2 ^ 59
def prefixEnd_359425 : Nat := 4983230072969 + 3 ^ 40 * 359425 * 2
def baseEnd_359425 : Nat := 41012840942746995941009

theorem tailTrace_359425 : CollatzResearch.WordTrace tailWord_359425 prefixEnd_359425 41012840942746995941009 := by
  unfold tailWord_359425
  simp only [CollatzResearch.WordTrace]
  refine ⟨13109306722872084748007729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8739537815248056498671819 13109306722872084748007729)
  ·
    refine ⟨9831980042154063561005797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13109306722872084748007729 9831980042154063561005797)
    ·
      refine ⟨1843496257903886917688587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9831980042154063561005797 1843496257903886917688587)
      ·
        refine ⟨2765244386855830376532881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1843496257903886917688587 2765244386855830376532881)
        ·
          refine ⟨2073933290141872782399661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2765244386855830376532881 2073933290141872782399661)
          ·
            refine ⟨777724983803202293399873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2073933290141872782399661 777724983803202293399873)
            ·
              refine ⟨583293737852401720049905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 777724983803202293399873 583293737852401720049905)
              ·
                refine ⟨437470303389301290037429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583293737852401720049905 437470303389301290037429)
                ·
                  refine ⟨41012840942746995941009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 437470303389301290037429 41012840942746995941009)
                  ·
                    rfl

theorem cell22_359425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 2, 2, 5].length) (baseStart_359425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359425 prefixEnd_359425 := by exact prefixLift 359425
  have htrace : WordTrace (prefixWord ++ tailWord_359425) baseStart_359425 baseEnd_359425 := by
    simpa [prefixWord, tailWord_359425, baseEnd_359425] using wordTrace_append hprefix tailTrace_359425
  have hstable : (prefixWord ++ tailWord_359425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359425).length < 2 ^ (prefixWord ++ tailWord_359425).sum := by decide
  have hdescent : baseEnd_359425 < baseStart_359425 := by decide
  rcases family_descends (prefixWord ++ tailWord_359425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359468 : List Nat := [2, 2, 1, 1, 1, 2, 3, 4, 1, 5]
def baseStart_359468 : Nat := 118140960795 + 359468 * 2 ^ 59
def prefixEnd_359468 : Nat := 4983230072969 + 3 ^ 40 * 359468 * 2
def baseEnd_359468 : Nat := 123053242607003208997895

theorem tailTrace_359468 : CollatzResearch.WordTrace tailWord_359468 prefixEnd_359468 123053242607003208997895 := by
  unfold tailWord_359468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6555437530858151545911529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8740583374477535394548705 6555437530858151545911529)
  ·
    refine ⟨4916578148143613659433647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6555437530858151545911529 4916578148143613659433647)
    ·
      refine ⟨7374867222215420489150471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4916578148143613659433647 7374867222215420489150471)
      ·
        refine ⟨11062300833323130733725707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7374867222215420489150471 11062300833323130733725707)
        ·
          refine ⟨16593451249984696100588561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11062300833323130733725707 16593451249984696100588561)
          ·
            refine ⟨12445088437488522075441421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16593451249984696100588561 12445088437488522075441421)
            ·
              refine ⟨4666908164058195778290533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12445088437488522075441421 4666908164058195778290533)
              ·
                refine ⟨875045280760911708429475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4666908164058195778290533 875045280760911708429475)
                ·
                  refine ⟨1312567921141367562644213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875045280760911708429475 1312567921141367562644213)
                  ·
                    refine ⟨123053242607003208997895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1312567921141367562644213 123053242607003208997895)
                    ·
                      rfl

theorem cell22_359468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 5].length) (baseStart_359468 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359468 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359468 prefixEnd_359468 := by exact prefixLift 359468
  have htrace : WordTrace (prefixWord ++ tailWord_359468) baseStart_359468 baseEnd_359468 := by
    simpa [prefixWord, tailWord_359468, baseEnd_359468] using wordTrace_append hprefix tailTrace_359468
  have hstable : (prefixWord ++ tailWord_359468).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359468).length < 2 ^ (prefixWord ++ tailWord_359468).sum := by decide
  have hdescent : baseEnd_359468 < baseStart_359468 := by decide
  rcases family_descends (prefixWord ++ tailWord_359468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359543 : List Nat := [1, 1, 3, 1, 1, 4, 1, 3, 7]
def baseStart_359543 : Nat := 118140960795 + 359543 * 2 ^ 59
def prefixEnd_359543 : Nat := 4983230072969 + 3 ^ 40 * 359543 * 2
def baseEnd_359543 : Nat := 41026305546576004457555

theorem tailTrace_359543 : CollatzResearch.WordTrace tailWord_359543 prefixEnd_359543 41026305546576004457555 := by
  unfold tailWord_359543
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113610536444590900803283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8742407024296393933868855 13113610536444590900803283)
  ·
    refine ⟨19670415804666886351204925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13113610536444590900803283 19670415804666886351204925)
    ·
      refine ⟨7376405926750082381701847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19670415804666886351204925 7376405926750082381701847)
      ·
        refine ⟨11064608890125123572552771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7376405926750082381701847 11064608890125123572552771)
        ·
          refine ⟨16596913335187685358829157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11064608890125123572552771 16596913335187685358829157)
          ·
            refine ⟨3111921250347691004780467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16596913335187685358829157 3111921250347691004780467)
            ·
              refine ⟨4667881875521536507170701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3111921250347691004780467 4667881875521536507170701)
              ·
                refine ⟨1750455703320576190189013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4667881875521536507170701 1750455703320576190189013)
                ·
                  refine ⟨41026305546576004457555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1750455703320576190189013 41026305546576004457555)
                  ·
                    rfl

theorem cell22_359543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 3, 7].length) (baseStart_359543 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359543 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359543 prefixEnd_359543 := by exact prefixLift 359543
  have htrace : WordTrace (prefixWord ++ tailWord_359543) baseStart_359543 baseEnd_359543 := by
    simpa [prefixWord, tailWord_359543, baseEnd_359543] using wordTrace_append hprefix tailTrace_359543
  have hstable : (prefixWord ++ tailWord_359543).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359543).length < 2 ^ (prefixWord ++ tailWord_359543).sum := by decide
  have hdescent : baseEnd_359543 < baseStart_359543 := by decide
  rcases family_descends (prefixWord ++ tailWord_359543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359547 : List Nat := [1, 1, 1, 1, 1, 4, 1, 8, 1, 3]
def baseStart_359547 : Nat := 118140960795 + 359547 * 2 ^ 59
def prefixEnd_359547 : Nat := 4983230072969 + 3 ^ 40 * 359547 * 2
def baseEnd_359547 : Nat := 123080285921473336272653

theorem tailTrace_359547 : CollatzResearch.WordTrace tailWord_359547 prefixEnd_359547 123080285921473336272653 := by
  unfold tailWord_359547
  simp only [CollatzResearch.WordTrace]
  refine ⟨13113756428430099583948895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8742504285620066389299263 13113756428430099583948895)
  ·
    refine ⟨19670634642645149375923343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13113756428430099583948895 19670634642645149375923343)
    ·
      refine ⟨29505951963967724063885015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19670634642645149375923343 29505951963967724063885015)
      ·
        refine ⟨44258927945951586095827523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29505951963967724063885015 44258927945951586095827523)
        ·
          refine ⟨66388391918927379143741285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44258927945951586095827523 66388391918927379143741285)
          ·
            refine ⟨12447823484798883589451491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 66388391918927379143741285 12447823484798883589451491)
            ·
              refine ⟨18671735227198325384177237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12447823484798883589451491 18671735227198325384177237)
              ·
                refine ⟨218809397193730375595827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 18671735227198325384177237 218809397193730375595827)
                ·
                  refine ⟨328214095790595563393741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 218809397193730375595827 328214095790595563393741)
                  ·
                    refine ⟨123080285921473336272653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 328214095790595563393741 123080285921473336272653)
                    ·
                      rfl

theorem cell22_359547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 8, 1, 3].length) (baseStart_359547 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359547 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359547 prefixEnd_359547 := by exact prefixLift 359547
  have htrace : WordTrace (prefixWord ++ tailWord_359547) baseStart_359547 baseEnd_359547 := by
    simpa [prefixWord, tailWord_359547, baseEnd_359547] using wordTrace_append hprefix tailTrace_359547
  have hstable : (prefixWord ++ tailWord_359547).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359547).length < 2 ^ (prefixWord ++ tailWord_359547).sum := by decide
  have hdescent : baseEnd_359547 < baseStart_359547 := by decide
  rcases family_descends (prefixWord ++ tailWord_359547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359594 : List Nat := [3, 1, 5, 1, 1, 2, 2, 2, 5]
def baseStart_359594 : Nat := 118140960795 + 359594 * 2 ^ 59
def prefixEnd_359594 : Nat := 4983230072969 + 3 ^ 40 * 359594 * 2
def baseEnd_359594 : Nat := 41032124993993626782503

theorem tailTrace_359594 : CollatzResearch.WordTrace tailWord_359594 prefixEnd_359594 41032124993993626782503 := by
  unfold tailWord_359594
  simp only [CollatzResearch.WordTrace]
  refine ⟨3278867664814956652727459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8743647106173217740606557 3278867664814956652727459)
  ·
    refine ⟨4918301497222434979091189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3278867664814956652727459 4918301497222434979091189)
    ·
      refine ⟨461090765364603279289799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4918301497222434979091189 461090765364603279289799)
      ·
        refine ⟨691636148046904918934699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461090765364603279289799 691636148046904918934699)
        ·
          refine ⟨1037454222070357378402049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691636148046904918934699 1037454222070357378402049)
          ·
            refine ⟨778090666552768033801537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1037454222070357378402049 778090666552768033801537)
            ·
              refine ⟨583567999914576025351153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778090666552768033801537 583567999914576025351153)
              ·
                refine ⟨437675999935932019013365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 583567999914576025351153 437675999935932019013365)
                ·
                  refine ⟨41032124993993626782503, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 437675999935932019013365 41032124993993626782503)
                  ·
                    rfl

theorem cell22_359594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 2, 2, 5].length) (baseStart_359594 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359594 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359594 prefixEnd_359594 := by exact prefixLift 359594
  have htrace : WordTrace (prefixWord ++ tailWord_359594) baseStart_359594 baseEnd_359594 := by
    simpa [prefixWord, tailWord_359594, baseEnd_359594] using wordTrace_append hprefix tailTrace_359594
  have hstable : (prefixWord ++ tailWord_359594).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359594).length < 2 ^ (prefixWord ++ tailWord_359594).sum := by decide
  have hdescent : baseEnd_359594 < baseStart_359594 := by decide
  rcases family_descends (prefixWord ++ tailWord_359594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359637 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 1, 5]
def baseStart_359637 : Nat := 118140960795 + 359637 * 2 ^ 59
def prefixEnd_359637 : Nat := 4983230072969 + 3 ^ 40 * 359637 * 2
def baseEnd_359637 : Nat := 123111094760743101522377

theorem tailTrace_359637 : CollatzResearch.WordTrace tailWord_359637 prefixEnd_359637 123111094760743101522377 := by
  unfold tailWord_359637
  simp only [CollatzResearch.WordTrace]
  refine ⟨13117038998104044954725165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8744692665402696636483443 13117038998104044954725165)
  ·
    refine ⟨4918889624289016858021937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13117038998104044954725165 4918889624289016858021937)
    ·
      refine ⟨3689167218216762643516453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4918889624289016858021937 3689167218216762643516453)
      ·
        refine ⟨691718853415642995659335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3689167218216762643516453 691718853415642995659335)
        ·
          refine ⟨1037578280123464493489003, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 691718853415642995659335 1037578280123464493489003)
          ·
            refine ⟨1556367420185196740233505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037578280123464493489003 1556367420185196740233505)
            ·
              refine ⟨1167275565138897555175129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1556367420185196740233505 1167275565138897555175129)
              ·
                refine ⟨875456673854173166381347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1167275565138897555175129 875456673854173166381347)
                ·
                  refine ⟨1313185010781259749572021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875456673854173166381347 1313185010781259749572021)
                  ·
                    refine ⟨123111094760743101522377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1313185010781259749572021 123111094760743101522377)
                    ·
                      rfl

theorem cell22_359637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 5].length) (baseStart_359637 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359637 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359637 prefixEnd_359637 := by exact prefixLift 359637
  have htrace : WordTrace (prefixWord ++ tailWord_359637) baseStart_359637 baseEnd_359637 := by
    simpa [prefixWord, tailWord_359637, baseEnd_359637] using wordTrace_append hprefix tailTrace_359637
  have hstable : (prefixWord ++ tailWord_359637).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359637).length < 2 ^ (prefixWord ++ tailWord_359637).sum := by decide
  have hdescent : baseEnd_359637 < baseStart_359637 := by decide
  rcases family_descends (prefixWord ++ tailWord_359637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359684 : List Nat := [2, 3, 2, 2, 2, 3, 2, 6]
def baseStart_359684 : Nat := 118140960795 + 359684 * 2 ^ 59
def prefixEnd_359684 : Nat := 4983230072969 + 3 ^ 40 * 359684 * 2
def baseEnd_359684 : Nat := 13680798202361182844137

theorem tailTrace_359684 : CollatzResearch.WordTrace tailWord_359684 prefixEnd_359684 13680798202361182844137 := by
  unfold tailWord_359684
  simp only [CollatzResearch.WordTrace]
  refine ⟨6559376614466885990843053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8745835485955847987790737 6559376614466885990843053)
  ·
    refine ⟨2459766230425082246566145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6559376614466885990843053 2459766230425082246566145)
    ·
      refine ⟨1844824672818811684924609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2459766230425082246566145 1844824672818811684924609)
      ·
        refine ⟨1383618504614108763693457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1844824672818811684924609 1383618504614108763693457)
        ·
          refine ⟨1037713878460581572770093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1383618504614108763693457 1037713878460581572770093)
          ·
            refine ⟨389142704422718089788785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1037713878460581572770093 389142704422718089788785)
            ·
              refine ⟨291857028317038567341589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389142704422718089788785 291857028317038567341589)
              ·
                refine ⟨13680798202361182844137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 291857028317038567341589 13680798202361182844137)
                ·
                  rfl

theorem cell22_359684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 2, 3, 2, 6].length) (baseStart_359684 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359684 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359684 prefixEnd_359684 := by exact prefixLift 359684
  have htrace : WordTrace (prefixWord ++ tailWord_359684) baseStart_359684 baseEnd_359684 := by
    simpa [prefixWord, tailWord_359684, baseEnd_359684] using wordTrace_append hprefix tailTrace_359684
  have hstable : (prefixWord ++ tailWord_359684).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359684).length < 2 ^ (prefixWord ++ tailWord_359684).sum := by decide
  have hdescent : baseEnd_359684 < baseStart_359684 := by decide
  rcases family_descends (prefixWord ++ tailWord_359684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359729 : List Nat := [1, 2, 2, 3, 3, 1, 4, 1, 5]
def baseStart_359729 : Nat := 118140960795 + 359729 * 2 ^ 59
def prefixEnd_359729 : Nat := 4983230072969 + 3 ^ 40 * 359729 * 2
def baseEnd_359729 : Nat := 41047529413628509407365

theorem tailTrace_359729 : CollatzResearch.WordTrace tailWord_359729 prefixEnd_359729 41047529413628509407365 := by
  unfold tailWord_359729
  simp only [CollatzResearch.WordTrace]
  refine ⟨13120394513770744667074241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8746929675847163111382827 13120394513770744667074241)
  ·
    refine ⟨9840295885328058500305681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13120394513770744667074241 9840295885328058500305681)
    ·
      refine ⟨7380221913996043875229261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9840295885328058500305681 7380221913996043875229261)
      ·
        refine ⟨2767583217748516453210973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7380221913996043875229261 2767583217748516453210973)
        ·
          refine ⟨1037843706655693669954115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2767583217748516453210973 1037843706655693669954115)
          ·
            refine ⟨1556765559983540504931173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1037843706655693669954115 1556765559983540504931173)
            ·
              refine ⟨291893542496913844674595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1556765559983540504931173 291893542496913844674595)
              ·
                refine ⟨437840313745370767011893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291893542496913844674595 437840313745370767011893)
                ·
                  refine ⟨41047529413628509407365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 437840313745370767011893 41047529413628509407365)
                  ·
                    rfl

theorem cell22_359729_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 3, 1, 4, 1, 5].length) (baseStart_359729 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359729 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359729 prefixEnd_359729 := by exact prefixLift 359729
  have htrace : WordTrace (prefixWord ++ tailWord_359729) baseStart_359729 baseEnd_359729 := by
    simpa [prefixWord, tailWord_359729, baseEnd_359729] using wordTrace_append hprefix tailTrace_359729
  have hstable : (prefixWord ++ tailWord_359729).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359729).length < 2 ^ (prefixWord ++ tailWord_359729).sum := by decide
  have hdescent : baseEnd_359729 < baseStart_359729 := by decide
  rcases family_descends (prefixWord ++ tailWord_359729) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359785 : List Nat := [1, 2, 1, 1, 1, 3, 2, 11]
def baseStart_359785 : Nat := 118140960795 + 359785 * 2 ^ 59
def prefixEnd_359785 : Nat := 4983230072969 + 3 ^ 40 * 359785 * 2
def baseEnd_359785 : Nat := 13684639798368894313547

theorem tailTrace_359785 : CollatzResearch.WordTrace tailWord_359785 prefixEnd_359785 13684639798368894313547 := by
  unfold tailWord_359785
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122437001567866231112809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8748291334378577487408539 13122437001567866231112809)
  ·
    refine ⟨9841827751175899673334607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13122437001567866231112809 9841827751175899673334607)
    ·
      refine ⟨14762741626763849510001911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9841827751175899673334607 14762741626763849510001911)
      ·
        refine ⟨22144112440145774265002867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14762741626763849510001911 22144112440145774265002867)
        ·
          refine ⟨33216168660218661397504301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22144112440145774265002867 33216168660218661397504301)
          ·
            refine ⟨12456063247581998024064113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33216168660218661397504301 12456063247581998024064113)
            ·
              refine ⟨9342047435686498518048085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12456063247581998024064113 9342047435686498518048085)
              ·
                refine ⟨13684639798368894313547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 9342047435686498518048085 13684639798368894313547)
                ·
                  rfl

theorem cell22_359785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 11].length) (baseStart_359785 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359785 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359785 prefixEnd_359785 := by exact prefixLift 359785
  have htrace : WordTrace (prefixWord ++ tailWord_359785) baseStart_359785 baseEnd_359785 := by
    simpa [prefixWord, tailWord_359785, baseEnd_359785] using wordTrace_append hprefix tailTrace_359785
  have hstable : (prefixWord ++ tailWord_359785).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359785).length < 2 ^ (prefixWord ++ tailWord_359785).sum := by decide
  have hdescent : baseEnd_359785 < baseStart_359785 := by decide
  rcases family_descends (prefixWord ++ tailWord_359785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359789 : List Nat := [1, 5, 1, 1, 1, 4, 2, 1, 1, 5]
def baseStart_359789 : Nat := 118140960795 + 359789 * 2 ^ 59
def prefixEnd_359789 : Nat := 4983230072969 + 3 ^ 40 * 359789 * 2
def baseEnd_359789 : Nat := 123163127467065371721911

theorem tailTrace_359789 : CollatzResearch.WordTrace tailWord_359789 prefixEnd_359789 123163127467065371721911 := by
  unfold tailWord_359789
  simp only [CollatzResearch.WordTrace]
  refine ⟨13122582893553374914258421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8748388595702249942838947 13122582893553374914258421)
  ·
    refine ⟨1230242146270628898211727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13122582893553374914258421 1230242146270628898211727)
    ·
      refine ⟨1845363219405943347317591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1230242146270628898211727 1845363219405943347317591)
      ·
        refine ⟨2768044829108915020976387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1845363219405943347317591 2768044829108915020976387)
        ·
          refine ⟨4152067243663372531464581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2768044829108915020976387 4152067243663372531464581)
          ·
            refine ⟨778512608186882349649609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4152067243663372531464581 778512608186882349649609)
            ·
              refine ⟨583884456140161762237207, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 778512608186882349649609 583884456140161762237207)
              ·
                refine ⟨875826684210242643355811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 583884456140161762237207 875826684210242643355811)
                ·
                  refine ⟨1313740026315363965033717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 875826684210242643355811 1313740026315363965033717)
                  ·
                    refine ⟨123163127467065371721911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1313740026315363965033717 123163127467065371721911)
                    ·
                      rfl

theorem cell22_359789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 2, 1, 1, 5].length) (baseStart_359789 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359789 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359789 prefixEnd_359789 := by exact prefixLift 359789
  have htrace : WordTrace (prefixWord ++ tailWord_359789) baseStart_359789 baseEnd_359789 := by
    simpa [prefixWord, tailWord_359789, baseEnd_359789] using wordTrace_append hprefix tailTrace_359789
  have hstable : (prefixWord ++ tailWord_359789).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359789).length < 2 ^ (prefixWord ++ tailWord_359789).sum := by decide
  have hdescent : baseEnd_359789 < baseStart_359789 := by decide
  rcases family_descends (prefixWord ++ tailWord_359789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359810 : List Nat := [3, 4, 2, 1, 1, 3, 2, 1, 1, 4]
def baseStart_359810 : Nat := 118140960795 + 359810 * 2 ^ 59
def prefixEnd_359810 : Nat := 4983230072969 + 3 ^ 40 * 359810 * 2
def baseEnd_359810 : Nat := 123170316196228316946847

theorem tailTrace_359810 : CollatzResearch.WordTrace tailWord_359810 prefixEnd_359810 123170316196228316946847 := by
  unfold tailWord_359810
  simp only [CollatzResearch.WordTrace]
  refine ⟨3280837206619323875193221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8748899217651530333848589 3280837206619323875193221)
  ·
    refine ⟨615156976241123226598729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3280837206619323875193221 615156976241123226598729)
    ·
      refine ⟨461367732180842419949047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615156976241123226598729 461367732180842419949047)
      ·
        refine ⟨692051598271263629923571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 461367732180842419949047 692051598271263629923571)
        ·
          refine ⟨1038077397406895444885357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692051598271263629923571 1038077397406895444885357)
          ·
            refine ⟨389279024027585791832009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1038077397406895444885357 389279024027585791832009)
            ·
              refine ⟨291959268020689343874007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389279024027585791832009 291959268020689343874007)
              ·
                refine ⟨437938902031034015811011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 291959268020689343874007 437938902031034015811011)
                ·
                  refine ⟨656908353046551023716517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 437938902031034015811011 656908353046551023716517)
                  ·
                    refine ⟨123170316196228316946847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 656908353046551023716517 123170316196228316946847)
                    ·
                      rfl

theorem cell22_359810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 1, 3, 2, 1, 1, 4].length) (baseStart_359810 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359810 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359810 prefixEnd_359810 := by exact prefixLift 359810
  have htrace : WordTrace (prefixWord ++ tailWord_359810) baseStart_359810 baseEnd_359810 := by
    simpa [prefixWord, tailWord_359810, baseEnd_359810] using wordTrace_append hprefix tailTrace_359810
  have hstable : (prefixWord ++ tailWord_359810).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359810).length < 2 ^ (prefixWord ++ tailWord_359810).sum := by decide
  have hdescent : baseEnd_359810 < baseStart_359810 := by decide
  rcases family_descends (prefixWord ++ tailWord_359810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359911 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 1, 4]
def baseStart_359911 : Nat := 118140960795 + 359911 * 2 ^ 59
def prefixEnd_359911 : Nat := 4983230072969 + 3 ^ 40 * 359911 * 2
def baseEnd_359911 : Nat := 123204890560297720171537

theorem tailTrace_359911 : CollatzResearch.WordTrace tailWord_359911 prefixEnd_359911 123204890560297720171537 := by
  unfold tailWord_359911
  simp only [CollatzResearch.WordTrace]
  refine ⟨13127032599111389750199587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8751355066074259833466391 13127032599111389750199587)
  ·
    refine ⟨19690548898667084625299381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13127032599111389750199587 19690548898667084625299381)
    ·
      refine ⟨1845988959250039183621817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19690548898667084625299381 1845988959250039183621817)
      ·
        refine ⟨1384491719437529387716363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1845988959250039183621817 1384491719437529387716363)
        ·
          refine ⟨2076737579156294081574545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1384491719437529387716363 2076737579156294081574545)
          ·
            refine ⟨1557553184367220561180909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2076737579156294081574545 1557553184367220561180909)
            ·
              refine ⟨584082444137707710442841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1557553184367220561180909 584082444137707710442841)
              ·
                refine ⟨438061833103280782832131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584082444137707710442841 438061833103280782832131)
                ·
                  refine ⟨657092749654921174248197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438061833103280782832131 657092749654921174248197)
                  ·
                    refine ⟨123204890560297720171537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 657092749654921174248197 123204890560297720171537)
                    ·
                      rfl

theorem cell22_359911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 4].length) (baseStart_359911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359911 prefixEnd_359911 := by exact prefixLift 359911
  have htrace : WordTrace (prefixWord ++ tailWord_359911) baseStart_359911 baseEnd_359911 := by
    simpa [prefixWord, tailWord_359911, baseEnd_359911] using wordTrace_append hprefix tailTrace_359911
  have hstable : (prefixWord ++ tailWord_359911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359911).length < 2 ^ (prefixWord ++ tailWord_359911).sum := by decide
  have hdescent : baseEnd_359911 < baseStart_359911 := by decide
  rcases family_descends (prefixWord ++ tailWord_359911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359937 : List Nat := [1, 2, 4, 1, 14]
def baseStart_359937 : Nat := 118140960795 + 359937 * 2 ^ 59
def prefixEnd_359937 : Nat := 4983230072969 + 3 ^ 40 * 359937 * 2
def baseEnd_359937 : Nat := 507052637414165921899

theorem tailTrace_359937 : CollatzResearch.WordTrace tailWord_359937 prefixEnd_359937 507052637414165921899 := by
  unfold tailWord_359937
  simp only [CollatzResearch.WordTrace]
  refine ⟨13127980897017196190646065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8751987264678130793764043 13127980897017196190646065)
  ·
    refine ⟨9845985672762897142984549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13127980897017196190646065 9845985672762897142984549)
    ·
      refine ⟨1846122313643043214309603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9845985672762897142984549 1846122313643043214309603)
      ·
        refine ⟨2769183470464564821464405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1846122313643043214309603 2769183470464564821464405)
        ·
          refine ⟨507052637414165921899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 14 2769183470464564821464405 507052637414165921899)
          ·
            rfl

theorem cell22_359937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 14].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 14].length) (baseStart_359937 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359937 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359937 prefixEnd_359937 := by exact prefixLift 359937
  have htrace : WordTrace (prefixWord ++ tailWord_359937) baseStart_359937 baseEnd_359937 := by
    simpa [prefixWord, tailWord_359937, baseEnd_359937] using wordTrace_append hprefix tailTrace_359937
  have hstable : (prefixWord ++ tailWord_359937).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359937).length < 2 ^ (prefixWord ++ tailWord_359937).sum := by decide
  have hdescent : baseEnd_359937 < baseStart_359937 := by decide
  rcases family_descends (prefixWord ++ tailWord_359937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359943 : List Nat := [1, 1, 4, 3, 2, 1, 4, 2, 4]
def baseStart_359943 : Nat := 118140960795 + 359943 * 2 ^ 59
def prefixEnd_359943 : Nat := 4983230072969 + 3 ^ 40 * 359943 * 2
def baseEnd_359943 : Nat := 41071948271420101123813

theorem tailTrace_359943 : CollatzResearch.WordTrace tailWord_359943 prefixEnd_359943 41071948271420101123813 := by
  unfold tailWord_359943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13128199734995459215364483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8752133156663639476909655 13128199734995459215364483)
  ·
    refine ⟨19692299602493188823046725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13128199734995459215364483 19692299602493188823046725)
    ·
      refine ⟨3692306175467472904321261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19692299602493188823046725 3692306175467472904321261)
      ·
        refine ⟨1384614815800302339120473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3692306175467472904321261 1384614815800302339120473)
        ·
          refine ⟨1038461111850226754340355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1384614815800302339120473 1038461111850226754340355)
          ·
            refine ⟨1557691667775340131510533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038461111850226754340355 1557691667775340131510533)
            ·
              refine ⟨292067187707876274658225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1557691667775340131510533 292067187707876274658225)
              ·
                refine ⟨219050390780907205993669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292067187707876274658225 219050390780907205993669)
                ·
                  refine ⟨41071948271420101123813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219050390780907205993669 41071948271420101123813)
                  ·
                    rfl

theorem cell22_359943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 1, 4, 2, 4].length) (baseStart_359943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359943 prefixEnd_359943 := by exact prefixLift 359943
  have htrace : WordTrace (prefixWord ++ tailWord_359943) baseStart_359943 baseEnd_359943 := by
    simpa [prefixWord, tailWord_359943, baseEnd_359943] using wordTrace_append hprefix tailTrace_359943
  have hstable : (prefixWord ++ tailWord_359943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359943).length < 2 ^ (prefixWord ++ tailWord_359943).sum := by decide
  have hdescent : baseEnd_359943 < baseStart_359943 := by decide
  rcases family_descends (prefixWord ++ tailWord_359943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359971 : List Nat := [1, 1, 1, 4, 5, 1, 3, 6]
def baseStart_359971 : Nat := 118140960795 + 359971 * 2 ^ 59
def prefixEnd_359971 : Nat := 4983230072969 + 3 ^ 40 * 359971 * 2
def baseEnd_359971 : Nat := 13691714420719729296817

theorem tailTrace_359971 : CollatzResearch.WordTrace tailWord_359971 prefixEnd_359971 13691714420719729296817 := by
  unfold tailWord_359971
  simp only [CollatzResearch.WordTrace]
  refine ⟨13129220978894019997383767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8752813985929346664922511 13129220978894019997383767)
  ·
    refine ⟨19693831468341029996075651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13129220978894019997383767 19693831468341029996075651)
    ·
      refine ⟨29540747202511544994113477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19693831468341029996075651 29540747202511544994113477)
      ·
        refine ⟨5538890100470914686396277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29540747202511544994113477 5538890100470914686396277)
        ·
          refine ⟨519270946919148251849651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5538890100470914686396277 519270946919148251849651)
          ·
            refine ⟨778906420378722377774477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519270946919148251849651 778906420378722377774477)
            ·
              refine ⟨292089907642020891665429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 778906420378722377774477 292089907642020891665429)
              ·
                refine ⟨13691714420719729296817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 292089907642020891665429 13691714420719729296817)
                ·
                  rfl

theorem cell22_359971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 5, 1, 3, 6].length) (baseStart_359971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359971 prefixEnd_359971 := by exact prefixLift 359971
  have htrace : WordTrace (prefixWord ++ tailWord_359971) baseStart_359971 baseEnd_359971 := by
    simpa [prefixWord, tailWord_359971, baseEnd_359971] using wordTrace_append hprefix tailTrace_359971
  have hstable : (prefixWord ++ tailWord_359971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359971).length < 2 ^ (prefixWord ++ tailWord_359971).sum := by decide
  have hdescent : baseEnd_359971 < baseStart_359971 := by decide
  rcases family_descends (prefixWord ++ tailWord_359971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_359999 : List Nat := [1, 1, 2, 2, 3, 4, 1, 1, 7]
def baseStart_359999 : Nat := 118140960795 + 359999 * 2 ^ 59
def prefixEnd_359999 : Nat := 4983230072969 + 3 ^ 40 * 359999 * 2
def baseEnd_359999 : Nat := 41078338252898274657089

theorem tailTrace_359999 : CollatzResearch.WordTrace tailWord_359999 prefixEnd_359999 41078338252898274657089 := by
  unfold tailWord_359999
  simp only [CollatzResearch.WordTrace]
  refine ⟨13130242222792580779403051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8753494815195053852935367 13130242222792580779403051)
  ·
    refine ⟨19695363334188871169104577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13130242222792580779403051 19695363334188871169104577)
    ·
      refine ⟨14771522500641653376828433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19695363334188871169104577 14771522500641653376828433)
      ·
        refine ⟨11078641875481240032621325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14771522500641653376828433 11078641875481240032621325)
        ·
          refine ⟨4154490703305465012232997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11078641875481240032621325 4154490703305465012232997)
          ·
            refine ⟨778967006869774689793687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4154490703305465012232997 778967006869774689793687)
            ·
              refine ⟨1168450510304662034690531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 778967006869774689793687 1168450510304662034690531)
              ·
                refine ⟨1752675765456993052035797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1168450510304662034690531 1752675765456993052035797)
                ·
                  refine ⟨41078338252898274657089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1752675765456993052035797 41078338252898274657089)
                  ·
                    rfl

theorem cell22_359999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 1, 7].length) (baseStart_359999 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_359999 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_359999 prefixEnd_359999 := by exact prefixLift 359999
  have htrace : WordTrace (prefixWord ++ tailWord_359999) baseStart_359999 baseEnd_359999 := by
    simpa [prefixWord, tailWord_359999, baseEnd_359999] using wordTrace_append hprefix tailTrace_359999
  have hstable : (prefixWord ++ tailWord_359999).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_359999).length < 2 ^ (prefixWord ++ tailWord_359999).sum := by decide
  have hdescent : baseEnd_359999 < baseStart_359999 := by decide
  rcases family_descends (prefixWord ++ tailWord_359999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360016 : List Nat := [2, 1, 1, 1, 1, 3, 7, 1, 5]
def baseStart_360016 : Nat := 118140960795 + 360016 * 2 ^ 59
def prefixEnd_360016 : Nat := 4983230072969 + 3 ^ 40 * 360016 * 2
def baseEnd_360016 : Nat := 41080278068704148765405

theorem tailTrace_360016 : CollatzResearch.WordTrace tailWord_360016 prefixEnd_360016 41080278068704148765405 := by
  unfold tailWord_360016
  simp only [CollatzResearch.WordTrace]
  refine ⟨6565431131865496341385951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8753908175820661788514601 6565431131865496341385951)
  ·
    refine ⟨9848146697798244512078927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6565431131865496341385951 9848146697798244512078927)
    ·
      refine ⟨14772220046697366768118391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9848146697798244512078927 14772220046697366768118391)
      ·
        refine ⟨22158330070046050152177587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14772220046697366768118391 22158330070046050152177587)
        ·
          refine ⟨33237495105069075228266381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22158330070046050152177587 33237495105069075228266381)
          ·
            refine ⟨12464060664400903210599893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33237495105069075228266381 12464060664400903210599893)
            ·
              refine ⟨292126421821896168998435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12464060664400903210599893 292126421821896168998435)
              ·
                refine ⟨438189632732844253497653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 292126421821896168998435 438189632732844253497653)
                ·
                  refine ⟨41080278068704148765405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438189632732844253497653 41080278068704148765405)
                  ·
                    rfl

theorem cell22_360016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 7, 1, 5].length) (baseStart_360016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360016 prefixEnd_360016 := by exact prefixLift 360016
  have htrace : WordTrace (prefixWord ++ tailWord_360016) baseStart_360016 baseEnd_360016 := by
    simpa [prefixWord, tailWord_360016, baseEnd_360016] using wordTrace_append hprefix tailTrace_360016
  have hstable : (prefixWord ++ tailWord_360016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360016).length < 2 ^ (prefixWord ++ tailWord_360016).sum := by decide
  have hdescent : baseEnd_360016 < baseStart_360016 := by decide
  rcases family_descends (prefixWord ++ tailWord_360016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360022 : List Nat := [5, 2, 2, 2, 1, 2, 2, 6]
def baseStart_360022 : Nat := 118140960795 + 360022 * 2 ^ 59
def prefixEnd_360022 : Nat := 4983230072969 + 3 ^ 40 * 360022 * 2
def baseEnd_360022 : Nat := 13693654236525603405133

theorem tailTrace_360022 : CollatzResearch.WordTrace tailWord_360022 prefixEnd_360022 13693654236525603405133 := by
  unfold tailWord_360022
  simp only [CollatzResearch.WordTrace]
  refine ⟨820692568856828481718145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8754054067806170471660213 820692568856828481718145)
  ·
    refine ⟨615519426642621361288609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 820692568856828481718145 615519426642621361288609)
    ·
      refine ⟨461639569981966020966457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 615519426642621361288609 461639569981966020966457)
      ·
        refine ⟨346229677486474515724843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 461639569981966020966457 346229677486474515724843)
        ·
          refine ⟨519344516229711773587265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346229677486474515724843 519344516229711773587265)
          ·
            refine ⟨389508387172283830190449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519344516229711773587265 389508387172283830190449)
            ·
              refine ⟨292131290379212872642837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 389508387172283830190449 292131290379212872642837)
              ·
                refine ⟨13693654236525603405133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 292131290379212872642837 13693654236525603405133)
                ·
                  rfl

theorem cell22_360022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 2, 1, 2, 2, 6].length) (baseStart_360022 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360022 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360022 prefixEnd_360022 := by exact prefixLift 360022
  have htrace : WordTrace (prefixWord ++ tailWord_360022) baseStart_360022 baseEnd_360022 := by
    simpa [prefixWord, tailWord_360022, baseEnd_360022] using wordTrace_append hprefix tailTrace_360022
  have hstable : (prefixWord ++ tailWord_360022).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360022).length < 2 ^ (prefixWord ++ tailWord_360022).sum := by decide
  have hdescent : baseEnd_360022 < baseStart_360022 := by decide
  rcases family_descends (prefixWord ++ tailWord_360022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360061 : List Nat := [1, 4, 1, 1, 4, 1, 3, 1, 6]
def baseStart_360061 : Nat := 118140960795 + 360061 * 2 ^ 59
def prefixEnd_360061 : Nat := 4983230072969 + 3 ^ 40 * 360061 * 2
def baseEnd_360061 : Nat := 41085412875249109640359

theorem tailTrace_360061 : CollatzResearch.WordTrace tailWord_360061 prefixEnd_360061 41085412875249109640359 := by
  unfold tailWord_360061
  simp only [CollatzResearch.WordTrace]
  refine ⟨13132503548567965368160037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8755002365711976912106691 13132503548567965368160037)
  ·
    refine ⟨2462344415356493506530007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13132503548567965368160037 2462344415356493506530007)
    ·
      refine ⟨3693516623034740259795011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2462344415356493506530007 3693516623034740259795011)
      ·
        refine ⟨5540274934552110389692517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3693516623034740259795011 5540274934552110389692517)
        ·
          refine ⟨1038801550228520698067347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5540274934552110389692517 1038801550228520698067347)
          ·
            refine ⟨1558202325342781047101021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1038801550228520698067347 1558202325342781047101021)
            ·
              refine ⟨584325872003542892662883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558202325342781047101021 584325872003542892662883)
              ·
                refine ⟨876488808005314338994325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584325872003542892662883 876488808005314338994325)
                ·
                  refine ⟨41085412875249109640359, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 876488808005314338994325 41085412875249109640359)
                  ·
                    rfl

theorem cell22_360061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 4, 1, 3, 1, 6].length) (baseStart_360061 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360061 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360061 prefixEnd_360061 := by exact prefixLift 360061
  have htrace : WordTrace (prefixWord ++ tailWord_360061) baseStart_360061 baseEnd_360061 := by
    simpa [prefixWord, tailWord_360061, baseEnd_360061] using wordTrace_append hprefix tailTrace_360061
  have hstable : (prefixWord ++ tailWord_360061).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360061).length < 2 ^ (prefixWord ++ tailWord_360061).sum := by decide
  have hdescent : baseEnd_360061 < baseStart_360061 := by decide
  rcases family_descends (prefixWord ++ tailWord_360061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360168 : List Nat := [2, 1, 4, 1, 3, 1, 3, 2, 5]
def baseStart_360168 : Nat := 118140960795 + 360168 * 2 ^ 59
def prefixEnd_360168 : Nat := 4983230072969 + 3 ^ 40 * 360168 * 2
def baseEnd_360168 : Nat := 41097622304144905498583

theorem tailTrace_360168 : CollatzResearch.WordTrace tailWord_360168 prefixEnd_360168 41097622304144905498583 := by
  unfold tailWord_360168
  simp only [CollatzResearch.WordTrace]
  refine ⟨6568203079590161321152579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8757604106120215094870105 6568203079590161321152579)
  ·
    refine ⟨9852304619385241981728869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6568203079590161321152579 9852304619385241981728869)
    ·
      refine ⟨1847307116134732871574163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9852304619385241981728869 1847307116134732871574163)
      ·
        refine ⟨2770960674202099307361245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1847307116134732871574163 2770960674202099307361245)
        ·
          refine ⟨1039110252825787240260467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2770960674202099307361245 1039110252825787240260467)
          ·
            refine ⟨1558665379238680860390701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1039110252825787240260467 1558665379238680860390701)
            ·
              refine ⟨584499517214505322646513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1558665379238680860390701 584499517214505322646513)
              ·
                refine ⟨438374637910878991984885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584499517214505322646513 438374637910878991984885)
                ·
                  refine ⟨41097622304144905498583, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438374637910878991984885 41097622304144905498583)
                  ·
                    rfl

theorem cell22_360168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 3, 2, 5].length) (baseStart_360168 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360168 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360168 prefixEnd_360168 := by exact prefixLift 360168
  have htrace : WordTrace (prefixWord ++ tailWord_360168) baseStart_360168 baseEnd_360168 := by
    simpa [prefixWord, tailWord_360168, baseEnd_360168] using wordTrace_append hprefix tailTrace_360168
  have hstable : (prefixWord ++ tailWord_360168).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360168).length < 2 ^ (prefixWord ++ tailWord_360168).sum := by decide
  have hdescent : baseEnd_360168 < baseStart_360168 := by decide
  rcases family_descends (prefixWord ++ tailWord_360168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360241 : List Nat := [1, 2, 2, 3, 2, 2, 1, 9]
def baseStart_360241 : Nat := 118140960795 + 360241 * 2 ^ 59
def prefixEnd_360241 : Nat := 4983230072969 + 3 ^ 40 * 360241 * 2
def baseEnd_360241 : Nat := 13701984033809651046725

theorem tailTrace_360241 : CollatzResearch.WordTrace tailWord_360241 prefixEnd_360241 13701984033809651046725 := by
  unfold tailWord_360241
  simp only [CollatzResearch.WordTrace]
  refine ⟨13139068687915856109712577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8759379125277237406475051 13139068687915856109712577)
  ·
    refine ⟨9854301515936892082284433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13139068687915856109712577 9854301515936892082284433)
    ·
      refine ⟨7390726136952669061713325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9854301515936892082284433 7390726136952669061713325)
      ·
        refine ⟨2771522301357250898142497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7390726136952669061713325 2771522301357250898142497)
        ·
          refine ⟨2078641726017938173606873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2771522301357250898142497 2078641726017938173606873)
          ·
            refine ⟨1558981294513453630205155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2078641726017938173606873 1558981294513453630205155)
            ·
              refine ⟨2338471941770180445307733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1558981294513453630205155 2338471941770180445307733)
              ·
                refine ⟨13701984033809651046725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2338471941770180445307733 13701984033809651046725)
                ·
                  rfl

theorem cell22_360241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 9].length) (baseStart_360241 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360241 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360241 prefixEnd_360241 := by exact prefixLift 360241
  have htrace : WordTrace (prefixWord ++ tailWord_360241) baseStart_360241 baseEnd_360241 := by
    simpa [prefixWord, tailWord_360241, baseEnd_360241] using wordTrace_append hprefix tailTrace_360241
  have hstable : (prefixWord ++ tailWord_360241).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360241).length < 2 ^ (prefixWord ++ tailWord_360241).sum := by decide
  have hdescent : baseEnd_360241 < baseStart_360241 := by decide
  rcases family_descends (prefixWord ++ tailWord_360241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360249 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 1, 4]
def baseStart_360249 : Nat := 118140960795 + 360249 * 2 ^ 59
def prefixEnd_360249 : Nat := 4983230072969 + 3 ^ 40 * 360249 * 2
def baseEnd_360249 : Nat := 123320594867777505220501

theorem tailTrace_360249 : CollatzResearch.WordTrace tailWord_360249 prefixEnd_360249 123320594867777505220501 := by
  unfold tailWord_360249
  simp only [CollatzResearch.WordTrace]
  refine ⟨13139360471886873476003801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8759573647924582317335867 13139360471886873476003801)
  ·
    refine ⟨9854520353915155107002851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13139360471886873476003801 9854520353915155107002851)
    ·
      refine ⟨14781780530872732660504277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9854520353915155107002851 14781780530872732660504277)
      ·
        refine ⟨346447981192329671730569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14781780530872732660504277 346447981192329671730569)
        ·
          refine ⟨259835985894247253797927, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 346447981192329671730569 259835985894247253797927)
          ·
            refine ⟨389753978841370880696891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 259835985894247253797927 389753978841370880696891)
            ·
              refine ⟨584630968262056321045337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389753978841370880696891 584630968262056321045337)
              ·
                refine ⟨438473226196542240784003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 584630968262056321045337 438473226196542240784003)
                ·
                  refine ⟨657709839294813361176005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 438473226196542240784003 657709839294813361176005)
                  ·
                    refine ⟨123320594867777505220501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 657709839294813361176005 123320594867777505220501)
                    ·
                      rfl

theorem cell22_360249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 4].length) (baseStart_360249 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360249 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360249 prefixEnd_360249 := by exact prefixLift 360249
  have htrace : WordTrace (prefixWord ++ tailWord_360249) baseStart_360249 baseEnd_360249 := by
    simpa [prefixWord, tailWord_360249, baseEnd_360249] using wordTrace_append hprefix tailTrace_360249
  have hstable : (prefixWord ++ tailWord_360249).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360249).length < 2 ^ (prefixWord ++ tailWord_360249).sum := by decide
  have hdescent : baseEnd_360249 < baseStart_360249 := by decide
  rcases family_descends (prefixWord ++ tailWord_360249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360262 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 1, 5]
def baseStart_360262 : Nat := 118140960795 + 360262 * 2 ^ 59
def prefixEnd_360262 : Nat := 4983230072969 + 3 ^ 40 * 360262 * 2
def baseEnd_360262 : Nat := 123325045033449804645461

theorem tailTrace_360262 : CollatzResearch.WordTrace tailWord_360262 prefixEnd_360262 123325045033449804645461 := by
  unfold tailWord_360262
  simp only [CollatzResearch.WordTrace]
  refine ⟨410619831901243021757095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8759889747226517797484693 410619831901243021757095)
  ·
    refine ⟨615929747851864532635643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 410619831901243021757095 615929747851864532635643)
    ·
      refine ⟨923894621777796798953465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 615929747851864532635643 923894621777796798953465)
      ·
        refine ⟨692920966333347599215099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 923894621777796798953465 692920966333347599215099)
        ·
          refine ⟨1039381449500021398822649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 692920966333347599215099 1039381449500021398822649)
          ·
            refine ⟨779536087125016049116987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1039381449500021398822649 779536087125016049116987)
            ·
              refine ⟨1169304130687524073675481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 779536087125016049116987 1169304130687524073675481)
              ·
                refine ⟨876978098015643055256611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1169304130687524073675481 876978098015643055256611)
                ·
                  refine ⟨1315467147023464582884917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 876978098015643055256611 1315467147023464582884917)
                  ·
                    refine ⟨123325045033449804645461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1315467147023464582884917 123325045033449804645461)
                    ·
                      rfl

theorem cell22_360262_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_360262 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360262 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360262 prefixEnd_360262 := by exact prefixLift 360262
  have htrace : WordTrace (prefixWord ++ tailWord_360262) baseStart_360262 baseEnd_360262 := by
    simpa [prefixWord, tailWord_360262, baseEnd_360262] using wordTrace_append hprefix tailTrace_360262
  have hstable : (prefixWord ++ tailWord_360262).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360262).length < 2 ^ (prefixWord ++ tailWord_360262).sum := by decide
  have hdescent : baseEnd_360262 < baseStart_360262 := by decide
  rcases family_descends (prefixWord ++ tailWord_360262) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360331 : List Nat := [1, 1, 1, 1, 4, 2, 1, 1, 10]
def baseStart_360331 : Nat := 118140960795 + 360331 * 2 ^ 59
def prefixEnd_360331 : Nat := 4983230072969 + 3 ^ 40 * 360331 * 2
def baseEnd_360331 : Nat := 41116221714518874890083

theorem tailTrace_360331 : CollatzResearch.WordTrace tailWord_360331 prefixEnd_360331 41116221714518874890083 := by
  unfold tailWord_360331
  simp only [CollatzResearch.WordTrace]
  refine ⟨13142351257589801480488847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8761567505059867653659231 13142351257589801480488847)
  ·
    refine ⟨19713526886384702220733271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13142351257589801480488847 19713526886384702220733271)
    ·
      refine ⟨29570290329577053331099907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19713526886384702220733271 29570290329577053331099907)
      ·
        refine ⟨44355435494365579996649861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29570290329577053331099907 44355435494365579996649861)
        ·
          refine ⟨8316644155193546249371849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 44355435494365579996649861 8316644155193546249371849)
          ·
            refine ⟨6237483116395159687028887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8316644155193546249371849 6237483116395159687028887)
            ·
              refine ⟨9356224674592739530543331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6237483116395159687028887 9356224674592739530543331)
              ·
                refine ⟨14034337011889109295814997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9356224674592739530543331 14034337011889109295814997)
                ·
                  refine ⟨41116221714518874890083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14034337011889109295814997 41116221714518874890083)
                  ·
                    rfl

theorem cell22_360331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 1, 1, 10].length) (baseStart_360331 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360331 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360331 prefixEnd_360331 := by exact prefixLift 360331
  have htrace : WordTrace (prefixWord ++ tailWord_360331) baseStart_360331 baseEnd_360331 := by
    simpa [prefixWord, tailWord_360331, baseEnd_360331] using wordTrace_append hprefix tailTrace_360331
  have hstable : (prefixWord ++ tailWord_360331).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360331).length < 2 ^ (prefixWord ++ tailWord_360331).sum := by decide
  have hdescent : baseEnd_360331 < baseStart_360331 := by decide
  rcases family_descends (prefixWord ++ tailWord_360331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360363 : List Nat := [1, 1, 1, 1, 2, 1, 1, 3, 8, 3]
def baseStart_360363 : Nat := 118140960795 + 360363 * 2 ^ 59
def prefixEnd_360363 : Nat := 4983230072969 + 3 ^ 40 * 360363 * 2
def baseEnd_360363 : Nat := 123359619397519207870151

theorem tailTrace_360363 : CollatzResearch.WordTrace tailWord_360363 prefixEnd_360363 123359619397519207870151 := by
  unfold tailWord_360363
  simp only [CollatzResearch.WordTrace]
  refine ⟨13143518393473870945653743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8762345595649247297102495 13143518393473870945653743)
  ·
    refine ⟨19715277590210806418480615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13143518393473870945653743 19715277590210806418480615)
    ·
      refine ⟨29572916385316209627720923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19715277590210806418480615 29572916385316209627720923)
      ·
        refine ⟨44359374577974314441581385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29572916385316209627720923 44359374577974314441581385)
        ·
          refine ⟨33269530933480735831186039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44359374577974314441581385 33269530933480735831186039)
          ·
            refine ⟨49904296400221103746779059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33269530933480735831186039 49904296400221103746779059)
            ·
              refine ⟨74856444600331655620168589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 49904296400221103746779059 74856444600331655620168589)
              ·
                refine ⟨28071166725124370857563221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 74856444600331655620168589 28071166725124370857563221)
                ·
                  refine ⟨328958985060051220987069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28071166725124370857563221 328958985060051220987069)
                  ·
                    refine ⟨123359619397519207870151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 328958985060051220987069 123359619397519207870151)
                    ·
                      rfl

theorem cell22_360363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 3, 8, 3].length) (baseStart_360363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360363 prefixEnd_360363 := by exact prefixLift 360363
  have htrace : WordTrace (prefixWord ++ tailWord_360363) baseStart_360363 baseEnd_360363 := by
    simpa [prefixWord, tailWord_360363, baseEnd_360363] using wordTrace_append hprefix tailTrace_360363
  have hstable : (prefixWord ++ tailWord_360363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360363).length < 2 ^ (prefixWord ++ tailWord_360363).sum := by decide
  have hdescent : baseEnd_360363 < baseStart_360363 := by decide
  rcases family_descends (prefixWord ++ tailWord_360363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360382 : List Nat := [4, 2, 1, 1, 1, 3, 3, 3, 4]
def baseStart_360382 : Nat := 118140960795 + 360382 * 2 ^ 59
def prefixEnd_360382 : Nat := 4983230072969 + 3 ^ 40 * 360382 * 2
def baseEnd_360382 : Nat := 41122041161936497215031

theorem tailTrace_360382 : CollatzResearch.WordTrace tailWord_360382 prefixEnd_360382 41122041161936497215031 := by
  unfold tailWord_360382
  simp only [CollatzResearch.WordTrace]
  refine ⟨1643026422550629648824425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8762807586936691460396933 1643026422550629648824425)
  ·
    refine ⟨1232269816912972236618319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1643026422550629648824425 1232269816912972236618319)
    ·
      refine ⟨1848404725369458354927479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232269816912972236618319 1848404725369458354927479)
      ·
        refine ⟨2772607088054187532391219, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1848404725369458354927479 2772607088054187532391219)
        ·
          refine ⟨4158910632081281298586829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2772607088054187532391219 4158910632081281298586829)
          ·
            refine ⟨1559591487030480486970061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4158910632081281298586829 1559591487030480486970061)
            ·
              refine ⟨584846807636430182613773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1559591487030480486970061 584846807636430182613773)
              ·
                refine ⟨219317552863661318480165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 584846807636430182613773 219317552863661318480165)
                ·
                  refine ⟨41122041161936497215031, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219317552863661318480165 41122041161936497215031)
                  ·
                    rfl

theorem cell22_360382_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 3, 3, 4].length) (baseStart_360382 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360382 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360382 prefixEnd_360382 := by exact prefixLift 360382
  have htrace : WordTrace (prefixWord ++ tailWord_360382) baseStart_360382 baseEnd_360382 := by
    simpa [prefixWord, tailWord_360382, baseEnd_360382] using wordTrace_append hprefix tailTrace_360382
  have hstable : (prefixWord ++ tailWord_360382).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360382).length < 2 ^ (prefixWord ++ tailWord_360382).sum := by decide
  have hdescent : baseEnd_360382 < baseStart_360382 := by decide
  rcases family_descends (prefixWord ++ tailWord_360382) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360410 : List Nat := [3, 1, 1, 2, 5, 1, 2, 7]
def baseStart_360410 : Nat := 118140960795 + 360410 * 2 ^ 59
def prefixEnd_360410 : Nat := 4983230072969 + 3 ^ 40 * 360410 * 2
def baseEnd_360410 : Nat := 13708412050891861327223

theorem tailTrace_360410 : CollatzResearch.WordTrace tailWord_360410 prefixEnd_360410 13708412050891861327223 := by
  unfold tailWord_360410
  simp only [CollatzResearch.WordTrace]
  refine ⟨3286308156075899493153671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8763488416202398648409789 3286308156075899493153671)
  ·
    refine ⟨4929462234113849239730507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3286308156075899493153671 4929462234113849239730507)
    ·
      refine ⟨7394193351170773859595761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4929462234113849239730507 7394193351170773859595761)
      ·
        refine ⟨5545645013378080394696821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7394193351170773859595761 5545645013378080394696821)
        ·
          refine ⟨519904220004195037002827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5545645013378080394696821 519904220004195037002827)
          ·
            refine ⟨779856330006292555504241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519904220004195037002827 779856330006292555504241)
            ·
              refine ⟨584892247504719416628181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779856330006292555504241 584892247504719416628181)
              ·
                refine ⟨13708412050891861327223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 584892247504719416628181 13708412050891861327223)
                ·
                  rfl

theorem cell22_360410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 2, 7].length) (baseStart_360410 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360410 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360410 prefixEnd_360410 := by exact prefixLift 360410
  have htrace : WordTrace (prefixWord ++ tailWord_360410) baseStart_360410 baseEnd_360410 := by
    simpa [prefixWord, tailWord_360410, baseEnd_360410] using wordTrace_append hprefix tailTrace_360410
  have hstable : (prefixWord ++ tailWord_360410).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360410).length < 2 ^ (prefixWord ++ tailWord_360410).sum := by decide
  have hdescent : baseEnd_360410 < baseStart_360410 := by decide
  rcases family_descends (prefixWord ++ tailWord_360410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360429 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_360429 : Nat := 118140960795 + 360429 * 2 ^ 59
def prefixEnd_360429 : Nat := 4983230072969 + 3 ^ 40 * 360429 * 2
def baseEnd_360429 : Nat := 123382212546317035719949

theorem tailTrace_360429 : CollatzResearch.WordTrace tailWord_360429 prefixEnd_360429 123382212546317035719949 := by
  unfold tailWord_360429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13145925611234764217556341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8763950407489842811704227 13145925611234764217556341)
  ·
    refine ⟨1232430526053259145395907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13145925611234764217556341 1232430526053259145395907)
    ·
      refine ⟨1848645789079888718093861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1232430526053259145395907 1848645789079888718093861)
      ·
        refine ⟨346621085452479134642599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1848645789079888718093861 346621085452479134642599)
        ·
          refine ⟨519931628178718701963899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346621085452479134642599 519931628178718701963899)
          ·
            refine ⟨779897442268078052945849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 519931628178718701963899 779897442268078052945849)
            ·
              refine ⟨584923081701058539709387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 779897442268078052945849 584923081701058539709387)
              ·
                refine ⟨877384622551587809564081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 584923081701058539709387 877384622551587809564081)
                ·
                  refine ⟨658038466913690857173061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 877384622551587809564081 658038466913690857173061)
                  ·
                    refine ⟨123382212546317035719949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658038466913690857173061 123382212546317035719949)
                    ·
                      rfl

theorem cell22_360429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_360429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360429 prefixEnd_360429 := by exact prefixLift 360429
  have htrace : WordTrace (prefixWord ++ tailWord_360429) baseStart_360429 baseEnd_360429 := by
    simpa [prefixWord, tailWord_360429, baseEnd_360429] using wordTrace_append hprefix tailTrace_360429
  have hstable : (prefixWord ++ tailWord_360429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360429).length < 2 ^ (prefixWord ++ tailWord_360429).sum := by decide
  have hdescent : baseEnd_360429 < baseStart_360429 := by decide
  rcases family_descends (prefixWord ++ tailWord_360429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360455 : List Nat := [1, 1, 4, 3, 1, 2, 1, 4, 5]
def baseStart_360455 : Nat := 118140960795 + 360455 * 2 ^ 59
def prefixEnd_360455 : Nat := 4983230072969 + 3 ^ 40 * 360455 * 2
def baseEnd_360455 : Nat := 41130370959220544856623

theorem tailTrace_360455 : CollatzResearch.WordTrace tailWord_360455 prefixEnd_360455 41130370959220544856623 := by
  unfold tailWord_360455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13146873909140570658002819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8764582606093713772001879 13146873909140570658002819)
  ·
    refine ⟨19720310863710855987004229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13146873909140570658002819 19720310863710855987004229)
    ·
      refine ⟨3697558286945785497563293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19720310863710855987004229 3697558286945785497563293)
      ·
        refine ⟨1386584357604669561586235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3697558286945785497563293 1386584357604669561586235)
        ·
          refine ⟨2079876536407004342379353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1386584357604669561586235 2079876536407004342379353)
          ·
            refine ⟨1559907402305253256784515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2079876536407004342379353 1559907402305253256784515)
            ·
              refine ⟨2339861103457879885176773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1559907402305253256784515 2339861103457879885176773)
              ·
                refine ⟨438723956898352478470645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2339861103457879885176773 438723956898352478470645)
                ·
                  refine ⟨41130370959220544856623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 438723956898352478470645 41130370959220544856623)
                  ·
                    rfl

theorem cell22_360455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 2, 1, 4, 5].length) (baseStart_360455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360455 prefixEnd_360455 := by exact prefixLift 360455
  have htrace : WordTrace (prefixWord ++ tailWord_360455) baseStart_360455 baseEnd_360455 := by
    simpa [prefixWord, tailWord_360455, baseEnd_360455] using wordTrace_append hprefix tailTrace_360455
  have hstable : (prefixWord ++ tailWord_360455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360455).length < 2 ^ (prefixWord ++ tailWord_360455).sum := by decide
  have hdescent : baseEnd_360455 < baseStart_360455 := by decide
  rcases family_descends (prefixWord ++ tailWord_360455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360461 : List Nat := [1, 7, 1, 2, 1, 2, 1, 7]
def baseStart_360461 : Nat := 118140960795 + 360461 * 2 ^ 59
def prefixEnd_360461 : Nat := 4983230072969 + 3 ^ 40 * 360461 * 2
def baseEnd_360461 : Nat := 13710351866697735435539

theorem tailTrace_360461 : CollatzResearch.WordTrace tailWord_360461 prefixEnd_360461 13710351866697735435539 := by
  unfold tailWord_360461
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147092747118833682721237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8764728498079222455147491 13147092747118833682721237)
  ·
    refine ⟨308134986260597664438779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 13147092747118833682721237 308134986260597664438779)
    ·
      refine ⟨462202479390896496658169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308134986260597664438779 462202479390896496658169)
      ·
        refine ⟨346651859543172372493627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 462202479390896496658169 346651859543172372493627)
        ·
          refine ⟨519977789314758558740441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 346651859543172372493627 519977789314758558740441)
          ·
            refine ⟨389983341986068919055331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 519977789314758558740441 389983341986068919055331)
            ·
              refine ⟨584975012979103378582997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 389983341986068919055331 584975012979103378582997)
              ·
                refine ⟨13710351866697735435539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 584975012979103378582997 13710351866697735435539)
                ·
                  rfl

theorem cell22_360461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 1, 7].length) (baseStart_360461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360461 prefixEnd_360461 := by exact prefixLift 360461
  have htrace : WordTrace (prefixWord ++ tailWord_360461) baseStart_360461 baseEnd_360461 := by
    simpa [prefixWord, tailWord_360461, baseEnd_360461] using wordTrace_append hprefix tailTrace_360461
  have hstable : (prefixWord ++ tailWord_360461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360461).length < 2 ^ (prefixWord ++ tailWord_360461).sum := by decide
  have hdescent : baseEnd_360461 < baseStart_360461 := by decide
  rcases family_descends (prefixWord ++ tailWord_360461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360485 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 3, 4]
def baseStart_360485 : Nat := 118140960795 + 360485 * 2 ^ 59
def prefixEnd_360485 : Nat := 4983230072969 + 3 ^ 40 * 360485 * 2
def baseEnd_360485 : Nat := 123401382490751556319777

theorem tailTrace_360485 : CollatzResearch.WordTrace tailWord_360485 prefixEnd_360485 123401382490751556319777 := by
  unfold tailWord_360485
  simp only [CollatzResearch.WordTrace]
  refine ⟨13147968099031885781594909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8765312066021257187729939 13147968099031885781594909)
  ·
    refine ⟨4930488037136957168098091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13147968099031885781594909 4930488037136957168098091)
    ·
      refine ⟨7395732055705435752147137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4930488037136957168098091 7395732055705435752147137)
      ·
        refine ⟨5546799041779076814110353, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7395732055705435752147137 5546799041779076814110353)
        ·
          refine ⟨4160099281334307610582765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5546799041779076814110353 4160099281334307610582765)
          ·
            refine ⟨1560037230500365353968537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4160099281334307610582765 1560037230500365353968537)
            ·
              refine ⟨1170027922875274015476403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560037230500365353968537 1170027922875274015476403)
              ·
                refine ⟨1755041884312911023214605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1170027922875274015476403 1755041884312911023214605)
                ·
                  refine ⟨658140706617341633705477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1755041884312911023214605 658140706617341633705477)
                  ·
                    refine ⟨123401382490751556319777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658140706617341633705477 123401382490751556319777)
                    ·
                      rfl

theorem cell22_360485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 4].length) (baseStart_360485 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360485 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360485 prefixEnd_360485 := by exact prefixLift 360485
  have htrace : WordTrace (prefixWord ++ tailWord_360485) baseStart_360485 baseEnd_360485 := by
    simpa [prefixWord, tailWord_360485, baseEnd_360485] using wordTrace_append hprefix tailTrace_360485
  have hstable : (prefixWord ++ tailWord_360485).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360485).length < 2 ^ (prefixWord ++ tailWord_360485).sum := by decide
  have hdescent : baseEnd_360485 < baseStart_360485 := by decide
  rcases family_descends (prefixWord ++ tailWord_360485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360534 : List Nat := [5, 2, 2, 1, 1, 1, 2, 2, 6]
def baseStart_360534 : Nat := 118140960795 + 360534 * 2 ^ 59
def prefixEnd_360534 : Nat := 4983230072969 + 3 ^ 40 * 360534 * 2
def baseEnd_360534 : Nat := 41139385397377253948209

theorem tailTrace_360534 : CollatzResearch.WordTrace tailWord_360534 prefixEnd_360534 41139385397377253948209 := by
  unfold tailWord_360534
  simp only [CollatzResearch.WordTrace]
  refine ⟨821859704740897946883041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8766503517236244766752437 821859704740897946883041)
  ·
    refine ⟨616394778555673460162281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 821859704740897946883041 616394778555673460162281)
    ·
      refine ⟨462296083916755095121711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 616394778555673460162281 462296083916755095121711)
      ·
        refine ⟨693444125875132642682567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462296083916755095121711 693444125875132642682567)
        ·
          refine ⟨1040166188812698964023851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 693444125875132642682567 1040166188812698964023851)
          ·
            refine ⟨1560249283219048446035777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1040166188812698964023851 1560249283219048446035777)
            ·
              refine ⟨1170186962414286334526833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1560249283219048446035777 1170186962414286334526833)
              ·
                refine ⟨877640221810714750895125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1170186962414286334526833 877640221810714750895125)
                ·
                  refine ⟨41139385397377253948209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 877640221810714750895125 41139385397377253948209)
                  ·
                    rfl

theorem cell22_360534_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_360534 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360534 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360534 prefixEnd_360534 := by exact prefixLift 360534
  have htrace : WordTrace (prefixWord ++ tailWord_360534) baseStart_360534 baseEnd_360534 := by
    simpa [prefixWord, tailWord_360534, baseEnd_360534] using wordTrace_append hprefix tailTrace_360534
  have hstable : (prefixWord ++ tailWord_360534).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360534).length < 2 ^ (prefixWord ++ tailWord_360534).sum := by decide
  have hdescent : baseEnd_360534 < baseStart_360534 := by decide
  rcases family_descends (prefixWord ++ tailWord_360534) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360635 : List Nat := [1, 1, 1, 1, 1, 2, 6, 3, 6]
def baseStart_360635 : Nat := 118140960795 + 360635 * 2 ^ 59
def prefixEnd_360635 : Nat := 4983230072969 + 3 ^ 40 * 360635 * 2
def baseEnd_360635 : Nat := 41150910185400388356439

theorem tailTrace_360635 : CollatzResearch.WordTrace tailWord_360635 prefixEnd_360635 41150910185400388356439 := by
  unfold tailWord_360635
  simp only [CollatzResearch.WordTrace]
  refine ⟨13153439048488461399555359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8768959365658974266370239 13153439048488461399555359)
  ·
    refine ⟨19730158572732692099333039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13153439048488461399555359 19730158572732692099333039)
    ·
      refine ⟨29595237859099038148999559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19730158572732692099333039 29595237859099038148999559)
      ·
        refine ⟨44392856788648557223499339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29595237859099038148999559 44392856788648557223499339)
        ·
          refine ⟨66589285182972835835249009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44392856788648557223499339 66589285182972835835249009)
          ·
            refine ⟨49941963887229626876436757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66589285182972835835249009 49941963887229626876436757)
            ·
              refine ⟨2341029557213888759832973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 49941963887229626876436757 2341029557213888759832973)
              ·
                refine ⟨877886083955208284937365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2341029557213888759832973 877886083955208284937365)
                ·
                  refine ⟨41150910185400388356439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 877886083955208284937365 41150910185400388356439)
                  ·
                    rfl

theorem cell22_360635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 6, 3, 6].length) (baseStart_360635 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360635 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360635 prefixEnd_360635 := by exact prefixLift 360635
  have htrace : WordTrace (prefixWord ++ tailWord_360635) baseStart_360635 baseEnd_360635 := by
    simpa [prefixWord, tailWord_360635, baseEnd_360635] using wordTrace_append hprefix tailTrace_360635
  have hstable : (prefixWord ++ tailWord_360635).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360635).length < 2 ^ (prefixWord ++ tailWord_360635).sum := by decide
  have hdescent : baseEnd_360635 < baseStart_360635 := by decide
  rcases family_descends (prefixWord ++ tailWord_360635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360682 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 4, 4]
def baseStart_360682 : Nat := 118140960795 + 360682 * 2 ^ 59
def prefixEnd_360682 : Nat := 4983230072969 + 3 ^ 40 * 360682 * 2
def baseEnd_360682 : Nat := 123468819616708709144173

theorem tailTrace_360682 : CollatzResearch.WordTrace tailWord_360682 prefixEnd_360682 123468819616708709144173 := by
  unfold tailWord_360682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3288788319829547106629075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8770102186212125617677533 3288788319829547106629075)
  ·
    refine ⟨4933182479744320659943613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3288788319829547106629075 4933182479744320659943613)
    ·
      refine ⟨1849943429904120247478855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4933182479744320659943613 1849943429904120247478855)
      ·
        refine ⟨2774915144856180371218283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1849943429904120247478855 2774915144856180371218283)
        ·
          refine ⟨4162372717284270556827425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2774915144856180371218283 4162372717284270556827425)
          ·
            refine ⟨3121779537963202917620569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4162372717284270556827425 3121779537963202917620569)
            ·
              refine ⟨2341334653472402188215427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3121779537963202917620569 2341334653472402188215427)
              ·
                refine ⟨3512001980208603282323141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341334653472402188215427 3512001980208603282323141)
                ·
                  refine ⟨658500371289113115435589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3512001980208603282323141 658500371289113115435589)
                  ·
                    refine ⟨123468819616708709144173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 658500371289113115435589 123468819616708709144173)
                    ·
                      rfl

theorem cell22_360682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 4].length) (baseStart_360682 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360682 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360682 prefixEnd_360682 := by exact prefixLift 360682
  have htrace : WordTrace (prefixWord ++ tailWord_360682) baseStart_360682 baseEnd_360682 := by
    simpa [prefixWord, tailWord_360682, baseEnd_360682] using wordTrace_append hprefix tailTrace_360682
  have hstable : (prefixWord ++ tailWord_360682).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360682).length < 2 ^ (prefixWord ++ tailWord_360682).sum := by decide
  have hdescent : baseEnd_360682 < baseStart_360682 := by decide
  rcases family_descends (prefixWord ++ tailWord_360682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360695 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 7]
def baseStart_360695 : Nat := 118140960795 + 360695 * 2 ^ 59
def prefixEnd_360695 : Nat := 4983230072969 + 3 ^ 40 * 360695 * 2
def baseEnd_360695 : Nat := 123473269782381008569133

theorem tailTrace_360695 : CollatzResearch.WordTrace tailWord_360695 prefixEnd_360695 123473269782381008569133 := by
  unfold tailWord_360695
  simp only [CollatzResearch.WordTrace]
  refine ⟨13155627428271091646739539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8770418285514061097826359 13155627428271091646739539)
  ·
    refine ⟨19733441142406637470109309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13155627428271091646739539 19733441142406637470109309)
    ·
      refine ⟨7400040428402489051290991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19733441142406637470109309 7400040428402489051290991)
      ·
        refine ⟨11100060642603733576936487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7400040428402489051290991 11100060642603733576936487)
        ·
          refine ⟨16650090963905600365404731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11100060642603733576936487 16650090963905600365404731)
          ·
            refine ⟨24975136445858400548107097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16650090963905600365404731 24975136445858400548107097)
            ·
              refine ⟨18731352334393800411080323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 24975136445858400548107097 18731352334393800411080323)
              ·
                refine ⟨28097028501590700616620485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 18731352334393800411080323 28097028501590700616620485)
                ·
                  refine ⟨5268192844048256365616341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28097028501590700616620485 5268192844048256365616341)
                  ·
                    refine ⟨123473269782381008569133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5268192844048256365616341 123473269782381008569133)
                    ·
                      rfl

theorem cell22_360695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 7].length) (baseStart_360695 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360695 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360695 prefixEnd_360695 := by exact prefixLift 360695
  have htrace : WordTrace (prefixWord ++ tailWord_360695) baseStart_360695 baseEnd_360695 := by
    simpa [prefixWord, tailWord_360695, baseEnd_360695] using wordTrace_append hprefix tailTrace_360695
  have hstable : (prefixWord ++ tailWord_360695).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360695).length < 2 ^ (prefixWord ++ tailWord_360695).sum := by decide
  have hdescent : baseEnd_360695 < baseStart_360695 := by decide
  rcases family_descends (prefixWord ++ tailWord_360695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360757 : List Nat := [1, 3, 3, 1, 2, 1, 2, 1, 1, 7]
def baseStart_360757 : Nat := 118140960795 + 360757 * 2 ^ 59
def prefixEnd_360757 : Nat := 4983230072969 + 3 ^ 40 * 360757 * 2
def baseEnd_360757 : Nat := 123494493649433513518943

theorem tailTrace_360757 : CollatzResearch.WordTrace tailWord_360757 prefixEnd_360757 123494493649433513518943 := by
  unfold tailWord_360757
  simp only [CollatzResearch.WordTrace]
  refine ⟨13157888754046476235496525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8771925836030984156997683 13157888754046476235496525)
  ·
    refine ⟨4934208282767428588311197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13157888754046476235496525 4934208282767428588311197)
    ·
      refine ⟨1850328106037785720616699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4934208282767428588311197 1850328106037785720616699)
      ·
        refine ⟨2775492159056678580925049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1850328106037785720616699 2775492159056678580925049)
        ·
          refine ⟨2081619119292508935693787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2775492159056678580925049 2081619119292508935693787)
          ·
            refine ⟨3122428678938763403540681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2081619119292508935693787 3122428678938763403540681)
            ·
              refine ⟨2341821509204072552655511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3122428678938763403540681 2341821509204072552655511)
              ·
                refine ⟨3512732263806108828983267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2341821509204072552655511 3512732263806108828983267)
                ·
                  refine ⟨5269098395709163243474901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3512732263806108828983267 5269098395709163243474901)
                  ·
                    refine ⟨123494493649433513518943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5269098395709163243474901 123494493649433513518943)
                    ·
                      rfl

theorem cell22_360757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 2, 1, 1, 7].length) (baseStart_360757 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360757 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360757 prefixEnd_360757 := by exact prefixLift 360757
  have htrace : WordTrace (prefixWord ++ tailWord_360757) baseStart_360757 baseEnd_360757 := by
    simpa [prefixWord, tailWord_360757, baseEnd_360757] using wordTrace_append hprefix tailTrace_360757
  have hstable : (prefixWord ++ tailWord_360757).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360757).length < 2 ^ (prefixWord ++ tailWord_360757).sum := by decide
  have hdescent : baseEnd_360757 < baseStart_360757 := by decide
  rcases family_descends (prefixWord ++ tailWord_360757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360817 : List Nat := [1, 2, 2, 2, 1, 2, 1, 4, 1, 6]
def baseStart_360817 : Nat := 118140960795 + 360817 * 2 ^ 59
def prefixEnd_360817 : Nat := 4983230072969 + 3 ^ 40 * 360817 * 2
def baseEnd_360817 : Nat := 123515032875613357018759

theorem tailTrace_360817 : CollatzResearch.WordTrace tailWord_360817 prefixEnd_360817 123515032875613357018759 := by
  unfold tailWord_360817
  simp only [CollatzResearch.WordTrace]
  refine ⟨13160077133829106482680705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8773384755886070988453803 13160077133829106482680705)
  ·
    refine ⟨9870057850371829862010529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13160077133829106482680705 9870057850371829862010529)
    ·
      refine ⟨7402543387778872396507897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9870057850371829862010529 7402543387778872396507897)
      ·
        refine ⟨5551907540834154297380923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7402543387778872396507897 5551907540834154297380923)
        ·
          refine ⟨8327861311251231446071385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5551907540834154297380923 8327861311251231446071385)
          ·
            refine ⟨6245895983438423584553539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8327861311251231446071385 6245895983438423584553539)
            ·
              refine ⟨9368843975157635376830309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6245895983438423584553539 9368843975157635376830309)
              ·
                refine ⟨1756658245342056633155683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9368843975157635376830309 1756658245342056633155683)
                ·
                  refine ⟨2634987368013084949733525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1756658245342056633155683 2634987368013084949733525)
                  ·
                    refine ⟨123515032875613357018759, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2634987368013084949733525 123515032875613357018759)
                    ·
                      rfl

theorem cell22_360817_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 1, 4, 1, 6].length) (baseStart_360817 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360817 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360817 prefixEnd_360817 := by exact prefixLift 360817
  have htrace : WordTrace (prefixWord ++ tailWord_360817) baseStart_360817 baseEnd_360817 := by
    simpa [prefixWord, tailWord_360817, baseEnd_360817] using wordTrace_append hprefix tailTrace_360817
  have hstable : (prefixWord ++ tailWord_360817).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360817).length < 2 ^ (prefixWord ++ tailWord_360817).sum := by decide
  have hdescent : baseEnd_360817 < baseStart_360817 := by decide
  rcases family_descends (prefixWord ++ tailWord_360817) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360881 : List Nat := [1, 2, 2, 4, 1, 2, 2, 2, 3, 3]
def baseStart_360881 : Nat := 118140960795 + 360881 * 2 ^ 59
def prefixEnd_360881 : Nat := 4983230072969 + 3 ^ 40 * 360881 * 2
def baseEnd_360881 : Nat := 123536941383538523418563

theorem tailTrace_360881 : CollatzResearch.WordTrace tailWord_360881 prefixEnd_360881 123536941383538523418563 := by
  unfold tailWord_360881
  simp only [CollatzResearch.WordTrace]
  refine ⟨13162411405597245413010497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8774940937064830275340331 13162411405597245413010497)
  ·
    refine ⟨9871808554197934059757873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13162411405597245413010497 9871808554197934059757873)
    ·
      refine ⟨7403856415648450544818405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9871808554197934059757873 7403856415648450544818405)
      ·
        refine ⟨1388223077934084477153451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7403856415648450544818405 1388223077934084477153451)
        ·
          refine ⟨2082334616901126715730177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1388223077934084477153451 2082334616901126715730177)
          ·
            refine ⟨1561750962675845036797633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082334616901126715730177 1561750962675845036797633)
            ·
              refine ⟨1171313222006883777598225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1561750962675845036797633 1171313222006883777598225)
              ·
                refine ⟨878484916505162833198669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1171313222006883777598225 878484916505162833198669)
                ·
                  refine ⟨329431843689436062449501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 878484916505162833198669 329431843689436062449501)
                  ·
                    refine ⟨123536941383538523418563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329431843689436062449501 123536941383538523418563)
                    ·
                      rfl

theorem cell22_360881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 2, 2, 2, 3, 3].length) (baseStart_360881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360881 prefixEnd_360881 := by exact prefixLift 360881
  have htrace : WordTrace (prefixWord ++ tailWord_360881) baseStart_360881 baseEnd_360881 := by
    simpa [prefixWord, tailWord_360881, baseEnd_360881] using wordTrace_append hprefix tailTrace_360881
  have hstable : (prefixWord ++ tailWord_360881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360881).length < 2 ^ (prefixWord ++ tailWord_360881).sum := by decide
  have hdescent : baseEnd_360881 < baseStart_360881 := by decide
  rcases family_descends (prefixWord ++ tailWord_360881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360894 : List Nat := [4, 2, 1, 1, 1, 1, 3, 2, 7]
def baseStart_360894 : Nat := 118140960795 + 360894 * 2 ^ 59
def prefixEnd_360894 : Nat := 4983230072969 + 3 ^ 40 * 360894 * 2
def baseEnd_360894 : Nat := 41180463849736940947841

theorem tailTrace_360894 : CollatzResearch.WordTrace tailWord_360894 prefixEnd_360894 41180463849736940947841 := by
  unfold tailWord_360894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1645360694318768579154217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8775257036366765755489157 1645360694318768579154217)
  ·
    refine ⟨1234020520739076434365663, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1645360694318768579154217 1234020520739076434365663)
    ·
      refine ⟨1851030781108614651548495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234020520739076434365663 1851030781108614651548495)
      ·
        refine ⟨2776546171662921977322743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851030781108614651548495 2776546171662921977322743)
        ·
          refine ⟨4164819257494382965984115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2776546171662921977322743 4164819257494382965984115)
          ·
            refine ⟨6247228886241574448976173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4164819257494382965984115 6247228886241574448976173)
            ·
              refine ⟨2342710832340590418366065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6247228886241574448976173 2342710832340590418366065)
              ·
                refine ⟨1757033124255442813774549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2342710832340590418366065 1757033124255442813774549)
                ·
                  refine ⟨41180463849736940947841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1757033124255442813774549 41180463849736940947841)
                  ·
                    rfl

theorem cell22_360894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 2, 7].length) (baseStart_360894 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360894 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360894 prefixEnd_360894 := by exact prefixLift 360894
  have htrace : WordTrace (prefixWord ++ tailWord_360894) baseStart_360894 baseEnd_360894 := by
    simpa [prefixWord, tailWord_360894, baseEnd_360894] using wordTrace_append hprefix tailTrace_360894
  have hstable : (prefixWord ++ tailWord_360894).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360894).length < 2 ^ (prefixWord ++ tailWord_360894).sum := by decide
  have hdescent : baseEnd_360894 < baseStart_360894 := by decide
  rcases family_descends (prefixWord ++ tailWord_360894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360956 : List Nat := [2, 2, 2, 1, 2, 1, 1, 7, 4]
def baseStart_360956 : Nat := 118140960795 + 360956 * 2 ^ 59
def prefixEnd_360956 : Nat := 4983230072969 + 3 ^ 40 * 360956 * 2
def baseEnd_360956 : Nat := 41187538472087775931111

theorem tailTrace_360956 : CollatzResearch.WordTrace tailWord_360956 prefixEnd_360956 41187538472087775931111 := by
  unfold tailWord_360956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6582573440162766610995361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8776764586883688814660481 6582573440162766610995361)
  ·
    refine ⟨4936930080122074958246521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6582573440162766610995361 4936930080122074958246521)
    ·
      refine ⟨3702697560091556218684891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4936930080122074958246521 3702697560091556218684891)
      ·
        refine ⟨5554046340137334328027337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3702697560091556218684891 5554046340137334328027337)
        ·
          refine ⟨4165534755103000746020503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5554046340137334328027337 4165534755103000746020503)
          ·
            refine ⟨6248302132654501119030755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4165534755103000746020503 6248302132654501119030755)
            ·
              refine ⟨9372453198981751678546133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6248302132654501119030755 9372453198981751678546133)
              ·
                refine ⟨219666871851134804965925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9372453198981751678546133 219666871851134804965925)
                ·
                  refine ⟨41187538472087775931111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 219666871851134804965925 41187538472087775931111)
                  ·
                    rfl

theorem cell22_360956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 1, 7, 4].length) (baseStart_360956 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360956 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360956 prefixEnd_360956 := by exact prefixLift 360956
  have htrace : WordTrace (prefixWord ++ tailWord_360956) baseStart_360956 baseEnd_360956 := by
    simpa [prefixWord, tailWord_360956, baseEnd_360956] using wordTrace_append hprefix tailTrace_360956
  have hstable : (prefixWord ++ tailWord_360956).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360956).length < 2 ^ (prefixWord ++ tailWord_360956).sum := by decide
  have hdescent : baseEnd_360956 < baseStart_360956 := by decide
  rcases family_descends (prefixWord ++ tailWord_360956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360966 : List Nat := [6, 2, 1, 1, 1, 1, 4, 2, 1, 3]
def baseStart_360966 : Nat := 118140960795 + 360966 * 2 ^ 59
def prefixEnd_360966 : Nat := 4983230072969 + 3 ^ 40 * 360966 * 2
def baseEnd_360966 : Nat := 123566038620626635043303

theorem tailTrace_360966 : CollatzResearch.WordTrace tailWord_360966 prefixEnd_360966 123566038620626635043303 := by
  unfold tailWord_360966
  simp only [CollatzResearch.WordTrace]
  refine ⟨411422237821540779057961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8777007740192869953236501 411422237821540779057961)
  ·
    refine ⟨308566678366155584293471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 411422237821540779057961 308566678366155584293471)
    ·
      refine ⟨462850017549233376440207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 308566678366155584293471 462850017549233376440207)
      ·
        refine ⟨694275026323850064660311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 462850017549233376440207 694275026323850064660311)
        ·
          refine ⟨1041412539485775096990467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 694275026323850064660311 1041412539485775096990467)
          ·
            refine ⟨1562118809228662645485701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1041412539485775096990467 1562118809228662645485701)
            ·
              refine ⟨292897276730374246028569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1562118809228662645485701 292897276730374246028569)
              ·
                refine ⟨219672957547780684521427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 292897276730374246028569 219672957547780684521427)
                ·
                  refine ⟨329509436321671026782141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219672957547780684521427 329509436321671026782141)
                  ·
                    refine ⟨123566038620626635043303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329509436321671026782141 123566038620626635043303)
                    ·
                      rfl

theorem cell22_360966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_360966 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360966 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360966 prefixEnd_360966 := by exact prefixLift 360966
  have htrace : WordTrace (prefixWord ++ tailWord_360966) baseStart_360966 baseEnd_360966 := by
    simpa [prefixWord, tailWord_360966, baseEnd_360966] using wordTrace_append hprefix tailTrace_360966
  have hstable : (prefixWord ++ tailWord_360966).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360966).length < 2 ^ (prefixWord ++ tailWord_360966).sum := by decide
  have hdescent : baseEnd_360966 < baseStart_360966 := by decide
  rcases family_descends (prefixWord ++ tailWord_360966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360969 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 4, 4]
def baseStart_360969 : Nat := 118140960795 + 360969 * 2 ^ 59
def prefixEnd_360969 : Nat := 4983230072969 + 3 ^ 40 * 360969 * 2
def baseEnd_360969 : Nat := 123567065581935627218293

theorem tailTrace_360969 : CollatzResearch.WordTrace tailWord_360969 prefixEnd_360969 123567065581935627218293 := by
  unfold tailWord_360969
  simp only [CollatzResearch.WordTrace]
  refine ⟨13165621029278436442213961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8777080686185624294809307 13165621029278436442213961)
  ·
    refine ⟨9874215771958827331660471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13165621029278436442213961 9874215771958827331660471)
    ·
      refine ⟨14811323657938240997490707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9874215771958827331660471 14811323657938240997490707)
      ·
        refine ⟨22216985486907361496236061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14811323657938240997490707 22216985486907361496236061)
        ·
          refine ⟨8331369557590260561088523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22216985486907361496236061 8331369557590260561088523)
          ·
            refine ⟨12497054336385390841632785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8331369557590260561088523 12497054336385390841632785)
            ·
              refine ⟨9372790752289043131224589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12497054336385390841632785 9372790752289043131224589)
              ·
                refine ⟨3514796532108391174209221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9372790752289043131224589 3514796532108391174209221)
                ·
                  refine ⟨659024349770323345164229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3514796532108391174209221 659024349770323345164229)
                  ·
                    refine ⟨123567065581935627218293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659024349770323345164229 123567065581935627218293)
                    ·
                      rfl

theorem cell22_360969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 4].length) (baseStart_360969 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360969 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360969 prefixEnd_360969 := by exact prefixLift 360969
  have htrace : WordTrace (prefixWord ++ tailWord_360969) baseStart_360969 baseEnd_360969 := by
    simpa [prefixWord, tailWord_360969, baseEnd_360969] using wordTrace_append hprefix tailTrace_360969
  have hstable : (prefixWord ++ tailWord_360969).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360969).length < 2 ^ (prefixWord ++ tailWord_360969).sum := by decide
  have hdescent : baseEnd_360969 < baseStart_360969 := by decide
  rcases family_descends (prefixWord ++ tailWord_360969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_360988 : List Nat := [2, 2, 3, 1, 2, 2, 2, 3, 2, 3]
def baseStart_360988 : Nat := 118140960795 + 360988 * 2 ^ 59
def prefixEnd_360988 : Nat := 4983230072969 + 3 ^ 40 * 360988 * 2
def baseEnd_360988 : Nat := 123573569670225910993235

theorem tailTrace_360988 : CollatzResearch.WordTrace tailWord_360988 prefixEnd_360988 123573569670225910993235 := by
  unfold tailWord_360988
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583157008104801343577809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8777542677473068458103745 6583157008104801343577809)
  ·
    refine ⟨4937367756078601007683357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6583157008104801343577809 4937367756078601007683357)
    ·
      refine ⟨1851512908529475377881259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4937367756078601007683357 1851512908529475377881259)
      ·
        refine ⟨2777269362794213066821889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1851512908529475377881259 2777269362794213066821889)
        ·
          refine ⟨2082952022095659800116417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2777269362794213066821889 2082952022095659800116417)
          ·
            refine ⟨1562214016571744850087313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2082952022095659800116417 1562214016571744850087313)
            ·
              refine ⟨1171660512428808637565485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1562214016571744850087313 1171660512428808637565485)
              ·
                refine ⟨439372692160803239087057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1171660512428808637565485 439372692160803239087057)
                ·
                  refine ⟨329529519120602429315293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 439372692160803239087057 329529519120602429315293)
                  ·
                    refine ⟨123573569670225910993235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329529519120602429315293 123573569670225910993235)
                    ·
                      rfl

theorem cell22_360988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 2, 3, 2, 3].length) (baseStart_360988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_360988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_360988 prefixEnd_360988 := by exact prefixLift 360988
  have htrace : WordTrace (prefixWord ++ tailWord_360988) baseStart_360988 baseEnd_360988 := by
    simpa [prefixWord, tailWord_360988, baseEnd_360988] using wordTrace_append hprefix tailTrace_360988
  have hstable : (prefixWord ++ tailWord_360988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_360988).length < 2 ^ (prefixWord ++ tailWord_360988).sum := by decide
  have hdescent : baseEnd_360988 < baseStart_360988 := by decide
  rcases family_descends (prefixWord ++ tailWord_360988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361016 : List Nat := [2, 1, 2, 1, 4, 1, 1, 2, 5, 3]
def baseStart_361016 : Nat := 118140960795 + 361016 * 2 ^ 59
def prefixEnd_361016 : Nat := 4983230072969 + 3 ^ 40 * 361016 * 2
def baseEnd_361016 : Nat := 123583154642443171293149

theorem tailTrace_361016 : CollatzResearch.WordTrace tailWord_361016 prefixEnd_361016 123583154642443171293149 := by
  unfold tailWord_361016
  simp only [CollatzResearch.WordTrace]
  refine ⟨6583667630054081734587451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8778223506738775646116601 6583667630054081734587451)
  ·
    refine ⟨9875501445081122601881177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6583667630054081734587451 9875501445081122601881177)
    ·
      refine ⟨7406626083810841951410883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9875501445081122601881177 7406626083810841951410883)
      ·
        refine ⟨11109939125716262927116325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7406626083810841951410883 11109939125716262927116325)
        ·
          refine ⟨2083113586071799298834311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11109939125716262927116325 2083113586071799298834311)
          ·
            refine ⟨3124670379107698948251467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2083113586071799298834311 3124670379107698948251467)
            ·
              refine ⟨4687005568661548422377201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3124670379107698948251467 4687005568661548422377201)
              ·
                refine ⟨3515254176496161316782901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4687005568661548422377201 3515254176496161316782901)
                ·
                  refine ⟨329555079046515123448397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3515254176496161316782901 329555079046515123448397)
                  ·
                    refine ⟨123583154642443171293149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329555079046515123448397 123583154642443171293149)
                    ·
                      rfl

theorem cell22_361016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 1, 1, 2, 5, 3].length) (baseStart_361016 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361016 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361016 prefixEnd_361016 := by exact prefixLift 361016
  have htrace : WordTrace (prefixWord ++ tailWord_361016) baseStart_361016 baseEnd_361016 := by
    simpa [prefixWord, tailWord_361016, baseEnd_361016] using wordTrace_append hprefix tailTrace_361016
  have hstable : (prefixWord ++ tailWord_361016).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361016).length < 2 ^ (prefixWord ++ tailWord_361016).sum := by decide
  have hdescent : baseEnd_361016 < baseStart_361016 := by decide
  rcases family_descends (prefixWord ++ tailWord_361016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361091 : List Nat := [1, 1, 1, 3, 3, 1, 5, 1, 6]
def baseStart_361091 : Nat := 118140960795 + 361091 * 2 ^ 59
def prefixEnd_361091 : Nat := 4983230072969 + 3 ^ 40 * 361091 * 2
def baseEnd_361091 : Nat := 41202942891722658555973

theorem tailTrace_361091 : CollatzResearch.WordTrace tailWord_361091 prefixEnd_361091 41202942891722658555973 := by
  unfold tailWord_361091
  simp only [CollatzResearch.WordTrace]
  refine ⟨13170070734836451278155127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8780047156557634185436751 13170070734836451278155127)
  ·
    refine ⟨19755106102254676917232691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13170070734836451278155127 19755106102254676917232691)
    ·
      refine ⟨29632659153382015375849037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19755106102254676917232691 29632659153382015375849037)
      ·
        refine ⟨11112247182518255765943389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29632659153382015375849037 11112247182518255765943389)
        ·
          refine ⟨4167092693444345912228771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11112247182518255765943389 4167092693444345912228771)
          ·
            refine ⟨6250639040166518868343157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4167092693444345912228771 6250639040166518868343157)
            ·
              refine ⟨585997410015611143907171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6250639040166518868343157 585997410015611143907171)
              ·
                refine ⟨878996115023416715860757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 585997410015611143907171 878996115023416715860757)
                ·
                  refine ⟨41202942891722658555973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 878996115023416715860757 41202942891722658555973)
                  ·
                    rfl

theorem cell22_361091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 5, 1, 6].length) (baseStart_361091 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361091 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361091 prefixEnd_361091 := by exact prefixLift 361091
  have htrace : WordTrace (prefixWord ++ tailWord_361091) baseStart_361091 baseEnd_361091 := by
    simpa [prefixWord, tailWord_361091, baseEnd_361091] using wordTrace_append hprefix tailTrace_361091
  have hstable : (prefixWord ++ tailWord_361091).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361091).length < 2 ^ (prefixWord ++ tailWord_361091).sum := by decide
  have hdescent : baseEnd_361091 < baseStart_361091 := by decide
  rcases family_descends (prefixWord ++ tailWord_361091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361170 : List Nat := [3, 2, 2, 2, 3, 1, 3, 6]
def baseStart_361170 : Nat := 118140960795 + 361170 * 2 ^ 59
def prefixEnd_361170 : Nat := 4983230072969 + 3 ^ 40 * 361170 * 2
def baseEnd_361170 : Nat := 13737319109959789215853

theorem tailTrace_361170 : CollatzResearch.WordTrace tailWord_361170 prefixEnd_361170 13737319109959789215853 := by
  unfold tailWord_361170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293238025387561942570241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8781968067700165180187309 3293238025387561942570241)
  ·
    refine ⟨2469928519040671456927681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293238025387561942570241 2469928519040671456927681)
    ·
      refine ⟨1852446389280503592695761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2469928519040671456927681 1852446389280503592695761)
      ·
        refine ⟨1389334791960377694521821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1852446389280503592695761 1389334791960377694521821)
        ·
          refine ⟨521000546985141635445683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1389334791960377694521821 521000546985141635445683)
          ·
            refine ⟨781500820477712453168525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521000546985141635445683 781500820477712453168525)
            ·
              refine ⟨293062807679142169938197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 781500820477712453168525 293062807679142169938197)
              ·
                refine ⟨13737319109959789215853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293062807679142169938197 13737319109959789215853)
                ·
                  rfl

theorem cell22_361170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_361170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361170 prefixEnd_361170 := by exact prefixLift 361170
  have htrace : WordTrace (prefixWord ++ tailWord_361170) baseStart_361170 baseEnd_361170 := by
    simpa [prefixWord, tailWord_361170, baseEnd_361170] using wordTrace_append hprefix tailTrace_361170
  have hstable : (prefixWord ++ tailWord_361170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361170).length < 2 ^ (prefixWord ++ tailWord_361170).sum := by decide
  have hdescent : baseEnd_361170 < baseStart_361170 := by decide
  rcases family_descends (prefixWord ++ tailWord_361170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361172 : List Nat := [2, 4, 1, 3, 2, 2, 1, 1, 2, 4]
def baseStart_361172 : Nat := 118140960795 + 361172 * 2 ^ 59
def prefixEnd_361172 : Nat := 4983230072969 + 3 ^ 40 * 361172 * 2
def baseEnd_361172 : Nat := 123636556630510764392671

theorem tailTrace_361172 : CollatzResearch.WordTrace tailWord_361172 prefixEnd_361172 123636556630510764392671 := by
  unfold tailWord_361172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6586512523771501055926885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8782016698362001407902513 6586512523771501055926885)
  ·
    refine ⟨1234971098207156447986291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6586512523771501055926885 1234971098207156447986291)
    ·
      refine ⟨1852456647310734671979437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1234971098207156447986291 1852456647310734671979437)
      ·
        refine ⟨694671242741525501992289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1852456647310734671979437 694671242741525501992289)
        ·
          refine ⟨521003432056144126494217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 694671242741525501992289 521003432056144126494217)
          ·
            refine ⟨390752574042108094870663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 521003432056144126494217 390752574042108094870663)
            ·
              refine ⟨586128861063162142305995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 390752574042108094870663 586128861063162142305995)
              ·
                refine ⟨879193291594743213458993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586128861063162142305995 879193291594743213458993)
                ·
                  refine ⟨659394968696057410094245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879193291594743213458993 659394968696057410094245)
                  ·
                    refine ⟨123636556630510764392671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659394968696057410094245 123636556630510764392671)
                    ·
                      rfl

theorem cell22_361172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 2, 2, 1, 1, 2, 4].length) (baseStart_361172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361172 prefixEnd_361172 := by exact prefixLift 361172
  have htrace : WordTrace (prefixWord ++ tailWord_361172) baseStart_361172 baseEnd_361172 := by
    simpa [prefixWord, tailWord_361172, baseEnd_361172] using wordTrace_append hprefix tailTrace_361172
  have hstable : (prefixWord ++ tailWord_361172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361172).length < 2 ^ (prefixWord ++ tailWord_361172).sum := by decide
  have hdescent : baseEnd_361172 < baseStart_361172 := by decide
  rcases family_descends (prefixWord ++ tailWord_361172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361198 : List Nat := [4, 1, 2, 1, 1, 4, 1, 1, 7]
def baseStart_361198 : Nat := 118140960795 + 361198 * 2 ^ 59
def prefixEnd_361198 : Nat := 4983230072969 + 3 ^ 40 * 361198 * 2
def baseEnd_361198 : Nat := 41215152320618454414197

theorem tailTrace_361198 : CollatzResearch.WordTrace tailWord_361198 prefixEnd_361198 41215152320618454414197 := by
  unfold tailWord_361198
  simp only [CollatzResearch.WordTrace]
  refine ⟨1646746668181101069037531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8782648896965872368200165 1646746668181101069037531)
  ·
    refine ⟨2470120002271651603556297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1646746668181101069037531 2470120002271651603556297)
    ·
      refine ⟨1852590001703738702667223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2470120002271651603556297 1852590001703738702667223)
      ·
        refine ⟨2778885002555608054000835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1852590001703738702667223 2778885002555608054000835)
        ·
          refine ⟨4168327503833412081001253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2778885002555608054000835 4168327503833412081001253)
          ·
            refine ⟨781561406968764765187735, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4168327503833412081001253 781561406968764765187735)
            ·
              refine ⟨1172342110453147147781603, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 781561406968764765187735 1172342110453147147781603)
              ·
                refine ⟨1758513165679720721672405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1172342110453147147781603 1758513165679720721672405)
                ·
                  refine ⟨41215152320618454414197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1758513165679720721672405 41215152320618454414197)
                  ·
                    rfl

theorem cell22_361198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 1, 7].length) (baseStart_361198 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361198 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361198 prefixEnd_361198 := by exact prefixLift 361198
  have htrace : WordTrace (prefixWord ++ tailWord_361198) baseStart_361198 baseEnd_361198 := by
    simpa [prefixWord, tailWord_361198, baseEnd_361198] using wordTrace_append hprefix tailTrace_361198
  have hstable : (prefixWord ++ tailWord_361198).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361198).length < 2 ^ (prefixWord ++ tailWord_361198).sum := by decide
  have hdescent : baseEnd_361198 < baseStart_361198 := by decide
  rcases family_descends (prefixWord ++ tailWord_361198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361202 : List Nat := [3, 2, 1, 3, 1, 2, 2, 4, 1, 3]
def baseStart_361202 : Nat := 118140960795 + 361202 * 2 ^ 59
def prefixEnd_361202 : Nat := 4983230072969 + 3 ^ 40 * 361202 * 2
def baseEnd_361202 : Nat := 123646826243600686142579

theorem tailTrace_361202 : CollatzResearch.WordTrace tailWord_361202 prefixEnd_361202 123646826243600686142579 := by
  unfold tailWord_361202
  simp only [CollatzResearch.WordTrace]
  refine ⟨3293529809358579308861465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8782746158289544823630573 3293529809358579308861465)
  ·
    refine ⟨2470147357018934481646099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3293529809358579308861465 2470147357018934481646099)
    ·
      refine ⟨3705221035528401722469149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2470147357018934481646099 3705221035528401722469149)
      ·
        refine ⟨1389457888323150645925931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3705221035528401722469149 1389457888323150645925931)
        ·
          refine ⟨2084186832484725968888897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1389457888323150645925931 2084186832484725968888897)
          ·
            refine ⟨1563140124363544476666673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2084186832484725968888897 1563140124363544476666673)
            ·
              refine ⟨1172355093272658357500005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1563140124363544476666673 1172355093272658357500005)
              ·
                refine ⟨219816579988623442031251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1172355093272658357500005 219816579988623442031251)
                ·
                  refine ⟨329724869982935163046877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219816579988623442031251 329724869982935163046877)
                  ·
                    refine ⟨123646826243600686142579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329724869982935163046877 123646826243600686142579)
                    ·
                      rfl

theorem cell22_361202_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 2, 2, 4, 1, 3].length) (baseStart_361202 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361202 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361202 prefixEnd_361202 := by exact prefixLift 361202
  have htrace : WordTrace (prefixWord ++ tailWord_361202) baseStart_361202 baseEnd_361202 := by
    simpa [prefixWord, tailWord_361202, baseEnd_361202] using wordTrace_append hprefix tailTrace_361202
  have hstable : (prefixWord ++ tailWord_361202).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361202).length < 2 ^ (prefixWord ++ tailWord_361202).sum := by decide
  have hdescent : baseEnd_361202 < baseStart_361202 := by decide
  rcases family_descends (prefixWord ++ tailWord_361202) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361348 : List Nat := [2, 3, 2, 1, 1, 1, 1, 1, 3, 7]
def baseStart_361348 : Nat := 118140960795 + 361348 * 2 ^ 59
def prefixEnd_361348 : Nat := 4983230072969 + 3 ^ 40 * 361348 * 2
def baseEnd_361348 : Nat := 123696805027304971992131

theorem tailTrace_361348 : CollatzResearch.WordTrace tailWord_361348 prefixEnd_361348 123696805027304971992131 := by
  unfold tailWord_361348
  simp only [CollatzResearch.WordTrace]
  refine ⟨6589722147452692085130349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8786296196603589446840465 6589722147452692085130349)
  ·
    refine ⟨2471145805294759531923881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6589722147452692085130349 2471145805294759531923881)
    ·
      refine ⟨1853359353971069648942911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2471145805294759531923881 1853359353971069648942911)
      ·
        refine ⟨2780039030956604473414367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1853359353971069648942911 2780039030956604473414367)
        ·
          refine ⟨4170058546434906710121551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2780039030956604473414367 4170058546434906710121551)
          ·
            refine ⟨6255087819652360065182327, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4170058546434906710121551 6255087819652360065182327)
            ·
              refine ⟨9382631729478540097773491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6255087819652360065182327 9382631729478540097773491)
              ·
                refine ⟨14073947594217810146660237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9382631729478540097773491 14073947594217810146660237)
                ·
                  refine ⟨5277730347831678804997589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14073947594217810146660237 5277730347831678804997589)
                  ·
                    refine ⟨123696805027304971992131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5277730347831678804997589 123696805027304971992131)
                    ·
                      rfl

theorem cell22_361348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 1, 1, 1, 1, 3, 7].length) (baseStart_361348 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361348 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361348 prefixEnd_361348 := by exact prefixLift 361348
  have htrace : WordTrace (prefixWord ++ tailWord_361348) baseStart_361348 baseEnd_361348 := by
    simpa [prefixWord, tailWord_361348, baseEnd_361348] using wordTrace_append hprefix tailTrace_361348
  have hstable : (prefixWord ++ tailWord_361348).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361348).length < 2 ^ (prefixWord ++ tailWord_361348).sum := by decide
  have hdescent : baseEnd_361348 < baseStart_361348 := by decide
  rcases family_descends (prefixWord ++ tailWord_361348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361354 : List Nat := [3, 1, 2, 4, 1, 1, 1, 5, 1, 3]
def baseStart_361354 : Nat := 118140960795 + 361354 * 2 ^ 59
def prefixEnd_361354 : Nat := 4983230072969 + 3 ^ 40 * 361354 * 2
def baseEnd_361354 : Nat := 123698858949922956342113

theorem tailTrace_361354 : CollatzResearch.WordTrace tailWord_361354 prefixEnd_361354 123698858949922956342113 := by
  unfold tailWord_361354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3294915783220911798744779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8786442088589098129986077 3294915783220911798744779)
  ·
    refine ⟨4942373674831367698117169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3294915783220911798744779 4942373674831367698117169)
    ·
      refine ⟨3706780256123525773587877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4942373674831367698117169 3706780256123525773587877)
      ·
        refine ⟨695021298023161082547727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3706780256123525773587877 695021298023161082547727)
        ·
          refine ⟨1042531947034741623821591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 695021298023161082547727 1042531947034741623821591)
          ·
            refine ⟨1563797920552112435732387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1042531947034741623821591 1563797920552112435732387)
            ·
              refine ⟨2345696880828168653598581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1563797920552112435732387 2345696880828168653598581)
              ·
                refine ⟨219909082577640811274867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2345696880828168653598581 219909082577640811274867)
                ·
                  refine ⟨329863623866461216912301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 219909082577640811274867 329863623866461216912301)
                  ·
                    refine ⟨123698858949922956342113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 329863623866461216912301 123698858949922956342113)
                    ·
                      rfl

theorem cell22_361354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 4, 1, 1, 1, 5, 1, 3].length) (baseStart_361354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361354 prefixEnd_361354 := by exact prefixLift 361354
  have htrace : WordTrace (prefixWord ++ tailWord_361354) baseStart_361354 baseEnd_361354 := by
    simpa [prefixWord, tailWord_361354, baseEnd_361354] using wordTrace_append hprefix tailTrace_361354
  have hstable : (prefixWord ++ tailWord_361354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361354).length < 2 ^ (prefixWord ++ tailWord_361354).sum := by decide
  have hdescent : baseEnd_361354 < baseStart_361354 := by decide
  rcases family_descends (prefixWord ++ tailWord_361354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361363 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 5, 4]
def baseStart_361363 : Nat := 118140960795 + 361363 * 2 ^ 59
def prefixEnd_361363 : Nat := 4983230072969 + 3 ^ 40 * 361363 * 2
def baseEnd_361363 : Nat := 123701939833849932867085

theorem tailTrace_361363 : CollatzResearch.WordTrace tailWord_361363 prefixEnd_361363 123701939833849932867085 := by
  unfold tailWord_361363
  simp only [CollatzResearch.WordTrace]
  refine ⟨13179991389851041732056743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8786660926567361154704495 13179991389851041732056743)
  ·
    refine ⟨19769987084776562598085115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13179991389851041732056743 19769987084776562598085115)
    ·
      refine ⟨29654980627164843897127673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19769987084776562598085115 29654980627164843897127673)
      ·
        refine ⟨22241235470373632922845755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29654980627164843897127673 22241235470373632922845755)
        ·
          refine ⟨33361853205560449384268633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22241235470373632922845755 33361853205560449384268633)
          ·
            refine ⟨25021389904170337038201475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33361853205560449384268633 25021389904170337038201475)
            ·
              refine ⟨37532084856255505557302213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25021389904170337038201475 37532084856255505557302213)
              ·
                refine ⟨7037265910547907291994165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 37532084856255505557302213 7037265910547907291994165)
                ·
                  refine ⟨659743679113866308624453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 7037265910547907291994165 659743679113866308624453)
                  ·
                    refine ⟨123701939833849932867085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659743679113866308624453 123701939833849932867085)
                    ·
                      rfl

theorem cell22_361363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 4].length) (baseStart_361363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361363 prefixEnd_361363 := by exact prefixLift 361363
  have htrace : WordTrace (prefixWord ++ tailWord_361363) baseStart_361363 baseEnd_361363 := by
    simpa [prefixWord, tailWord_361363, baseEnd_361363] using wordTrace_append hprefix tailTrace_361363
  have hstable : (prefixWord ++ tailWord_361363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361363).length < 2 ^ (prefixWord ++ tailWord_361363).sum := by decide
  have hdescent : baseEnd_361363 < baseStart_361363 := by decide
  rcases family_descends (prefixWord ++ tailWord_361363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361397 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 1, 4]
def baseStart_361397 : Nat := 118140960795 + 361397 * 2 ^ 59
def prefixEnd_361397 : Nat := 4983230072969 + 3 ^ 40 * 361397 * 2
def baseEnd_361397 : Nat := 123713578728685177516981

theorem tailTrace_361397 : CollatzResearch.WordTrace tailWord_361397 prefixEnd_361397 123713578728685177516981 := by
  unfold tailWord_361397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13181231471727865538794445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8787487647818577025862963 13181231471727865538794445)
  ·
    refine ⟨4942961801897949577047917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13181231471727865538794445 4942961801897949577047917)
    ·
      refine ⟨1853610675711731091392969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4942961801897949577047917 1853610675711731091392969)
      ·
        refine ⟨1390208006783798318544727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1853610675711731091392969 1390208006783798318544727)
        ·
          refine ⟨2085312010175697477817091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1390208006783798318544727 2085312010175697477817091)
          ·
            refine ⟨3127968015263546216725637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2085312010175697477817091 3127968015263546216725637)
            ·
              refine ⟨586494002861914915636057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3127968015263546216725637 586494002861914915636057)
              ·
                refine ⟨439870502146436186727043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 586494002861914915636057 439870502146436186727043)
                ·
                  refine ⟨659805753219654280090565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 439870502146436186727043 659805753219654280090565)
                  ·
                    refine ⟨123713578728685177516981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659805753219654280090565 123713578728685177516981)
                    ·
                      rfl

theorem cell22_361397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 4].length) (baseStart_361397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361397 prefixEnd_361397 := by exact prefixLift 361397
  have htrace : WordTrace (prefixWord ++ tailWord_361397) baseStart_361397 baseEnd_361397 := by
    simpa [prefixWord, tailWord_361397, baseEnd_361397] using wordTrace_append hprefix tailTrace_361397
  have hstable : (prefixWord ++ tailWord_361397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361397).length < 2 ^ (prefixWord ++ tailWord_361397).sum := by decide
  have hdescent : baseEnd_361397 < baseStart_361397 := by decide
  rcases family_descends (prefixWord ++ tailWord_361397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361423 : List Nat := [1, 1, 2, 1, 1, 6, 10]
def baseStart_361423 : Nat := 118140960795 + 361423 * 2 ^ 59
def prefixEnd_361423 : Nat := 4983230072969 + 3 ^ 40 * 361423 * 2
def baseEnd_361423 : Nat := 4582314039260362087663

theorem tailTrace_361423 : CollatzResearch.WordTrace tailWord_361423 prefixEnd_361423 4582314039260362087663 := by
  unfold tailWord_361423
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182179769633671979240923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8788119846422447986160615 13182179769633671979240923)
  ·
    refine ⟨19773269654450507968861385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13182179769633671979240923 19773269654450507968861385)
    ·
      refine ⟨14829952240837880976646039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19773269654450507968861385 14829952240837880976646039)
      ·
        refine ⟨22244928361256821464969059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14829952240837880976646039 22244928361256821464969059)
        ·
          refine ⟨33367392541885232197453589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22244928361256821464969059 33367392541885232197453589)
          ·
            refine ⟨1564096525400870259255637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33367392541885232197453589 1564096525400870259255637)
            ·
              refine ⟨4582314039260362087663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1564096525400870259255637 4582314039260362087663)
              ·
                rfl

theorem cell22_361423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 10].length) (baseStart_361423 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361423 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361423 prefixEnd_361423 := by exact prefixLift 361423
  have htrace : WordTrace (prefixWord ++ tailWord_361423) baseStart_361423 baseEnd_361423 := by
    simpa [prefixWord, tailWord_361423, baseEnd_361423] using wordTrace_append hprefix tailTrace_361423
  have hstable : (prefixWord ++ tailWord_361423).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361423).length < 2 ^ (prefixWord ++ tailWord_361423).sum := by decide
  have hdescent : baseEnd_361423 < baseStart_361423 := by decide
  rcases family_descends (prefixWord ++ tailWord_361423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361425 : List Nat := [1, 2, 2, 1, 2, 1, 5, 2, 2, 4]
def baseStart_361425 : Nat := 118140960795 + 361425 * 2 ^ 59
def prefixEnd_361425 : Nat := 4983230072969 + 3 ^ 40 * 361425 * 2
def baseEnd_361425 : Nat := 123723163700902437816895

theorem tailTrace_361425 : CollatzResearch.WordTrace tailWord_361425 prefixEnd_361425 123723163700902437816895 := by
  unfold tailWord_361425
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182252715626426320813729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8788168477084284213875819 13182252715626426320813729)
  ·
    refine ⟨9886689536719819740610297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13182252715626426320813729 9886689536719819740610297)
    ·
      refine ⟨7415017152539864805457723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9886689536719819740610297 7415017152539864805457723)
      ·
        refine ⟨11122525728809797208186585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7415017152539864805457723 11122525728809797208186585)
        ·
          refine ⟨8341894296607347906139939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11122525728809797208186585 8341894296607347906139939)
          ·
            refine ⟨12512841444911021859209909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8341894296607347906139939 12512841444911021859209909)
            ·
              refine ⟨1173078885460408299300929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12512841444911021859209909 1173078885460408299300929)
              ·
                refine ⟨879809164095306224475697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1173078885460408299300929 879809164095306224475697)
                ·
                  refine ⟨659856873071479668356773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 879809164095306224475697 659856873071479668356773)
                  ·
                    refine ⟨123723163700902437816895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 659856873071479668356773 123723163700902437816895)
                    ·
                      rfl

theorem cell22_361425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 5, 2, 2, 4].length) (baseStart_361425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361425 prefixEnd_361425 := by exact prefixLift 361425
  have htrace : WordTrace (prefixWord ++ tailWord_361425) baseStart_361425 baseEnd_361425 := by
    simpa [prefixWord, tailWord_361425, baseEnd_361425] using wordTrace_append hprefix tailTrace_361425
  have hstable : (prefixWord ++ tailWord_361425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361425).length < 2 ^ (prefixWord ++ tailWord_361425).sum := by decide
  have hdescent : baseEnd_361425 < baseStart_361425 := by decide
  rcases family_descends (prefixWord ++ tailWord_361425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361429 : List Nat := [1, 3, 2, 3, 4, 1, 1, 1, 6]
def baseStart_361429 : Nat := 118140960795 + 361429 * 2 ^ 59
def prefixEnd_361429 : Nat := 4983230072969 + 3 ^ 40 * 361429 * 2
def baseEnd_361429 : Nat := 41241510994215920238961

theorem tailTrace_361429 : CollatzResearch.WordTrace tailWord_361429 prefixEnd_361429 41241510994215920238961 := by
  unfold tailWord_361429
  simp only [CollatzResearch.WordTrace]
  refine ⟨13182398607611935003959341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8788265738407956669306227 13182398607611935003959341)
  ·
    refine ⟨4943399477854475626484753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13182398607611935003959341 4943399477854475626484753)
    ·
      refine ⟨3707549608390856719863565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4943399477854475626484753 3707549608390856719863565)
      ·
        refine ⟨1390331103146571269948837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3707549608390856719863565 1390331103146571269948837)
        ·
          refine ⟨260687081839982113115407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1390331103146571269948837 260687081839982113115407)
          ·
            refine ⟨391030622759973169673111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 260687081839982113115407 391030622759973169673111)
            ·
              refine ⟨586545934139959754509667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391030622759973169673111 586545934139959754509667)
              ·
                refine ⟨879818901209939631764501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 586545934139959754509667 879818901209939631764501)
                ·
                  refine ⟨41241510994215920238961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 879818901209939631764501 41241510994215920238961)
                  ·
                    rfl

theorem cell22_361429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 4, 1, 1, 1, 6].length) (baseStart_361429 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361429 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361429 prefixEnd_361429 := by exact prefixLift 361429
  have htrace : WordTrace (prefixWord ++ tailWord_361429) baseStart_361429 baseEnd_361429 := by
    simpa [prefixWord, tailWord_361429, baseEnd_361429] using wordTrace_append hprefix tailTrace_361429
  have hstable : (prefixWord ++ tailWord_361429).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361429).length < 2 ^ (prefixWord ++ tailWord_361429).sum := by decide
  have hdescent : baseEnd_361429 < baseStart_361429 := by decide
  rcases family_descends (prefixWord ++ tailWord_361429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361474 : List Nat := [3, 4, 1, 3, 2, 9]
def baseStart_361474 : Nat := 118140960795 + 361474 * 2 ^ 59
def prefixEnd_361474 : Nat := 4983230072969 + 3 ^ 40 * 361474 * 2
def baseEnd_361474 : Nat := 1527653548176328930145

theorem tailTrace_361474 : CollatzResearch.WordTrace tailWord_361474 prefixEnd_361474 1527653548176328930145 := by
  unfold tailWord_361474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3296009973112226922336869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8789359928299271792898317 3296009973112226922336869)
  ·
    refine ⟨618001869958542547938163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3296009973112226922336869 618001869958542547938163)
    ·
      refine ⟨927002804937813821907245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 618001869958542547938163 927002804937813821907245)
      ·
        refine ⟨347626051851680183215217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 927002804937813821907245 347626051851680183215217)
        ·
          refine ⟨260719538888760137411413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 347626051851680183215217 260719538888760137411413)
          ·
            refine ⟨1527653548176328930145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 260719538888760137411413 1527653548176328930145)
            ·
              rfl

theorem cell22_361474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 2, 9].length) (baseStart_361474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361474 prefixEnd_361474 := by exact prefixLift 361474
  have htrace : WordTrace (prefixWord ++ tailWord_361474) baseStart_361474 baseEnd_361474 := by
    simpa [prefixWord, tailWord_361474, baseEnd_361474] using wordTrace_append hprefix tailTrace_361474
  have hstable : (prefixWord ++ tailWord_361474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361474).length < 2 ^ (prefixWord ++ tailWord_361474).sum := by decide
  have hdescent : baseEnd_361474 < baseStart_361474 := by decide
  rcases family_descends (prefixWord ++ tailWord_361474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361515 : List Nat := [1, 1, 1, 1, 2, 1, 5, 3, 3, 4]
def baseStart_361515 : Nat := 118140960795 + 361515 * 2 ^ 59
def prefixEnd_361515 : Nat := 4983230072969 + 3 ^ 40 * 361515 * 2
def baseEnd_361515 : Nat := 123753972540172203066619

theorem tailTrace_361515 : CollatzResearch.WordTrace tailWord_361515 prefixEnd_361515 123753972540172203066619 := by
  unfold tailWord_361515
  simp only [CollatzResearch.WordTrace]
  refine ⟨13185535285300371691589999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8790356856866914461059999 13185535285300371691589999)
  ·
    refine ⟨19778302927950557537384999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13185535285300371691589999 19778302927950557537384999)
    ·
      refine ⟨29667454391925836306077499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19778302927950557537384999 29667454391925836306077499)
      ·
        refine ⟨44501181587888754459116249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29667454391925836306077499 44501181587888754459116249)
        ·
          refine ⟨33375886190916565844337187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 44501181587888754459116249 33375886190916565844337187)
          ·
            refine ⟨50063829286374848766505781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33375886190916565844337187 50063829286374848766505781)
            ·
              refine ⟨4693483995597642071859917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50063829286374848766505781 4693483995597642071859917)
              ·
                refine ⟨1760056498349115776947469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4693483995597642071859917 1760056498349115776947469)
                ·
                  refine ⟨660021186880918416355301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1760056498349115776947469 660021186880918416355301)
                  ·
                    refine ⟨123753972540172203066619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660021186880918416355301 123753972540172203066619)
                    ·
                      rfl

theorem cell22_361515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 3, 3, 4].length) (baseStart_361515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361515 prefixEnd_361515 := by exact prefixLift 361515
  have htrace : WordTrace (prefixWord ++ tailWord_361515) baseStart_361515 baseEnd_361515 := by
    simpa [prefixWord, tailWord_361515, baseEnd_361515] using wordTrace_append hprefix tailTrace_361515
  have hstable : (prefixWord ++ tailWord_361515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361515).length < 2 ^ (prefixWord ++ tailWord_361515).sum := by decide
  have hdescent : baseEnd_361515 < baseStart_361515 := by decide
  rcases family_descends (prefixWord ++ tailWord_361515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361560 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 3, 6]
def baseStart_361560 : Nat := 118140960795 + 361560 * 2 ^ 59
def prefixEnd_361560 : Nat := 4983230072969 + 3 ^ 40 * 361560 * 2
def baseEnd_361560 : Nat := 123769376959807085691481

theorem tailTrace_361560 : CollatzResearch.WordTrace tailWord_361560 prefixEnd_361560 123769376959807085691481 := by
  unfold tailWord_361560
  simp only [CollatzResearch.WordTrace]
  refine ⟨6593588285068672188489067, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8791451046758229584652089 6593588285068672188489067)
  ·
    refine ⟨9890382427603008282733601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6593588285068672188489067 9890382427603008282733601)
    ·
      refine ⟨7417786820702256212050201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9890382427603008282733601 7417786820702256212050201)
      ·
        refine ⟨5563340115526692159037651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7417786820702256212050201 5563340115526692159037651)
        ·
          refine ⟨8345010173290038238556477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5563340115526692159037651 8345010173290038238556477)
          ·
            refine ⟨3129378814983764339458679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8345010173290038238556477 3129378814983764339458679)
            ·
              refine ⟨4694068222475646509188019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3129378814983764339458679 4694068222475646509188019)
              ·
                refine ⟨7041102333713469763782029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4694068222475646509188019 7041102333713469763782029)
                ·
                  refine ⟨2640413375142551161418261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 7041102333713469763782029 2640413375142551161418261)
                  ·
                    refine ⟨123769376959807085691481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2640413375142551161418261 123769376959807085691481)
                    ·
                      rfl

theorem cell22_361560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 6].length) (baseStart_361560 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361560 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361560 prefixEnd_361560 := by exact prefixLift 361560
  have htrace : WordTrace (prefixWord ++ tailWord_361560) baseStart_361560 baseEnd_361560 := by
    simpa [prefixWord, tailWord_361560, baseEnd_361560] using wordTrace_append hprefix tailTrace_361560
  have hstable : (prefixWord ++ tailWord_361560).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361560).length < 2 ^ (prefixWord ++ tailWord_361560).sum := by decide
  have hdescent : baseEnd_361560 < baseStart_361560 := by decide
  rcases family_descends (prefixWord ++ tailWord_361560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361581 : List Nat := [1, 5, 1, 1, 2, 4, 1, 3, 4]
def baseStart_361581 : Nat := 118140960795 + 361581 * 2 ^ 59
def prefixEnd_361581 : Nat := 4983230072969 + 3 ^ 40 * 361581 * 2
def baseEnd_361581 : Nat := 41258855229656676972139

theorem tailTrace_361581 : CollatzResearch.WordTrace tailWord_361581 prefixEnd_361581 41258855229656676972139 := by
  unfold tailWord_361581
  simp only [CollatzResearch.WordTrace]
  refine ⟨13187942503061264963492597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8791961668707509975661731 13187942503061264963492597)
  ·
    refine ⟨1236369609661993590327431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13187942503061264963492597 1236369609661993590327431)
    ·
      refine ⟨1854554414492990385491147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1236369609661993590327431 1854554414492990385491147)
      ·
        refine ⟨2781831621739485578236721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1854554414492990385491147 2781831621739485578236721)
        ·
          refine ⟨2086373716304614183677541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2781831621739485578236721 2086373716304614183677541)
          ·
            refine ⟨391195071807115159439539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2086373716304614183677541 391195071807115159439539)
            ·
              refine ⟨586792607710672739159309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 391195071807115159439539 586792607710672739159309)
              ·
                refine ⟨220047227891502277184741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 586792607710672739159309 220047227891502277184741)
                ·
                  refine ⟨41258855229656676972139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220047227891502277184741 41258855229656676972139)
                  ·
                    rfl

theorem cell22_361581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_361581 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361581 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361581 prefixEnd_361581 := by exact prefixLift 361581
  have htrace : WordTrace (prefixWord ++ tailWord_361581) baseStart_361581 baseEnd_361581 := by
    simpa [prefixWord, tailWord_361581, baseEnd_361581] using wordTrace_append hprefix tailTrace_361581
  have hstable : (prefixWord ++ tailWord_361581).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361581).length < 2 ^ (prefixWord ++ tailWord_361581).sum := by decide
  have hdescent : baseEnd_361581 < baseStart_361581 := by decide
  rcases family_descends (prefixWord ++ tailWord_361581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361701 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 1, 4]
def baseStart_361701 : Nat := 118140960795 + 361701 * 2 ^ 59
def prefixEnd_361701 : Nat := 4983230072969 + 3 ^ 40 * 361701 * 2
def baseEnd_361701 : Nat := 123817644141329717916049

theorem tailTrace_361701 : CollatzResearch.WordTrace tailWord_361701 prefixEnd_361701 123817644141329717916049 := by
  unfold tailWord_361701
  simp only [CollatzResearch.WordTrace]
  refine ⟨13192319262626525457860957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8794879508417683638573971 13192319262626525457860957)
  ·
    refine ⟨4947119723484947046697859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13192319262626525457860957 4947119723484947046697859)
    ·
      refine ⟨7420679585227420570046789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4947119723484947046697859 7420679585227420570046789)
      ·
        refine ⟨1391377422230141356883773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7420679585227420570046789 1391377422230141356883773)
        ·
          refine ⟨521766533336303008831415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1391377422230141356883773 521766533336303008831415)
          ·
            refine ⟨782649800004454513247123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521766533336303008831415 782649800004454513247123)
            ·
              refine ⟨1173974700006681769870685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782649800004454513247123 1173974700006681769870685)
              ·
                refine ⟨440240512502505663701507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1173974700006681769870685 440240512502505663701507)
                ·
                  refine ⟨660360768753758495552261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440240512502505663701507 660360768753758495552261)
                  ·
                    refine ⟨123817644141329717916049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660360768753758495552261 123817644141329717916049)
                    ·
                      rfl

theorem cell22_361701_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 4].length) (baseStart_361701 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361701 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361701 prefixEnd_361701 := by exact prefixLift 361701
  have htrace : WordTrace (prefixWord ++ tailWord_361701) baseStart_361701 baseEnd_361701 := by
    simpa [prefixWord, tailWord_361701, baseEnd_361701] using wordTrace_append hprefix tailTrace_361701
  have hstable : (prefixWord ++ tailWord_361701).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361701).length < 2 ^ (prefixWord ++ tailWord_361701).sum := by decide
  have hdescent : baseEnd_361701 < baseStart_361701 := by decide
  rcases family_descends (prefixWord ++ tailWord_361701) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361787 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 8, 5]
def baseStart_361787 : Nat := 118140960795 + 361787 * 2 ^ 59
def prefixEnd_361787 : Nat := 4983230072969 + 3 ^ 40 * 361787 * 2
def baseEnd_361787 : Nat := 123847083698854160265785

theorem tailTrace_361787 : CollatzResearch.WordTrace tailWord_361787 prefixEnd_361787 123847083698854160265785 := by
  unfold tailWord_361787
  simp only [CollatzResearch.WordTrace]
  refine ⟨13195455940314962145491615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8796970626876641430327743 13195455940314962145491615)
  ·
    refine ⟨19793183910472443218237423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13195455940314962145491615 19793183910472443218237423)
    ·
      refine ⟨29689775865708664827356135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19793183910472443218237423 29689775865708664827356135)
      ·
        refine ⟨44534663798562997241034203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29689775865708664827356135 44534663798562997241034203)
        ·
          refine ⟨66801995697844495861551305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44534663798562997241034203 66801995697844495861551305)
          ·
            refine ⟨50101496773383371896163479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 66801995697844495861551305 50101496773383371896163479)
            ·
              refine ⟨75152245160075057844245219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50101496773383371896163479 75152245160075057844245219)
              ·
                refine ⟨112728367740112586766367829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 75152245160075057844245219 112728367740112586766367829)
                ·
                  refine ⟨1321035559454444376168373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 112728367740112586766367829 1321035559454444376168373)
                  ·
                    refine ⟨123847083698854160265785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1321035559454444376168373 123847083698854160265785)
                    ·
                      rfl

theorem cell22_361787_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 5].length) (baseStart_361787 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361787 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361787 prefixEnd_361787 := by exact prefixLift 361787
  have htrace : WordTrace (prefixWord ++ tailWord_361787) baseStart_361787 baseEnd_361787 := by
    simpa [prefixWord, tailWord_361787, baseEnd_361787] using wordTrace_append hprefix tailTrace_361787
  have hstable : (prefixWord ++ tailWord_361787).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361787).length < 2 ^ (prefixWord ++ tailWord_361787).sum := by decide
  have hdescent : baseEnd_361787 < baseStart_361787 := by decide
  rcases family_descends (prefixWord ++ tailWord_361787) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361838 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 2, 5]
def baseStart_361838 : Nat := 118140960795 + 361838 * 2 ^ 59
def prefixEnd_361838 : Nat := 4983230072969 + 3 ^ 40 * 361838 * 2
def baseEnd_361838 : Nat := 123864542041107027240629

theorem tailTrace_361838 : CollatzResearch.WordTrace tailWord_361838 prefixEnd_361838 123864542041107027240629 := by
  unfold tailWord_361838
  simp only [CollatzResearch.WordTrace]
  refine ⟨1649664507891274731949771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8798210708753465237065445 1649664507891274731949771)
  ·
    refine ⟨2474496761836912097924657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1649664507891274731949771 2474496761836912097924657)
    ·
      refine ⟨1855872571377684073443493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2474496761836912097924657 1855872571377684073443493)
      ·
        refine ⟨347976107133315763770655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1855872571377684073443493 347976107133315763770655)
        ·
          refine ⟨521964160699973645655983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 347976107133315763770655 521964160699973645655983)
          ·
            refine ⟨782946241049960468483975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 521964160699973645655983 782946241049960468483975)
            ·
              refine ⟨1174419361574940702725963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 782946241049960468483975 1174419361574940702725963)
              ·
                refine ⟨1761629042362411054088945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1174419361574940702725963 1761629042362411054088945)
                ·
                  refine ⟨1321221781771808290566709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1761629042362411054088945 1321221781771808290566709)
                  ·
                    refine ⟨123864542041107027240629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1321221781771808290566709 123864542041107027240629)
                    ·
                      rfl

theorem cell22_361838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 5].length) (baseStart_361838 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361838 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361838 prefixEnd_361838 := by exact prefixLift 361838
  have htrace : WordTrace (prefixWord ++ tailWord_361838) baseStart_361838 baseEnd_361838 := by
    simpa [prefixWord, tailWord_361838, baseEnd_361838] using wordTrace_append hprefix tailTrace_361838
  have hstable : (prefixWord ++ tailWord_361838).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361838).length < 2 ^ (prefixWord ++ tailWord_361838).sum := by decide
  have hdescent : baseEnd_361838 < baseStart_361838 := by decide
  rcases family_descends (prefixWord ++ tailWord_361838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361849 : List Nat := [1, 2, 1, 3, 2, 1, 3, 3, 1, 5]
def baseStart_361849 : Nat := 118140960795 + 361849 * 2 ^ 59
def prefixEnd_361849 : Nat := 4983230072969 + 3 ^ 40 * 361849 * 2
def baseEnd_361849 : Nat := 123868307565906665215595

theorem tailTrace_361849 : CollatzResearch.WordTrace tailWord_361849 prefixEnd_361849 123868307565906665215595 := by
  unfold tailWord_361849
  simp only [CollatzResearch.WordTrace]
  refine ⟨13197717266090346734248601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8798478177393564489499067 13197717266090346734248601)
  ·
    refine ⟨9898287949567760050686451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13197717266090346734248601 9898287949567760050686451)
    ·
      refine ⟨14847431924351640076029677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9898287949567760050686451 14847431924351640076029677)
      ·
        refine ⟨5567786971631865028511129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14847431924351640076029677 5567786971631865028511129)
        ·
          refine ⟨4175840228723898771383347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5567786971631865028511129 4175840228723898771383347)
          ·
            refine ⟨6263760343085848157075021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4175840228723898771383347 6263760343085848157075021)
            ·
              refine ⟨2348910128657193058903133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6263760343085848157075021 2348910128657193058903133)
              ·
                refine ⟨880841298246447397088675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2348910128657193058903133 880841298246447397088675)
                ·
                  refine ⟨1321261947369671095633013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 880841298246447397088675 1321261947369671095633013)
                  ·
                    refine ⟨123868307565906665215595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1321261947369671095633013 123868307565906665215595)
                    ·
                      rfl

theorem cell22_361849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 3, 3, 1, 5].length) (baseStart_361849 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361849 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361849 prefixEnd_361849 := by exact prefixLift 361849
  have htrace : WordTrace (prefixWord ++ tailWord_361849) baseStart_361849 baseEnd_361849 := by
    simpa [prefixWord, tailWord_361849, baseEnd_361849] using wordTrace_append hprefix tailTrace_361849
  have hstable : (prefixWord ++ tailWord_361849).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361849).length < 2 ^ (prefixWord ++ tailWord_361849).sum := by decide
  have hdescent : baseEnd_361849 < baseStart_361849 := by decide
  rcases family_descends (prefixWord ++ tailWord_361849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361911 : List Nat := [1, 1, 3, 1, 3, 2, 1, 4, 3, 3]
def baseStart_361911 : Nat := 118140960795 + 361911 * 2 ^ 59
def prefixEnd_361911 : Nat := 4983230072969 + 3 ^ 40 * 361911 * 2
def baseEnd_361911 : Nat := 123889531432959170165405

theorem tailTrace_361911 : CollatzResearch.WordTrace tailWord_361911 prefixEnd_361911 123889531432959170165405 := by
  unfold tailWord_361911
  simp only [CollatzResearch.WordTrace]
  refine ⟨13199978591865731323005587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8799985727910487548670391 13199978591865731323005587)
  ·
    refine ⟨19799967887798596984508381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13199978591865731323005587 19799967887798596984508381)
    ·
      refine ⟨7424987957924473869190643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19799967887798596984508381 7424987957924473869190643)
      ·
        refine ⟨11137481936886710803785965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7424987957924473869190643 11137481936886710803785965)
        ·
          refine ⟨4176555726332516551419737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11137481936886710803785965 4176555726332516551419737)
          ·
            refine ⟨3132416794749387413564803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4176555726332516551419737 3132416794749387413564803)
            ·
              refine ⟨4698625192124081120347205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3132416794749387413564803 4698625192124081120347205)
              ·
                refine ⟨880992223523265210065101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4698625192124081120347205 880992223523265210065101)
                ·
                  refine ⟨330372083821224453774413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 880992223523265210065101 330372083821224453774413)
                  ·
                    refine ⟨123889531432959170165405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330372083821224453774413 123889531432959170165405)
                    ·
                      rfl

theorem cell22_361911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 4, 3, 3].length) (baseStart_361911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361911 prefixEnd_361911 := by exact prefixLift 361911
  have htrace : WordTrace (prefixWord ++ tailWord_361911) baseStart_361911 baseEnd_361911 := by
    simpa [prefixWord, tailWord_361911, baseEnd_361911] using wordTrace_append hprefix tailTrace_361911
  have hstable : (prefixWord ++ tailWord_361911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361911).length < 2 ^ (prefixWord ++ tailWord_361911).sum := by decide
  have hdescent : baseEnd_361911 < baseStart_361911 := by decide
  rcases family_descends (prefixWord ++ tailWord_361911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361913 : List Nat := [1, 2, 1, 4, 4, 2, 2, 6]
def baseStart_361913 : Nat := 118140960795 + 361913 * 2 ^ 59
def prefixEnd_361913 : Nat := 4983230072969 + 3 ^ 40 * 361913 * 2
def baseEnd_361913 : Nat := 13765579563759092401711

theorem tailTrace_361913 : CollatzResearch.WordTrace tailWord_361913 prefixEnd_361913 13765579563759092401711 := by
  unfold tailWord_361913
  simp only [CollatzResearch.WordTrace]
  refine ⟨13200051537858485664578393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8800034358572323776385595 13200051537858485664578393)
  ·
    refine ⟨9900038653393864248433795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13200051537858485664578393 9900038653393864248433795)
    ·
      refine ⟨14850057980090796372650693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9900038653393864248433795 14850057980090796372650693)
      ·
        refine ⟨2784385871267024319872005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14850057980090796372650693 2784385871267024319872005)
        ·
          refine ⟨522072350862567059976001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2784385871267024319872005 522072350862567059976001)
          ·
            refine ⟨391554263146925294982001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522072350862567059976001 391554263146925294982001)
            ·
              refine ⟨293665697360193971236501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 391554263146925294982001 293665697360193971236501)
              ·
                refine ⟨13765579563759092401711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 293665697360193971236501 13765579563759092401711)
                ·
                  rfl

theorem cell22_361913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 4, 2, 2, 6].length) (baseStart_361913 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361913 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361913 prefixEnd_361913 := by exact prefixLift 361913
  have htrace : WordTrace (prefixWord ++ tailWord_361913) baseStart_361913 baseEnd_361913 := by
    simpa [prefixWord, tailWord_361913, baseEnd_361913] using wordTrace_append hprefix tailTrace_361913
  have hstable : (prefixWord ++ tailWord_361913).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361913).length < 2 ^ (prefixWord ++ tailWord_361913).sum := by decide
  have hdescent : baseEnd_361913 < baseStart_361913 := by decide
  rcases family_descends (prefixWord ++ tailWord_361913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361941 : List Nat := [1, 3, 2, 3, 1, 1, 2, 4, 5]
def baseStart_361941 : Nat := 118140960795 + 361941 * 2 ^ 59
def prefixEnd_361941 : Nat := 4983230072969 + 3 ^ 40 * 361941 * 2
def baseEnd_361941 : Nat := 41299933682016363971771

theorem tailTrace_361941 : CollatzResearch.WordTrace tailWord_361941 prefixEnd_361941 41299933682016363971771 := by
  unfold tailWord_361941
  simp only [CollatzResearch.WordTrace]
  refine ⟨13201072781757046446597677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8800715187838030964398451 13201072781757046446597677)
  ·
    refine ⟨4950402293158892417474129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13201072781757046446597677 4950402293158892417474129)
    ·
      refine ⟨3712801719869169313105597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4950402293158892417474129 3712801719869169313105597)
      ·
        refine ⟨1392300644950938492414599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3712801719869169313105597 1392300644950938492414599)
        ·
          refine ⟨2088450967426407738621899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1392300644950938492414599 2088450967426407738621899)
          ·
            refine ⟨3132676451139611607932849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2088450967426407738621899 3132676451139611607932849)
            ·
              refine ⟨2349507338354708705949637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3132676451139611607932849 2349507338354708705949637)
              ·
                refine ⟨440532625941507882365557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2349507338354708705949637 440532625941507882365557)
                ·
                  refine ⟨41299933682016363971771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 440532625941507882365557 41299933682016363971771)
                  ·
                    rfl

theorem cell22_361941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 2, 4, 5].length) (baseStart_361941 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361941 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361941 prefixEnd_361941 := by exact prefixLift 361941
  have htrace : WordTrace (prefixWord ++ tailWord_361941) baseStart_361941 baseEnd_361941 := by
    simpa [prefixWord, tailWord_361941, baseEnd_361941] using wordTrace_append hprefix tailTrace_361941
  have hstable : (prefixWord ++ tailWord_361941).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361941).length < 2 ^ (prefixWord ++ tailWord_361941).sum := by decide
  have hdescent : baseEnd_361941 < baseStart_361941 := by decide
  rcases family_descends (prefixWord ++ tailWord_361941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_361971 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 1, 4]
def baseStart_361971 : Nat := 118140960795 + 361971 * 2 ^ 59
def prefixEnd_361971 : Nat := 4983230072969 + 3 ^ 40 * 361971 * 2
def baseEnd_361971 : Nat := 123910070659139013665221

theorem tailTrace_361971 : CollatzResearch.WordTrace tailWord_361971 prefixEnd_361971 123910070659139013665221 := by
  unfold tailWord_361971
  simp only [CollatzResearch.WordTrace]
  refine ⟨13202166971648361570189767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8801444647765574380126511 13202166971648361570189767)
  ·
    refine ⟨19803250457472542355284651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13202166971648361570189767 19803250457472542355284651)
    ·
      refine ⟨29704875686208813532926977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19803250457472542355284651 29704875686208813532926977)
      ·
        refine ⟨22278656764656610149695233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29704875686208813532926977 22278656764656610149695233)
        ·
          refine ⟨16708992573492457612271425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22278656764656610149695233 16708992573492457612271425)
          ·
            refine ⟨12531744430119343209203569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16708992573492457612271425 12531744430119343209203569)
            ·
              refine ⟨9398808322589507406902677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12531744430119343209203569 9398808322589507406902677)
              ·
                refine ⟨440569140121383159698563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9398808322589507406902677 440569140121383159698563)
                ·
                  refine ⟨660853710182074739547845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440569140121383159698563 660853710182074739547845)
                  ·
                    refine ⟨123910070659139013665221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 660853710182074739547845 123910070659139013665221)
                    ·
                      rfl

theorem cell22_361971_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 4].length) (baseStart_361971 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_361971 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_361971 prefixEnd_361971 := by exact prefixLift 361971
  have htrace : WordTrace (prefixWord ++ tailWord_361971) baseStart_361971 baseEnd_361971 := by
    simpa [prefixWord, tailWord_361971, baseEnd_361971] using wordTrace_append hprefix tailTrace_361971
  have hstable : (prefixWord ++ tailWord_361971).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_361971).length < 2 ^ (prefixWord ++ tailWord_361971).sum := by decide
  have hdescent : baseEnd_361971 < baseStart_361971 := by decide
  rcases family_descends (prefixWord ++ tailWord_361971) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362003 : List Nat := [1, 1, 1, 2, 1, 7, 1, 4, 4]
def baseStart_362003 : Nat := 118140960795 + 362003 * 2 ^ 59
def prefixEnd_362003 : Nat := 4983230072969 + 3 ^ 40 * 362003 * 2
def baseEnd_362003 : Nat := 41307008304367198955041

theorem tailTrace_362003 : CollatzResearch.WordTrace tailWord_362003 prefixEnd_362003 41307008304367198955041 := by
  unfold tailWord_362003
  simp only [CollatzResearch.WordTrace]
  refine ⟨13203334107532431035354663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8802222738354954023569775 13203334107532431035354663)
  ·
    refine ⟨19805001161298646553031995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13203334107532431035354663 19805001161298646553031995)
    ·
      refine ⟨29707501741947969829547993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19805001161298646553031995 29707501741947969829547993)
      ·
        refine ⟨22280626306460977372160995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29707501741947969829547993 22280626306460977372160995)
        ·
          refine ⟨33420939459691466058241493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22280626306460977372160995 33420939459691466058241493)
          ·
            refine ⟨783303268586518735740035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33420939459691466058241493 783303268586518735740035)
            ·
              refine ⟨1174954902879778103610053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783303268586518735740035 1174954902879778103610053)
              ·
                refine ⟨220304044289958394426885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1174954902879778103610053 220304044289958394426885)
                ·
                  refine ⟨41307008304367198955041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220304044289958394426885 41307008304367198955041)
                  ·
                    rfl

theorem cell22_362003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 7, 1, 4, 4].length) (baseStart_362003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362003 prefixEnd_362003 := by exact prefixLift 362003
  have htrace : WordTrace (prefixWord ++ tailWord_362003) baseStart_362003 baseEnd_362003 := by
    simpa [prefixWord, tailWord_362003, baseEnd_362003] using wordTrace_append hprefix tailTrace_362003
  have hstable : (prefixWord ++ tailWord_362003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362003).length < 2 ^ (prefixWord ++ tailWord_362003).sum := by decide
  have hdescent : baseEnd_362003 < baseStart_362003 := by decide
  rcases family_descends (prefixWord ++ tailWord_362003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362140 : List Nat := [2, 2, 3, 2, 3, 1, 1, 1, 3, 4]
def baseStart_362140 : Nat := 118140960795 + 362140 * 2 ^ 59
def prefixEnd_362140 : Nat := 4983230072969 + 3 ^ 40 * 362140 * 2
def baseEnd_362140 : Nat := 123967922812878906189703

theorem tailTrace_362140 : CollatzResearch.WordTrace tailWord_362140 prefixEnd_362140 123967922812878906189703 := by
  unfold tailWord_362140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604165454018051716545937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8805553938690735622061249 6604165454018051716545937)
  ·
    refine ⟨4953124090513538787409453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6604165454018051716545937 4953124090513538787409453)
    ·
      refine ⟨1857421533942577045278545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4953124090513538787409453 1857421533942577045278545)
      ·
        refine ⟨1393066150456932783958909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1857421533942577045278545 1393066150456932783958909)
        ·
          refine ⟨522399806421349793984591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1393066150456932783958909 522399806421349793984591)
          ·
            refine ⟨783599709632024690976887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522399806421349793984591 783599709632024690976887)
            ·
              refine ⟨1175399564448037036465331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 783599709632024690976887 1175399564448037036465331)
              ·
                refine ⟨1763099346672055554697997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175399564448037036465331 1763099346672055554697997)
                ·
                  refine ⟨661162255002020833011749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1763099346672055554697997 661162255002020833011749)
                  ·
                    refine ⟨123967922812878906189703, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 661162255002020833011749 123967922812878906189703)
                    ·
                      rfl

theorem cell22_362140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 3, 1, 1, 1, 3, 4].length) (baseStart_362140 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362140 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362140 prefixEnd_362140 := by exact prefixLift 362140
  have htrace : WordTrace (prefixWord ++ tailWord_362140) baseStart_362140 baseEnd_362140 := by
    simpa [prefixWord, tailWord_362140, baseEnd_362140] using wordTrace_append hprefix tailTrace_362140
  have hstable : (prefixWord ++ tailWord_362140).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362140).length < 2 ^ (prefixWord ++ tailWord_362140).sum := by decide
  have hdescent : baseEnd_362140 < baseStart_362140 := by decide
  rcases family_descends (prefixWord ++ tailWord_362140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362157 : List Nat := [1, 5, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_362157 : Nat := 118140960795 + 362157 * 2 ^ 59
def prefixEnd_362157 : Nat := 4983230072969 + 3 ^ 40 * 362157 * 2
def baseEnd_362157 : Nat := 123973742260296528514651

theorem tailTrace_362157 : CollatzResearch.WordTrace tailWord_362157 prefixEnd_362157 123973742260296528514651 := by
  unfold tailWord_362157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13208950948974515336460725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8805967299316343557640483 13208950948974515336460725)
  ·
    refine ⟨1238339151466360812793193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13208950948974515336460725 1238339151466360812793193)
    ·
      refine ⟨928754363599770609594895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1238339151466360812793193 928754363599770609594895)
      ·
        refine ⟨1393131545399655914392343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 928754363599770609594895 1393131545399655914392343)
        ·
          refine ⟨2089697318099483871588515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393131545399655914392343 2089697318099483871588515)
          ·
            refine ⟨3134545977149225807382773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2089697318099483871588515 3134545977149225807382773)
            ·
              refine ⟨293863685357739919442135, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3134545977149225807382773 293863685357739919442135)
              ·
                refine ⟨440795528036609879163203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 293863685357739919442135 440795528036609879163203)
                ·
                  refine ⟨661193292054914818744805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440795528036609879163203 661193292054914818744805)
                  ·
                    refine ⟨123973742260296528514651, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 661193292054914818744805 123973742260296528514651)
                    ·
                      rfl

theorem cell22_362157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_362157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362157 prefixEnd_362157 := by exact prefixLift 362157
  have htrace : WordTrace (prefixWord ++ tailWord_362157) baseStart_362157 baseEnd_362157 := by
    simpa [prefixWord, tailWord_362157, baseEnd_362157] using wordTrace_append hprefix tailTrace_362157
  have hstable : (prefixWord ++ tailWord_362157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362157).length < 2 ^ (prefixWord ++ tailWord_362157).sum := by decide
  have hdescent : baseEnd_362157 < baseStart_362157 := by decide
  rcases family_descends (prefixWord ++ tailWord_362157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362170 : List Nat := [3, 1, 1, 1, 2, 4, 1, 4, 2, 3]
def baseStart_362170 : Nat := 118140960795 + 362170 * 2 ^ 59
def prefixEnd_362170 : Nat := 4983230072969 + 3 ^ 40 * 362170 * 2
def baseEnd_362170 : Nat := 123978192425968827939611

theorem tailTrace_362170 : CollatzResearch.WordTrace tailWord_362170 prefixEnd_362170 123978192425968827939611 := by
  unfold tailWord_362170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3302356274481854639170991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8806283398618279037789309 3302356274481854639170991)
  ·
    refine ⟨4953534411722781958756487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3302356274481854639170991 4953534411722781958756487)
    ·
      refine ⟨7430301617584172938134731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4953534411722781958756487 7430301617584172938134731)
      ·
        refine ⟨11145452426376259407202097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7430301617584172938134731 11145452426376259407202097)
        ·
          refine ⟨8359089319782194555401573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11145452426376259407202097 8359089319782194555401573)
          ·
            refine ⟨1567329247459161479137795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8359089319782194555401573 1567329247459161479137795)
            ·
              refine ⟨2350993871188742218706693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1567329247459161479137795 2350993871188742218706693)
              ·
                refine ⟨440811350847889166007505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2350993871188742218706693 440811350847889166007505)
                ·
                  refine ⟨330608513135916874505629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 440811350847889166007505 330608513135916874505629)
                  ·
                    refine ⟨123978192425968827939611, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330608513135916874505629 123978192425968827939611)
                    ·
                      rfl

theorem cell22_362170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 4, 1, 4, 2, 3].length) (baseStart_362170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362170 prefixEnd_362170 := by exact prefixLift 362170
  have htrace : WordTrace (prefixWord ++ tailWord_362170) baseStart_362170 baseEnd_362170 := by
    simpa [prefixWord, tailWord_362170, baseEnd_362170] using wordTrace_append hprefix tailTrace_362170
  have hstable : (prefixWord ++ tailWord_362170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362170).length < 2 ^ (prefixWord ++ tailWord_362170).sum := by decide
  have hdescent : baseEnd_362170 < baseStart_362170 := by decide
  rcases family_descends (prefixWord ++ tailWord_362170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362172 : List Nat := [2, 2, 2, 3, 1, 2, 4, 2, 4]
def baseStart_362172 : Nat := 118140960795 + 362172 * 2 ^ 59
def prefixEnd_362172 : Nat := 4983230072969 + 3 ^ 40 * 362172 * 2
def baseEnd_362172 : Nat := 41326292355613829796535

theorem tailTrace_362172 : CollatzResearch.WordTrace tailWord_362172 prefixEnd_362172 41326292355613829796535 := by
  unfold tailWord_362172
  simp only [CollatzResearch.WordTrace]
  refine ⟨6604749021960086449128385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8806332029280115265504513 6604749021960086449128385)
  ·
    refine ⟨4953561766470064836846289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6604749021960086449128385 4953561766470064836846289)
    ·
      refine ⟨3715171324852548627634717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4953561766470064836846289 3715171324852548627634717)
      ·
        refine ⟨1393189246819705735363019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3715171324852548627634717 1393189246819705735363019)
        ·
          refine ⟨2089783870229558603044529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1393189246819705735363019 2089783870229558603044529)
          ·
            refine ⟨1567337902672168952283397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2089783870229558603044529 1567337902672168952283397)
            ·
              refine ⟨293875856751031678553137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1567337902672168952283397 293875856751031678553137)
              ·
                refine ⟨220406892563273758914853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 293875856751031678553137 220406892563273758914853)
                ·
                  refine ⟨41326292355613829796535, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220406892563273758914853 41326292355613829796535)
                  ·
                    rfl

theorem cell22_362172_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 2, 4, 2, 4].length) (baseStart_362172 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362172 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362172 prefixEnd_362172 := by exact prefixLift 362172
  have htrace : WordTrace (prefixWord ++ tailWord_362172) baseStart_362172 baseEnd_362172 := by
    simpa [prefixWord, tailWord_362172, baseEnd_362172] using wordTrace_append hprefix tailTrace_362172
  have hstable : (prefixWord ++ tailWord_362172).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362172).length < 2 ^ (prefixWord ++ tailWord_362172).sum := by decide
  have hdescent : baseEnd_362172 < baseStart_362172 := by decide
  rcases family_descends (prefixWord ++ tailWord_362172) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362243 : List Nat := [1, 1, 1, 3, 2, 2, 4, 1, 2, 5]
def baseStart_362243 : Nat := 118140960795 + 362243 * 2 ^ 59
def prefixEnd_362243 : Nat := 4983230072969 + 3 ^ 40 * 362243 * 2
def baseEnd_362243 : Nat := 124003181817820970864387

theorem tailTrace_362243 : CollatzResearch.WordTrace tailWord_362243 prefixEnd_362243 124003181817820970864387 := by
  unfold tailWord_362243
  simp only [CollatzResearch.WordTrace]
  refine ⟨13212087626662952024091383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8808058417775301349394255 13212087626662952024091383)
  ·
    refine ⟨19818131439994428036137075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13212087626662952024091383 19818131439994428036137075)
    ·
      refine ⟨29727197159991642054205613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19818131439994428036137075 29727197159991642054205613)
      ·
        refine ⟨11147698934996865770327105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29727197159991642054205613 11147698934996865770327105)
        ·
          refine ⟨8360774201247649327745329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11147698934996865770327105 8360774201247649327745329)
          ·
            refine ⟨6270580650935736995808997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8360774201247649327745329 6270580650935736995808997)
            ·
              refine ⟨1175733872050450686714187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6270580650935736995808997 1175733872050450686714187)
              ·
                refine ⟨1763600808075676030071281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1175733872050450686714187 1763600808075676030071281)
                ·
                  refine ⟨1322700606056757022553461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1763600808075676030071281 1322700606056757022553461)
                  ·
                    refine ⟨124003181817820970864387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1322700606056757022553461 124003181817820970864387)
                    ·
                      rfl

theorem cell22_362243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 4, 1, 2, 5].length) (baseStart_362243 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362243 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362243 prefixEnd_362243 := by exact prefixLift 362243
  have htrace : WordTrace (prefixWord ++ tailWord_362243) baseStart_362243 baseEnd_362243 := by
    simpa [prefixWord, tailWord_362243, baseEnd_362243] using wordTrace_append hprefix tailTrace_362243
  have hstable : (prefixWord ++ tailWord_362243).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362243).length < 2 ^ (prefixWord ++ tailWord_362243).sum := by decide
  have hdescent : baseEnd_362243 < baseStart_362243 := by decide
  rcases family_descends (prefixWord ++ tailWord_362243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362275 : List Nat := [1, 1, 1, 4, 2, 1, 4, 3, 1, 4]
def baseStart_362275 : Nat := 118140960795 + 362275 * 2 ^ 59
def prefixEnd_362275 : Nat := 4983230072969 + 3 ^ 40 * 362275 * 2
def baseEnd_362275 : Nat := 124014136071783554064289

theorem tailTrace_362275 : CollatzResearch.WordTrace tailWord_362275 prefixEnd_362275 124014136071783554064289 := by
  unfold tailWord_362275
  simp only [CollatzResearch.WordTrace]
  refine ⟨13213254762547021489256279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8808836508364680992837519 13213254762547021489256279)
  ·
    refine ⟨19819882143820532233884419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13213254762547021489256279 19819882143820532233884419)
    ·
      refine ⟨29729823215730798350826629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19819882143820532233884419 29729823215730798350826629)
      ·
        refine ⟨5574341852949524690779993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29729823215730798350826629 5574341852949524690779993)
        ·
          refine ⟨4180756389712143518084995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5574341852949524690779993 4180756389712143518084995)
          ·
            refine ⟨6271134584568215277127493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4180756389712143518084995 6271134584568215277127493)
            ·
              refine ⟨1175837734606540364461405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6271134584568215277127493 1175837734606540364461405)
              ·
                refine ⟨440939150477452636673027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1175837734606540364461405 440939150477452636673027)
                ·
                  refine ⟨661408725716178955009541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 440939150477452636673027 661408725716178955009541)
                  ·
                    refine ⟨124014136071783554064289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 661408725716178955009541 124014136071783554064289)
                    ·
                      rfl

theorem cell22_362275_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 4, 3, 1, 4].length) (baseStart_362275 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362275 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362275 prefixEnd_362275 := by exact prefixLift 362275
  have htrace : WordTrace (prefixWord ++ tailWord_362275) baseStart_362275 baseEnd_362275 := by
    simpa [prefixWord, tailWord_362275, baseEnd_362275] using wordTrace_append hprefix tailTrace_362275
  have hstable : (prefixWord ++ tailWord_362275).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362275).length < 2 ^ (prefixWord ++ tailWord_362275).sum := by decide
  have hdescent : baseEnd_362275 < baseStart_362275 := by decide
  rcases family_descends (prefixWord ++ tailWord_362275) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362290 : List Nat := [3, 2, 1, 1, 3, 2, 3, 1, 6]
def baseStart_362290 : Nat := 118140960795 + 362290 * 2 ^ 59
def prefixEnd_362290 : Nat := 4983230072969 + 3 ^ 40 * 362290 * 2
def baseEnd_362290 : Nat := 41339756959442838313081

theorem tailTrace_362290 : CollatzResearch.WordTrace tailWord_362290 prefixEnd_362290 41339756959442838313081 := by
  unfold tailWord_362290
  simp only [CollatzResearch.WordTrace]
  refine ⟨3303450464373169762763081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8809201238328452700701549 3303450464373169762763081)
  ·
    refine ⟨2477587848279877322072311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3303450464373169762763081 2477587848279877322072311)
    ·
      refine ⟨3716381772419815983108467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2477587848279877322072311 3716381772419815983108467)
      ·
        refine ⟨5574572658629723974662701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3716381772419815983108467 5574572658629723974662701)
        ·
          refine ⟨2090464746986146490498513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5574572658629723974662701 2090464746986146490498513)
          ·
            refine ⟨1567848560239609867873885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2090464746986146490498513 1567848560239609867873885)
            ·
              refine ⟨587943210089853700452707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1567848560239609867873885 587943210089853700452707)
              ·
                refine ⟨881914815134780550679061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 587943210089853700452707 881914815134780550679061)
                ·
                  refine ⟨41339756959442838313081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 881914815134780550679061 41339756959442838313081)
                  ·
                    rfl

theorem cell22_362290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 2, 3, 1, 6].length) (baseStart_362290 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362290 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362290 prefixEnd_362290 := by exact prefixLift 362290
  have htrace : WordTrace (prefixWord ++ tailWord_362290) baseStart_362290 baseEnd_362290 := by
    simpa [prefixWord, tailWord_362290, baseEnd_362290] using wordTrace_append hprefix tailTrace_362290
  have hstable : (prefixWord ++ tailWord_362290).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362290).length < 2 ^ (prefixWord ++ tailWord_362290).sum := by decide
  have hdescent : baseEnd_362290 < baseStart_362290 := by decide
  rcases family_descends (prefixWord ++ tailWord_362290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362339 : List Nat := [1, 1, 1, 5, 4, 1, 2, 2, 2, 3]
def baseStart_362339 : Nat := 118140960795 + 362339 * 2 ^ 59
def prefixEnd_362339 : Nat := 4983230072969 + 3 ^ 40 * 362339 * 2
def baseEnd_362339 : Nat := 124036044579708720464093

theorem tailTrace_362339 : CollatzResearch.WordTrace tailWord_362339 prefixEnd_362339 124036044579708720464093 := by
  unfold tailWord_362339
  simp only [CollatzResearch.WordTrace]
  refine ⟨13215589034315160419586071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8810392689543440279724047 13215589034315160419586071)
  ·
    refine ⟨19823383551472740629379107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13215589034315160419586071 19823383551472740629379107)
    ·
      refine ⟨29735075327209110944068661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19823383551472740629379107 29735075327209110944068661)
      ·
        refine ⟨2787663311925854151006437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 29735075327209110944068661 2787663311925854151006437)
        ·
          refine ⟨522686870986097653313707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2787663311925854151006437 522686870986097653313707)
          ·
            refine ⟨784030306479146479970561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522686870986097653313707 784030306479146479970561)
            ·
              refine ⟨588022729859359859977921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784030306479146479970561 588022729859359859977921)
              ·
                refine ⟨441017047394519894983441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588022729859359859977921 441017047394519894983441)
                ·
                  refine ⟨330762785545889921237581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441017047394519894983441 330762785545889921237581)
                  ·
                    refine ⟨124036044579708720464093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330762785545889921237581 124036044579708720464093)
                    ·
                      rfl

theorem cell22_362339_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 4, 1, 2, 2, 2, 3].length) (baseStart_362339 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362339 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362339 prefixEnd_362339 := by exact prefixLift 362339
  have htrace : WordTrace (prefixWord ++ tailWord_362339) baseStart_362339 baseEnd_362339 := by
    simpa [prefixWord, tailWord_362339, baseEnd_362339] using wordTrace_append hprefix tailTrace_362339
  have hstable : (prefixWord ++ tailWord_362339).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362339).length < 2 ^ (prefixWord ++ tailWord_362339).sum := by decide
  have hdescent : baseEnd_362339 < baseStart_362339 := by decide
  rcases family_descends (prefixWord ++ tailWord_362339) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362363 : List Nat := [1, 1, 1, 1, 1, 5, 1, 2, 9]
def baseStart_362363 : Nat := 118140960795 + 362363 * 2 ^ 59
def prefixEnd_362363 : Nat := 4983230072969 + 3 ^ 40 * 362363 * 2
def baseEnd_362363 : Nat := 41348086756726885954673

theorem tailTrace_362363 : CollatzResearch.WordTrace tailWord_362363 prefixEnd_362363 41348086756726885954673 := by
  unfold tailWord_362363
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216464386228212518459743, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8810976257485475012306495 13216464386228212518459743)
  ·
    refine ⟨19824696579342318777689615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13216464386228212518459743 19824696579342318777689615)
    ·
      refine ⟨29737044869013478166534423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19824696579342318777689615 29737044869013478166534423)
      ·
        refine ⟨44605567303520217249801635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 29737044869013478166534423 44605567303520217249801635)
        ·
          refine ⟨66908350955280325874702453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 44605567303520217249801635 66908350955280325874702453)
          ·
            refine ⟨6272657902057530550753355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 66908350955280325874702453 6272657902057530550753355)
            ·
              refine ⟨9408986853086295826130033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6272657902057530550753355 9408986853086295826130033)
              ·
                refine ⟨7056740139814721869597525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9408986853086295826130033 7056740139814721869597525)
                ·
                  refine ⟨41348086756726885954673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7056740139814721869597525 41348086756726885954673)
                  ·
                    rfl

theorem cell22_362363_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 5, 1, 2, 9].length) (baseStart_362363 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362363 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362363 prefixEnd_362363 := by exact prefixLift 362363
  have htrace : WordTrace (prefixWord ++ tailWord_362363) baseStart_362363 baseEnd_362363 := by
    simpa [prefixWord, tailWord_362363, baseEnd_362363] using wordTrace_append hprefix tailTrace_362363
  have hstable : (prefixWord ++ tailWord_362363).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362363).length < 2 ^ (prefixWord ++ tailWord_362363).sum := by decide
  have hdescent : baseEnd_362363 < baseStart_362363 := by decide
  rcases family_descends (prefixWord ++ tailWord_362363) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362369 : List Nat := [1, 2, 4, 4, 1, 1, 3, 6]
def baseStart_362369 : Nat := 118140960795 + 362369 * 2 ^ 59
def prefixEnd_362369 : Nat := 4983230072969 + 3 ^ 40 * 362369 * 2
def baseEnd_362369 : Nat := 13782923799199849134889

theorem tailTrace_362369 : CollatzResearch.WordTrace tailWord_362369 prefixEnd_362369 13782923799199849134889 := by
  unfold tailWord_362369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13216683224206475543178161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8811122149470983695452107 13216683224206475543178161)
  ·
    refine ⟨9912512418154856657383621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13216683224206475543178161 9912512418154856657383621)
    ·
      refine ⟨1858596078404035623259429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9912512418154856657383621 1858596078404035623259429)
      ·
        refine ⟨348486764700756679361143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1858596078404035623259429 348486764700756679361143)
        ·
          refine ⟨522730147051135019041715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348486764700756679361143 522730147051135019041715)
          ·
            refine ⟨784095220576702528562573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522730147051135019041715 784095220576702528562573)
            ·
              refine ⟨294035707716263448210965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 784095220576702528562573 294035707716263448210965)
              ·
                refine ⟨13782923799199849134889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 294035707716263448210965 13782923799199849134889)
                ·
                  rfl

theorem cell22_362369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 4, 1, 1, 3, 6].length) (baseStart_362369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362369 prefixEnd_362369 := by exact prefixLift 362369
  have htrace : WordTrace (prefixWord ++ tailWord_362369) baseStart_362369 baseEnd_362369 := by
    simpa [prefixWord, tailWord_362369, baseEnd_362369] using wordTrace_append hprefix tailTrace_362369
  have hstable : (prefixWord ++ tailWord_362369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362369).length < 2 ^ (prefixWord ++ tailWord_362369).sum := by decide
  have hdescent : baseEnd_362369 < baseStart_362369 := by decide
  rcases family_descends (prefixWord ++ tailWord_362369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362390 : List Nat := [5, 3, 1, 1, 2, 2, 1, 2, 2, 3]
def baseStart_362390 : Nat := 118140960795 + 362390 * 2 ^ 59
def prefixEnd_362390 : Nat := 4983230072969 + 3 ^ 40 * 362390 * 2
def baseEnd_362390 : Nat := 124053502921961587438937

theorem tailTrace_362390 : CollatzResearch.WordTrace tailWord_362390 prefixEnd_362390 124053502921961587438937 := by
  unfold tailWord_362390
  simp only [CollatzResearch.WordTrace]
  refine ⟨826090572320649758105789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8811632771420264086461749 826090572320649758105789)
  ·
    refine ⟨309783964620243659289671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 826090572320649758105789 309783964620243659289671)
    ·
      refine ⟨464675946930365488934507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 309783964620243659289671 464675946930365488934507)
      ·
        refine ⟨697013920395548233401761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 464675946930365488934507 697013920395548233401761)
        ·
          refine ⟨522760440296661175051321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697013920395548233401761 522760440296661175051321)
          ·
            refine ⟨392070330222495881288491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 522760440296661175051321 392070330222495881288491)
            ·
              refine ⟨588105495333743821932737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392070330222495881288491 588105495333743821932737)
              ·
                refine ⟨441079121500307866449553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588105495333743821932737 441079121500307866449553)
                ·
                  refine ⟨330809341125230899837165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441079121500307866449553 330809341125230899837165)
                  ·
                    refine ⟨124053502921961587438937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330809341125230899837165 124053502921961587438937)
                    ·
                      rfl

theorem cell22_362390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 2, 2, 1, 2, 2, 3].length) (baseStart_362390 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362390 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362390 prefixEnd_362390 := by exact prefixLift 362390
  have htrace : WordTrace (prefixWord ++ tailWord_362390) baseStart_362390 baseEnd_362390 := by
    simpa [prefixWord, tailWord_362390, baseEnd_362390] using wordTrace_append hprefix tailTrace_362390
  have hstable : (prefixWord ++ tailWord_362390).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362390).length < 2 ^ (prefixWord ++ tailWord_362390).sum := by decide
  have hdescent : baseEnd_362390 < baseStart_362390 := by decide
  rcases family_descends (prefixWord ++ tailWord_362390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362397 : List Nat := [1, 4, 2, 1, 2, 2, 3, 2, 5]
def baseStart_362397 : Nat := 118140960795 + 362397 * 2 ^ 59
def prefixEnd_362397 : Nat := 4983230072969 + 3 ^ 40 * 362397 * 2
def baseEnd_362397 : Nat := 41351966388338634171305

theorem tailTrace_362397 : CollatzResearch.WordTrace tailWord_362397 prefixEnd_362397 41351966388338634171305 := by
  unfold tailWord_362397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13217704468105036325197445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8811802978736690883464963 13217704468105036325197445)
  ·
    refine ⟨2478319587769694310974521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13217704468105036325197445 2478319587769694310974521)
    ·
      refine ⟨1858739690827270733230891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2478319587769694310974521 1858739690827270733230891)
      ·
        refine ⟨2788109536240906099846337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1858739690827270733230891 2788109536240906099846337)
        ·
          refine ⟨2091082152180679574884753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788109536240906099846337 2091082152180679574884753)
          ·
            refine ⟨1568311614135509681163565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2091082152180679574884753 1568311614135509681163565)
            ·
              refine ⟨588116855300816130436337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1568311614135509681163565 588116855300816130436337)
              ·
                refine ⟨441087641475612097827253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588116855300816130436337 441087641475612097827253)
                ·
                  refine ⟨41351966388338634171305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 441087641475612097827253 41351966388338634171305)
                  ·
                    rfl

theorem cell22_362397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 3, 2, 5].length) (baseStart_362397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362397 prefixEnd_362397 := by exact prefixLift 362397
  have htrace : WordTrace (prefixWord ++ tailWord_362397) baseStart_362397 baseEnd_362397 := by
    simpa [prefixWord, tailWord_362397, baseEnd_362397] using wordTrace_append hprefix tailTrace_362397
  have hstable : (prefixWord ++ tailWord_362397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362397).length < 2 ^ (prefixWord ++ tailWord_362397).sum := by decide
  have hdescent : baseEnd_362397 < baseStart_362397 := by decide
  rcases family_descends (prefixWord ++ tailWord_362397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362425 : List Nat := [1, 2, 1, 4, 2, 1, 1, 4, 6]
def baseStart_362425 : Nat := 118140960795 + 362425 * 2 ^ 59
def prefixEnd_362425 : Nat := 4983230072969 + 3 ^ 40 * 362425 * 2
def baseEnd_362425 : Nat := 41355161379077720937943

theorem tailTrace_362425 : CollatzResearch.WordTrace tailWord_362425 prefixEnd_362425 41355161379077720937943 := by
  unfold tailWord_362425
  simp only [CollatzResearch.WordTrace]
  refine ⟨13218725712003597107216729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8812483808002398071477819 13218725712003597107216729)
  ·
    refine ⟨9914044284002697830412547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13218725712003597107216729 9914044284002697830412547)
    ·
      refine ⟨14871066426004046745618821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9914044284002697830412547 14871066426004046745618821)
      ·
        refine ⟨2788324954875758764803529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14871066426004046745618821 2788324954875758764803529)
        ·
          refine ⟨2091243716156819073602647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788324954875758764803529 2091243716156819073602647)
          ·
            refine ⟨3136865574235228610403971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091243716156819073602647 3136865574235228610403971)
            ·
              refine ⟨4705298361352842915605957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3136865574235228610403971 4705298361352842915605957)
              ·
                refine ⟨882243442753658046676117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4705298361352842915605957 882243442753658046676117)
                ·
                  refine ⟨41355161379077720937943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 882243442753658046676117 41355161379077720937943)
                  ·
                    rfl

theorem cell22_362425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 4, 6].length) (baseStart_362425 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362425 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362425 prefixEnd_362425 := by exact prefixLift 362425
  have htrace : WordTrace (prefixWord ++ tailWord_362425) baseStart_362425 baseEnd_362425 := by
    simpa [prefixWord, tailWord_362425, baseEnd_362425] using wordTrace_append hprefix tailTrace_362425
  have hstable : (prefixWord ++ tailWord_362425).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362425).length < 2 ^ (prefixWord ++ tailWord_362425).sum := by decide
  have hdescent : baseEnd_362425 < baseStart_362425 := by decide
  rcases family_descends (prefixWord ++ tailWord_362425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362474 : List Nat := [3, 1, 3, 1, 2, 1, 3, 3, 2, 3]
def baseStart_362474 : Nat := 118140960795 + 362474 * 2 ^ 59
def prefixEnd_362474 : Nat := 4983230072969 + 3 ^ 40 * 362474 * 2
def baseEnd_362474 : Nat := 124082257838613368338679

theorem tailTrace_362474 : CollatzResearch.WordTrace tailWord_362474 prefixEnd_362474 124082257838613368338679 := by
  unfold tailWord_362474
  simp only [CollatzResearch.WordTrace]
  refine ⟨3305128222206519618937619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8813675259217385650500317 3305128222206519618937619)
  ·
    refine ⟨4957692333309779428406429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3305128222206519618937619 4957692333309779428406429)
    ·
      refine ⟨1859134624991167285652411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4957692333309779428406429 1859134624991167285652411)
      ·
        refine ⟨2788701937486750928478617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1859134624991167285652411 2788701937486750928478617)
        ·
          refine ⟨2091526453115063196358963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2788701937486750928478617 2091526453115063196358963)
          ·
            refine ⟨3137289679672594794538445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2091526453115063196358963 3137289679672594794538445)
            ·
              refine ⟨1176483629877223047951917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3137289679672594794538445 1176483629877223047951917)
              ·
                refine ⟨441181361203958642981969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1176483629877223047951917 441181361203958642981969)
                ·
                  refine ⟨330886020902968982236477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441181361203958642981969 330886020902968982236477)
                  ·
                    refine ⟨124082257838613368338679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330886020902968982236477 124082257838613368338679)
                    ·
                      rfl

theorem cell22_362474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 1, 3, 3, 2, 3].length) (baseStart_362474 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362474 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362474 prefixEnd_362474 := by exact prefixLift 362474
  have htrace : WordTrace (prefixWord ++ tailWord_362474) baseStart_362474 baseEnd_362474 := by
    simpa [prefixWord, tailWord_362474, baseEnd_362474] using wordTrace_append hprefix tailTrace_362474
  have hstable : (prefixWord ++ tailWord_362474).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362474).length < 2 ^ (prefixWord ++ tailWord_362474).sum := by decide
  have hdescent : baseEnd_362474 < baseStart_362474 := by decide
  rcases family_descends (prefixWord ++ tailWord_362474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362515 : List Nat := [1, 1, 1, 2, 1, 4, 2, 3, 7]
def baseStart_362515 : Nat := 118140960795 + 362515 * 2 ^ 59
def prefixEnd_362515 : Nat := 4983230072969 + 3 ^ 40 * 362515 * 2
def baseEnd_362515 : Nat := 41365430992167642687851

theorem tailTrace_362515 : CollatzResearch.WordTrace tailWord_362515 prefixEnd_362515 41365430992167642687851 := by
  unfold tailWord_362515
  simp only [CollatzResearch.WordTrace]
  refine ⟨13222008281677542477992999, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8814672187785028318661999 13222008281677542477992999)
  ·
    refine ⟨19833012422516313716989499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13222008281677542477992999 19833012422516313716989499)
    ·
      refine ⟨29749518633774470575484249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19833012422516313716989499 29749518633774470575484249)
      ·
        refine ⟨22312138975330852931613187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29749518633774470575484249 22312138975330852931613187)
        ·
          refine ⟨33468208462996279397419781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22312138975330852931613187 33468208462996279397419781)
          ·
            refine ⟨6275289086811802387016209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33468208462996279397419781 6275289086811802387016209)
            ·
              refine ⟨4706466815108851790262157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6275289086811802387016209 4706466815108851790262157)
              ·
                refine ⟨1764925055665819421348309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4706466815108851790262157 1764925055665819421348309)
                ·
                  refine ⟨41365430992167642687851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1764925055665819421348309 41365430992167642687851)
                  ·
                    rfl

theorem cell22_362515_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 3, 7].length) (baseStart_362515 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362515 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362515 prefixEnd_362515 := by exact prefixLift 362515
  have htrace : WordTrace (prefixWord ++ tailWord_362515) baseStart_362515 baseEnd_362515 := by
    simpa [prefixWord, tailWord_362515, baseEnd_362515] using wordTrace_append hprefix tailTrace_362515
  have hstable : (prefixWord ++ tailWord_362515).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362515).length < 2 ^ (prefixWord ++ tailWord_362515).sum := by decide
  have hdescent : baseEnd_362515 < baseStart_362515 := by decide
  rcases family_descends (prefixWord ++ tailWord_362515) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362553 : List Nat := [1, 2, 1, 5, 3, 1, 2, 3, 1, 3]
def baseStart_362553 : Nat := 118140960795 + 362553 * 2 ^ 59
def prefixEnd_362553 : Nat := 4983230072969 + 3 ^ 40 * 362553 * 2
def baseEnd_362553 : Nat := 124109301153083495613437

theorem tailTrace_362553 : CollatzResearch.WordTrace tailWord_362553 prefixEnd_362553 124109301153083495613437 := by
  unfold tailWord_362553
  simp only [CollatzResearch.WordTrace]
  refine ⟨13223394255539874967876313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8815596170359916645250875 13223394255539874967876313)
  ·
    refine ⟨9917545691654906225907235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13223394255539874967876313 9917545691654906225907235)
    ·
      refine ⟨14876318537482359338860853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9917545691654906225907235 14876318537482359338860853)
      ·
        refine ⟨1394654862888971188018205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14876318537482359338860853 1394654862888971188018205)
        ·
          refine ⟨522995573583364195506827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1394654862888971188018205 522995573583364195506827)
          ·
            refine ⟨784493360375046293260241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 522995573583364195506827 784493360375046293260241)
            ·
              refine ⟨588370020281284719945181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 784493360375046293260241 588370020281284719945181)
              ·
                refine ⟨220638757605481769979443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 588370020281284719945181 220638757605481769979443)
                ·
                  refine ⟨330958136408222654969165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220638757605481769979443 330958136408222654969165)
                  ·
                    refine ⟨124109301153083495613437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 330958136408222654969165 124109301153083495613437)
                    ·
                      rfl

theorem cell22_362553_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 2, 3, 1, 3].length) (baseStart_362553 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362553 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362553 prefixEnd_362553 := by exact prefixLift 362553
  have htrace : WordTrace (prefixWord ++ tailWord_362553) baseStart_362553 baseEnd_362553 := by
    simpa [prefixWord, tailWord_362553, baseEnd_362553] using wordTrace_append hprefix tailTrace_362553
  have hstable : (prefixWord ++ tailWord_362553).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362553).length < 2 ^ (prefixWord ++ tailWord_362553).sum := by decide
  have hdescent : baseEnd_362553 < baseStart_362553 := by decide
  rcases family_descends (prefixWord ++ tailWord_362553) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362607 : List Nat := [1, 1, 2, 1, 3, 4, 2, 1, 1, 6]
def baseStart_362607 : Nat := 118140960795 + 362607 * 2 ^ 59
def prefixEnd_362607 : Nat := 4983230072969 + 3 ^ 40 * 362607 * 2
def baseEnd_362607 : Nat := 124127786456645354763271

theorem tailTrace_362607 : CollatzResearch.WordTrace tailWord_362607 prefixEnd_362607 124127786456645354763271 := by
  unfold tailWord_362607
  simp only [CollatzResearch.WordTrace]
  refine ⟨13225363797344242190342075, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8816909198229494793561383 13225363797344242190342075)
  ·
    refine ⟨19838045696016363285513113, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13225363797344242190342075 19838045696016363285513113)
    ·
      refine ⟨14878534272012272464134835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19838045696016363285513113 14878534272012272464134835)
      ·
        refine ⟨22317801408018408696202253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14878534272012272464134835 22317801408018408696202253)
        ·
          refine ⟨8369175528006903261075845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22317801408018408696202253 8369175528006903261075845)
          ·
            refine ⟨1569220411501294361451721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8369175528006903261075845 1569220411501294361451721)
            ·
              refine ⟨1176915308625970771088791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569220411501294361451721 1176915308625970771088791)
              ·
                refine ⟨1765372962938956156633187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1176915308625970771088791 1765372962938956156633187)
                ·
                  refine ⟨2648059444408434234949781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1765372962938956156633187 2648059444408434234949781)
                  ·
                    refine ⟨124127786456645354763271, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2648059444408434234949781 124127786456645354763271)
                    ·
                      rfl

theorem cell22_362607_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 4, 2, 1, 1, 6].length) (baseStart_362607 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362607 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362607 prefixEnd_362607 := by exact prefixLift 362607
  have htrace : WordTrace (prefixWord ++ tailWord_362607) baseStart_362607 baseEnd_362607 := by
    simpa [prefixWord, tailWord_362607, baseEnd_362607] using wordTrace_append hprefix tailTrace_362607
  have hstable : (prefixWord ++ tailWord_362607).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362607).length < 2 ^ (prefixWord ++ tailWord_362607).sum := by decide
  have hdescent : baseEnd_362607 < baseStart_362607 := by decide
  rcases family_descends (prefixWord ++ tailWord_362607) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362671 : List Nat := [1, 1, 2, 1, 2, 3, 1, 7, 1, 3]
def baseStart_362671 : Nat := 118140960795 + 362671 * 2 ^ 59
def prefixEnd_362671 : Nat := 4983230072969 + 3 ^ 40 * 362671 * 2
def baseEnd_362671 : Nat := 124149694964570521163075

theorem tailTrace_362671 : CollatzResearch.WordTrace tailWord_362671 prefixEnd_362671 124149694964570521163075 := by
  unfold tailWord_362671
  simp only [CollatzResearch.WordTrace]
  refine ⟨13227698069112381120671867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8818465379408254080447911 13227698069112381120671867)
  ·
    refine ⟨19841547103668571681007801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13227698069112381120671867 19841547103668571681007801)
    ·
      refine ⟨14881160327751428760755851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19841547103668571681007801 14881160327751428760755851)
      ·
        refine ⟨22321740491627143141133777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14881160327751428760755851 22321740491627143141133777)
        ·
          refine ⟨16741305368720357355850333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22321740491627143141133777 16741305368720357355850333)
          ·
            refine ⟨6277989513270134008443875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16741305368720357355850333 6277989513270134008443875)
            ·
              refine ⟨9416984269905201012665813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6277989513270134008443875 9416984269905201012665813)
              ·
                refine ⟨220710568825903148734355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 9416984269905201012665813 220710568825903148734355)
                ·
                  refine ⟨331065853238854723101533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220710568825903148734355 331065853238854723101533)
                  ·
                    refine ⟨124149694964570521163075, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331065853238854723101533 124149694964570521163075)
                    ·
                      rfl

theorem cell22_362671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 7, 1, 3].length) (baseStart_362671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362671 prefixEnd_362671 := by exact prefixLift 362671
  have htrace : WordTrace (prefixWord ++ tailWord_362671) baseStart_362671 baseEnd_362671 := by
    simpa [prefixWord, tailWord_362671, baseEnd_362671] using wordTrace_append hprefix tailTrace_362671
  have hstable : (prefixWord ++ tailWord_362671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362671).length < 2 ^ (prefixWord ++ tailWord_362671).sum := by decide
  have hdescent : baseEnd_362671 < baseStart_362671 := by decide
  rcases family_descends (prefixWord ++ tailWord_362671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362688 : List Nat := [2, 1, 1, 2, 5, 2, 1, 4, 1, 3]
def baseStart_362688 : Nat := 118140960795 + 362688 * 2 ^ 59
def prefixEnd_362688 : Nat := 4983230072969 + 3 ^ 40 * 362688 * 2
def baseEnd_362688 : Nat := 124155514411988143488023

theorem tailTrace_362688 : CollatzResearch.WordTrace tailWord_362688 prefixEnd_362688 124155514411988143488023 := by
  unfold tailWord_362688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6614159055025396512020359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8818878740033862016027145 6614159055025396512020359)
  ·
    refine ⟨9921238582538094768030539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6614159055025396512020359 9921238582538094768030539)
    ·
      refine ⟨14881857873807142152045809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9921238582538094768030539 14881857873807142152045809)
      ·
        refine ⟨11161393405355356614034357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14881857873807142152045809 11161393405355356614034357)
        ·
          refine ⟨1046380631752064682565721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11161393405355356614034357 1046380631752064682565721)
          ·
            refine ⟨784785473814048511924291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1046380631752064682565721 784785473814048511924291)
            ·
              refine ⟨1177178210721072767886437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 784785473814048511924291 1177178210721072767886437)
              ·
                refine ⟨220720914510201143978707, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1177178210721072767886437 220720914510201143978707)
                ·
                  refine ⟨331081371765301715968061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220720914510201143978707 331081371765301715968061)
                  ·
                    refine ⟨124155514411988143488023, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331081371765301715968061 124155514411988143488023)
                    ·
                      rfl

theorem cell22_362688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 2, 1, 4, 1, 3].length) (baseStart_362688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362688 prefixEnd_362688 := by exact prefixLift 362688
  have htrace : WordTrace (prefixWord ++ tailWord_362688) baseStart_362688 baseEnd_362688 := by
    simpa [prefixWord, tailWord_362688, baseEnd_362688] using wordTrace_append hprefix tailTrace_362688
  have hstable : (prefixWord ++ tailWord_362688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362688).length < 2 ^ (prefixWord ++ tailWord_362688).sum := by decide
  have hdescent : baseEnd_362688 < baseStart_362688 := by decide
  rcases family_descends (prefixWord ++ tailWord_362688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362714 : List Nat := [3, 1, 1, 2, 2, 1, 4, 1, 3, 4]
def baseStart_362714 : Nat := 118140960795 + 362714 * 2 ^ 59
def prefixEnd_362714 : Nat := 4983230072969 + 3 ^ 40 * 362714 * 2
def baseEnd_362714 : Nat := 124164414743332742337943

theorem tailTrace_362714 : CollatzResearch.WordTrace tailWord_362714 prefixEnd_362714 124164414743332742337943 := by
  unfold tailWord_362714
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307316601989149866121799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8819510938637732976324797 3307316601989149866121799)
  ·
    refine ⟨4960974902983724799182699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307316601989149866121799 4960974902983724799182699)
    ·
      refine ⟨7441462354475587198774049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4960974902983724799182699 7441462354475587198774049)
      ·
        refine ⟨5581096765856690399080537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7441462354475587198774049 5581096765856690399080537)
        ·
          refine ⟨4185822574392517799310403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5581096765856690399080537 4185822574392517799310403)
          ·
            refine ⟨6278733861588776698965605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4185822574392517799310403 6278733861588776698965605)
            ·
              refine ⟨1177262599047895631056051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6278733861588776698965605 1177262599047895631056051)
              ·
                refine ⟨1765893898571843446584077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1177262599047895631056051 1765893898571843446584077)
                ·
                  refine ⟨662210211964441292469029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1765893898571843446584077 662210211964441292469029)
                  ·
                    refine ⟨124164414743332742337943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662210211964441292469029 124164414743332742337943)
                    ·
                      rfl

theorem cell22_362714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 4, 1, 3, 4].length) (baseStart_362714 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362714 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362714 prefixEnd_362714 := by exact prefixLift 362714
  have htrace : WordTrace (prefixWord ++ tailWord_362714) baseStart_362714 baseEnd_362714 := by
    simpa [prefixWord, tailWord_362714, baseEnd_362714] using wordTrace_append hprefix tailTrace_362714
  have hstable : (prefixWord ++ tailWord_362714).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362714).length < 2 ^ (prefixWord ++ tailWord_362714).sum := by decide
  have hdescent : baseEnd_362714 < baseStart_362714 := by decide
  rcases family_descends (prefixWord ++ tailWord_362714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362746 : List Nat := [3, 1, 1, 1, 1, 5, 2, 4, 4]
def baseStart_362746 : Nat := 118140960795 + 362746 * 2 ^ 59
def prefixEnd_362746 : Nat := 4983230072969 + 3 ^ 40 * 362746 * 2
def baseEnd_362746 : Nat := 41391789665765108512615

theorem tailTrace_362746 : CollatzResearch.WordTrace tailWord_362746 prefixEnd_362746 41391789665765108512615 := by
  unfold tailWord_362746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3307608385960167232413023, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8820289029227112619768061 3307608385960167232413023)
  ·
    refine ⟨4961412578940250848619535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3307608385960167232413023 4961412578940250848619535)
    ·
      refine ⟨7442118868410376272929303, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4961412578940250848619535 7442118868410376272929303)
      ·
        refine ⟨11163178302615564409393955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7442118868410376272929303 11163178302615564409393955)
        ·
          refine ⟨16744767453923346614090933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11163178302615564409393955 16744767453923346614090933)
          ·
            refine ⟨1569821948805313745071025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16744767453923346614090933 1569821948805313745071025)
            ·
              refine ⟨1177366461603985308803269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1569821948805313745071025 1177366461603985308803269)
              ·
                refine ⟨220756211550747245400613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1177366461603985308803269 220756211550747245400613)
                ·
                  refine ⟨41391789665765108512615, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220756211550747245400613 41391789665765108512615)
                  ·
                    rfl

theorem cell22_362746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 2, 4, 4].length) (baseStart_362746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362746 prefixEnd_362746 := by exact prefixLift 362746
  have htrace : WordTrace (prefixWord ++ tailWord_362746) baseStart_362746 baseEnd_362746 := by
    simpa [prefixWord, tailWord_362746, baseEnd_362746] using wordTrace_append hprefix tailTrace_362746
  have hstable : (prefixWord ++ tailWord_362746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362746).length < 2 ^ (prefixWord ++ tailWord_362746).sum := by decide
  have hdescent : baseEnd_362746 < baseStart_362746 := by decide
  rcases family_descends (prefixWord ++ tailWord_362746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362761 : List Nat := [1, 2, 1, 1, 3, 6, 1, 1, 1, 5]
def baseStart_362761 : Nat := 118140960795 + 362761 * 2 ^ 59
def prefixEnd_362761 : Nat := 4983230072969 + 3 ^ 40 * 362761 * 2
def baseEnd_362761 : Nat := 124180503803840286412799

theorem tailTrace_362761 : CollatzResearch.WordTrace tailWord_362761 prefixEnd_362761 124180503803840286412799 := by
  unfold tailWord_362761
  simp only [CollatzResearch.WordTrace]
  refine ⟨13230980638786326491448137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8820653759190884327632091 13230980638786326491448137)
  ·
    refine ⟨9923235479089744868586103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13230980638786326491448137 9923235479089744868586103)
    ·
      refine ⟨14884853218634617302879155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9923235479089744868586103 14884853218634617302879155)
      ·
        refine ⟨22327279827951925954318733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14884853218634617302879155 22327279827951925954318733)
        ·
          refine ⟨8372729935481972232869525, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22327279827951925954318733 8372729935481972232869525)
          ·
            refine ⟨392471715725717448415759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8372729935481972232869525 392471715725717448415759)
            ·
              refine ⟨588707573588576172623639, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392471715725717448415759 588707573588576172623639)
              ·
                refine ⟨883061360382864258935459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 588707573588576172623639 883061360382864258935459)
                ·
                  refine ⟨1324592040574296388403189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 883061360382864258935459 1324592040574296388403189)
                  ·
                    refine ⟨124180503803840286412799, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1324592040574296388403189 124180503803840286412799)
                    ·
                      rfl

theorem cell22_362761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 6, 1, 1, 1, 5].length) (baseStart_362761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362761 prefixEnd_362761 := by exact prefixLift 362761
  have htrace : WordTrace (prefixWord ++ tailWord_362761) baseStart_362761 baseEnd_362761 := by
    simpa [prefixWord, tailWord_362761, baseEnd_362761] using wordTrace_append hprefix tailTrace_362761
  have hstable : (prefixWord ++ tailWord_362761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362761).length < 2 ^ (prefixWord ++ tailWord_362761).sum := by decide
  have hdescent : baseEnd_362761 < baseStart_362761 := by decide
  rcases family_descends (prefixWord ++ tailWord_362761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362797 : List Nat := [1, 5, 3, 1, 2, 1, 3, 2, 4]
def baseStart_362797 : Nat := 118140960795 + 362797 * 2 ^ 59
def prefixEnd_362797 : Nat := 4983230072969 + 3 ^ 40 * 362797 * 2
def baseEnd_362797 : Nat := 41397609113182730837563

theorem tailTrace_362797 : CollatzResearch.WordTrace tailWord_362797 prefixEnd_362797 41397609113182730837563 := by
  unfold tailWord_362797
  simp only [CollatzResearch.WordTrace]
  refine ⟨13232293666655904639758645, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8821529111103936426505763 13232293666655904639758645)
  ·
    refine ⟨1240527531248991059977373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13232293666655904639758645 1240527531248991059977373)
    ·
      refine ⟨465197824218371647491515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1240527531248991059977373 465197824218371647491515)
      ·
        refine ⟨697796736327557471237273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 465197824218371647491515 697796736327557471237273)
        ·
          refine ⟨523347552245668103427955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 697796736327557471237273 523347552245668103427955)
          ·
            refine ⟨785021328368502155141933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523347552245668103427955 785021328368502155141933)
            ·
              refine ⟨294382998138188308178225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 785021328368502155141933 294382998138188308178225)
              ·
                refine ⟨220787248603641231133669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 294382998138188308178225 220787248603641231133669)
                ·
                  refine ⟨41397609113182730837563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220787248603641231133669 41397609113182730837563)
                  ·
                    rfl

theorem cell22_362797_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 1, 3, 2, 4].length) (baseStart_362797 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362797 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362797 prefixEnd_362797 := by exact prefixLift 362797
  have htrace : WordTrace (prefixWord ++ tailWord_362797) baseStart_362797 baseEnd_362797 := by
    simpa [prefixWord, tailWord_362797, baseEnd_362797] using wordTrace_append hprefix tailTrace_362797
  have hstable : (prefixWord ++ tailWord_362797).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362797).length < 2 ^ (prefixWord ++ tailWord_362797).sum := by decide
  have hdescent : baseEnd_362797 < baseStart_362797 := by decide
  rcases family_descends (prefixWord ++ tailWord_362797) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362846 : List Nat := [4, 4, 2, 1, 1, 1, 2, 2, 2, 3]
def baseStart_362846 : Nat := 118140960795 + 362846 * 2 ^ 59
def prefixEnd_362846 : Nat := 4983230072969 + 3 ^ 40 * 362846 * 2
def baseEnd_362846 : Nat := 124209601040928398037539

theorem tailTrace_362846 : CollatzResearch.WordTrace tailWord_362846 prefixEnd_362846 124209601040928398037539 := by
  unfold tailWord_362846
  simp only [CollatzResearch.WordTrace]
  refine ⟨1654260105434798251036549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8822720562318924005528261 1654260105434798251036549)
  ·
    refine ⟨310173769769024672069353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1654260105434798251036549 310173769769024672069353)
    ·
      refine ⟨232630327326768504052015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 310173769769024672069353 232630327326768504052015)
      ·
        refine ⟨348945490990152756078023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 232630327326768504052015 348945490990152756078023)
        ·
          refine ⟨523418236485229134117035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 348945490990152756078023 523418236485229134117035)
          ·
            refine ⟨785127354727843701175553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523418236485229134117035 785127354727843701175553)
            ·
              refine ⟨588845516045882775881665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 785127354727843701175553 588845516045882775881665)
              ·
                refine ⟨441634137034412081911249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 588845516045882775881665 441634137034412081911249)
                ·
                  refine ⟨331225602775809061433437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441634137034412081911249 331225602775809061433437)
                  ·
                    refine ⟨124209601040928398037539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331225602775809061433437 124209601040928398037539)
                    ·
                      rfl

theorem cell22_362846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 2, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_362846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362846 prefixEnd_362846 := by exact prefixLift 362846
  have htrace : WordTrace (prefixWord ++ tailWord_362846) baseStart_362846 baseEnd_362846 := by
    simpa [prefixWord, tailWord_362846, baseEnd_362846] using wordTrace_append hprefix tailTrace_362846
  have hstable : (prefixWord ++ tailWord_362846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362846).length < 2 ^ (prefixWord ++ tailWord_362846).sum := by decide
  have hdescent : baseEnd_362846 < baseStart_362846 := by decide
  rcases family_descends (prefixWord ++ tailWord_362846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362866 : List Nat := [3, 2, 1, 2, 1, 3, 1, 2, 3, 4]
def baseStart_362866 : Nat := 118140960795 + 362866 * 2 ^ 59
def prefixEnd_362866 : Nat := 4983230072969 + 3 ^ 40 * 362866 * 2
def baseEnd_362866 : Nat := 124216447449655012537477

theorem tailTrace_362866 : CollatzResearch.WordTrace tailWord_362866 prefixEnd_362866 124216447449655012537477 := by
  unfold tailWord_362866
  simp only [CollatzResearch.WordTrace]
  refine ⟨3308702575851482356005113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8823206868937286282680301 3308702575851482356005113)
  ·
    refine ⟨2481526931888611767003835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3308702575851482356005113 2481526931888611767003835)
    ·
      refine ⟨3722290397832917650505753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481526931888611767003835 3722290397832917650505753)
      ·
        refine ⟨2791717798374688237879315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3722290397832917650505753 2791717798374688237879315)
        ·
          refine ⟨4187576697562032356818973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2791717798374688237879315 4187576697562032356818973)
          ·
            refine ⟨1570341261585762133807115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4187576697562032356818973 1570341261585762133807115)
            ·
              refine ⟨2355511892378643200710673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570341261585762133807115 2355511892378643200710673)
              ·
                refine ⟨1766633919283982400533005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2355511892378643200710673 1766633919283982400533005)
                ·
                  refine ⟨662487719731493400199877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1766633919283982400533005 662487719731493400199877)
                  ·
                    refine ⟨124216447449655012537477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662487719731493400199877 124216447449655012537477)
                    ·
                      rfl

theorem cell22_362866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 3, 1, 2, 3, 4].length) (baseStart_362866 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362866 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362866 prefixEnd_362866 := by exact prefixLift 362866
  have htrace : WordTrace (prefixWord ++ tailWord_362866) baseStart_362866 baseEnd_362866 := by
    simpa [prefixWord, tailWord_362866, baseEnd_362866] using wordTrace_append hprefix tailTrace_362866
  have hstable : (prefixWord ++ tailWord_362866).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362866).length < 2 ^ (prefixWord ++ tailWord_362866).sum := by decide
  have hdescent : baseEnd_362866 < baseStart_362866 := by decide
  rcases family_descends (prefixWord ++ tailWord_362866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362879 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 5, 5]
def baseStart_362879 : Nat := 118140960795 + 362879 * 2 ^ 59
def prefixEnd_362879 : Nat := 4983230072969 + 3 ^ 40 * 362879 * 2
def baseEnd_362879 : Nat := 124220897615327311962437

theorem tailTrace_362879 : CollatzResearch.WordTrace tailWord_362879 prefixEnd_362879 124220897615327311962437 := by
  unfold tailWord_362879
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235284452358832644243691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8823522968239221762829127 13235284452358832644243691)
  ·
    refine ⟨19852926678538248966365537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13235284452358832644243691 19852926678538248966365537)
    ·
      refine ⟨14889695008903686724774153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19852926678538248966365537 14889695008903686724774153)
      ·
        refine ⟨11167271256677765043580615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14889695008903686724774153 11167271256677765043580615)
        ·
          refine ⟨16750906885016647565370923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11167271256677765043580615 16750906885016647565370923)
          ·
            refine ⟨25126360327524971348056385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16750906885016647565370923 25126360327524971348056385)
            ·
              refine ⟨18844770245643728511042289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25126360327524971348056385 18844770245643728511042289)
              ·
                refine ⟨14133577684232796383281717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18844770245643728511042289 14133577684232796383281717)
                ·
                  refine ⟨1325022907896824660932661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 14133577684232796383281717 1325022907896824660932661)
                  ·
                    refine ⟨124220897615327311962437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1325022907896824660932661 124220897615327311962437)
                    ·
                      rfl

theorem cell22_362879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 5, 5].length) (baseStart_362879 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362879 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362879 prefixEnd_362879 := by exact prefixLift 362879
  have htrace : WordTrace (prefixWord ++ tailWord_362879) baseStart_362879 baseEnd_362879 := by
    simpa [prefixWord, tailWord_362879, baseEnd_362879] using wordTrace_append hprefix tailTrace_362879
  have hstable : (prefixWord ++ tailWord_362879).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362879).length < 2 ^ (prefixWord ++ tailWord_362879).sum := by decide
  have hdescent : baseEnd_362879 < baseStart_362879 := by decide
  rcases family_descends (prefixWord ++ tailWord_362879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362881 : List Nat := [1, 2, 4, 3, 1, 1, 1, 1, 8]
def baseStart_362881 : Nat := 118140960795 + 362881 * 2 ^ 59
def prefixEnd_362881 : Nat := 4983230072969 + 3 ^ 40 * 362881 * 2
def baseEnd_362881 : Nat := 41407194085399991137477

theorem tailTrace_362881 : CollatzResearch.WordTrace tailWord_362881 prefixEnd_362881 41407194085399991137477 := by
  unfold tailWord_362881
  simp only [CollatzResearch.WordTrace]
  refine ⟨13235357398351586985816497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8823571598901057990544331 13235357398351586985816497)
  ·
    refine ⟨9926518048763690239362373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13235357398351586985816497 9926518048763690239362373)
    ·
      refine ⟨1861222134143191919880445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9926518048763690239362373 1861222134143191919880445)
      ·
        refine ⟨697958300303696969955167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1861222134143191919880445 697958300303696969955167)
        ·
          refine ⟨1046937450455545454932751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 697958300303696969955167 1046937450455545454932751)
          ·
            refine ⟨1570406175683318182399127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1046937450455545454932751 1570406175683318182399127)
            ·
              refine ⟨2355609263524977273598691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1570406175683318182399127 2355609263524977273598691)
              ·
                refine ⟨3533413895287465910398037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355609263524977273598691 3533413895287465910398037)
                ·
                  refine ⟨41407194085399991137477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3533413895287465910398037 41407194085399991137477)
                  ·
                    rfl

theorem cell22_362881_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 1, 1, 1, 8].length) (baseStart_362881 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362881 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362881 prefixEnd_362881 := by exact prefixLift 362881
  have htrace : WordTrace (prefixWord ++ tailWord_362881) baseStart_362881 baseEnd_362881 := by
    simpa [prefixWord, tailWord_362881, baseEnd_362881] using wordTrace_append hprefix tailTrace_362881
  have hstable : (prefixWord ++ tailWord_362881).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362881).length < 2 ^ (prefixWord ++ tailWord_362881).sum := by decide
  have hdescent : baseEnd_362881 < baseStart_362881 := by decide
  rcases family_descends (prefixWord ++ tailWord_362881) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362900 : List Nat := [2, 4, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_362900 : Nat := 118140960795 + 362900 * 2 ^ 59
def prefixEnd_362900 : Nat := 4983230072969 + 3 ^ 40 * 362900 * 2
def baseEnd_362900 : Nat := 124228086344490257187373

theorem tailTrace_362900 : CollatzResearch.WordTrace tailWord_362900 prefixEnd_362900 124228086344490257187373 := by
  unfold tailWord_362900
  simp only [CollatzResearch.WordTrace]
  refine ⟨6618025192641376615379077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8824033590188502153838769 6618025192641376615379077)
  ·
    refine ⟨1240879723620258115383577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6618025192641376615379077 1240879723620258115383577)
    ·
      refine ⟨930659792715193586537683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1240879723620258115383577 930659792715193586537683)
      ·
        refine ⟨1395989689072790379806525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 930659792715193586537683 1395989689072790379806525)
        ·
          refine ⟨523496133402296392427447, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1395989689072790379806525 523496133402296392427447)
          ·
            refine ⟨785244200103444588641171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 523496133402296392427447 785244200103444588641171)
            ·
              refine ⟨1177866300155166882961757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 785244200103444588641171 1177866300155166882961757)
              ·
                refine ⟨441699862558187581110659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1177866300155166882961757 441699862558187581110659)
                ·
                  refine ⟨662549793837281371665989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 441699862558187581110659 662549793837281371665989)
                  ·
                    refine ⟨124228086344490257187373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662549793837281371665989 124228086344490257187373)
                    ·
                      rfl

theorem cell22_362900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_362900 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362900 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362900 prefixEnd_362900 := by exact prefixLift 362900
  have htrace : WordTrace (prefixWord ++ tailWord_362900) baseStart_362900 baseEnd_362900 := by
    simpa [prefixWord, tailWord_362900, baseEnd_362900] using wordTrace_append hprefix tailTrace_362900
  have hstable : (prefixWord ++ tailWord_362900).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362900).length < 2 ^ (prefixWord ++ tailWord_362900).sum := by decide
  have hdescent : baseEnd_362900 < baseStart_362900 := by decide
  rcases family_descends (prefixWord ++ tailWord_362900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362911 : List Nat := [1, 1, 2, 5, 1, 1, 2, 1, 4, 4]
def baseStart_362911 : Nat := 118140960795 + 362911 * 2 ^ 59
def prefixEnd_362911 : Nat := 4983230072969 + 3 ^ 40 * 362911 * 2
def baseEnd_362911 : Nat := 124231851869289895162339

theorem tailTrace_362911 : CollatzResearch.WordTrace tailWord_362911 prefixEnd_362911 124231851869289895162339 := by
  unfold tailWord_362911
  simp only [CollatzResearch.WordTrace]
  refine ⟨13236451588242902109408587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8824301058828601406272391 13236451588242902109408587)
  ·
    refine ⟨19854677382364353164112881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13236451588242902109408587 19854677382364353164112881)
    ·
      refine ⟨14891008036773264873084661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19854677382364353164112881 14891008036773264873084661)
      ·
        refine ⟨1396032003447493581851687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14891008036773264873084661 1396032003447493581851687)
        ·
          refine ⟨2094048005171240372777531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1396032003447493581851687 2094048005171240372777531)
          ·
            refine ⟨3141072007756860559166297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2094048005171240372777531 3141072007756860559166297)
            ·
              refine ⟨2355804005817645419374723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3141072007756860559166297 2355804005817645419374723)
              ·
                refine ⟨3533706008726468129062085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2355804005817645419374723 3533706008726468129062085)
                ·
                  refine ⟨662569876636212774199141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3533706008726468129062085 662569876636212774199141)
                  ·
                    refine ⟨124231851869289895162339, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 662569876636212774199141 124231851869289895162339)
                    ·
                      rfl

theorem cell22_362911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 1, 2, 1, 4, 4].length) (baseStart_362911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362911 prefixEnd_362911 := by exact prefixLift 362911
  have htrace : WordTrace (prefixWord ++ tailWord_362911) baseStart_362911 baseEnd_362911 := by
    simpa [prefixWord, tailWord_362911, baseEnd_362911] using wordTrace_append hprefix tailTrace_362911
  have hstable : (prefixWord ++ tailWord_362911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362911).length < 2 ^ (prefixWord ++ tailWord_362911).sum := by decide
  have hdescent : baseEnd_362911 < baseStart_362911 := by decide
  rcases family_descends (prefixWord ++ tailWord_362911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362930 : List Nat := [3, 2, 1, 1, 1, 1, 7, 1, 2, 3]
def baseStart_362930 : Nat := 118140960795 + 362930 * 2 ^ 59
def prefixEnd_362930 : Nat := 4983230072969 + 3 ^ 40 * 362930 * 2
def baseEnd_362930 : Nat := 124238355957580178937281

theorem tailTrace_362930 : CollatzResearch.WordTrace tailWord_362930 prefixEnd_362930 124238355957580178937281 := by
  unfold tailWord_362930
  simp only [CollatzResearch.WordTrace]
  refine ⟨3309286143793517088587561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8824763050116045569566829 3309286143793517088587561)
  ·
    refine ⟨2481964607845137816440671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3309286143793517088587561 2481964607845137816440671)
    ·
      refine ⟨3722946911767706724661007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2481964607845137816440671 3722946911767706724661007)
      ·
        refine ⟨5584420367651560086991511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3722946911767706724661007 5584420367651560086991511)
        ·
          refine ⟨8376630551477340130487267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5584420367651560086991511 8376630551477340130487267)
          ·
            refine ⟨12564945827216010195730901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8376630551477340130487267 12564945827216010195730901)
            ·
              refine ⟨294490917825375238962443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 12564945827216010195730901 294490917825375238962443)
              ·
                refine ⟨441736376738062858443665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294490917825375238962443 441736376738062858443665)
                ·
                  refine ⟨331302282553547143832749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441736376738062858443665 331302282553547143832749)
                  ·
                    refine ⟨124238355957580178937281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331302282553547143832749 124238355957580178937281)
                    ·
                      rfl

theorem cell22_362930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 7, 1, 2, 3].length) (baseStart_362930 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362930 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362930 prefixEnd_362930 := by exact prefixLift 362930
  have htrace : WordTrace (prefixWord ++ tailWord_362930) baseStart_362930 baseEnd_362930 := by
    simpa [prefixWord, tailWord_362930, baseEnd_362930] using wordTrace_append hprefix tailTrace_362930
  have hstable : (prefixWord ++ tailWord_362930).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362930).length < 2 ^ (prefixWord ++ tailWord_362930).sum := by decide
  have hdescent : baseEnd_362930 < baseStart_362930 := by decide
  rcases family_descends (prefixWord ++ tailWord_362930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_362975 : List Nat := [1, 1, 2, 3, 3, 4, 1, 1, 3, 3]
def baseStart_362975 : Nat := 118140960795 + 362975 * 2 ^ 59
def prefixEnd_362975 : Nat := 4983230072969 + 3 ^ 40 * 362975 * 2
def baseEnd_362975 : Nat := 124253760377215061562143

theorem tailTrace_362975 : CollatzResearch.WordTrace tailWord_362975 prefixEnd_362975 124253760377215061562143 := by
  unfold tailWord_362975
  simp only [CollatzResearch.WordTrace]
  refine ⟨13238785860011041039738379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8825857240007360693158919 13238785860011041039738379)
  ·
    refine ⟨19858178790016561559607569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13238785860011041039738379 19858178790016561559607569)
    ·
      refine ⟨14893634092512421169705677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19858178790016561559607569 14893634092512421169705677)
      ·
        refine ⟨5585112784692157938639629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14893634092512421169705677 5585112784692157938639629)
        ·
          refine ⟨2094417294259559226989861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5585112784692157938639629 2094417294259559226989861)
          ·
            refine ⟨392703242673667355060599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2094417294259559226989861 392703242673667355060599)
            ·
              refine ⟨589054864010501032590899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392703242673667355060599 589054864010501032590899)
              ·
                refine ⟨883582296015751548886349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589054864010501032590899 883582296015751548886349)
                ·
                  refine ⟨331343361005906830832381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 883582296015751548886349 331343361005906830832381)
                  ·
                    refine ⟨124253760377215061562143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331343361005906830832381 124253760377215061562143)
                    ·
                      rfl

theorem cell22_362975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 4, 1, 1, 3, 3].length) (baseStart_362975 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_362975 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_362975 prefixEnd_362975 := by exact prefixLift 362975
  have htrace : WordTrace (prefixWord ++ tailWord_362975) baseStart_362975 baseEnd_362975 := by
    simpa [prefixWord, tailWord_362975, baseEnd_362975] using wordTrace_append hprefix tailTrace_362975
  have hstable : (prefixWord ++ tailWord_362975).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_362975).length < 2 ^ (prefixWord ++ tailWord_362975).sum := by decide
  have hdescent : baseEnd_362975 < baseStart_362975 := by decide
  rcases family_descends (prefixWord ++ tailWord_362975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363033 : List Nat := [1, 2, 1, 2, 1, 1, 2, 8, 4]
def baseStart_363033 : Nat := 118140960795 + 363033 * 2 ^ 59
def prefixEnd_363033 : Nat := 4983230072969 + 3 ^ 40 * 363033 * 2
def baseEnd_363033 : Nat := 41424538320840747870655

theorem tailTrace_363033 : CollatzResearch.WordTrace tailWord_363033 prefixEnd_363033 41424538320840747870655 := by
  unfold tailWord_363033
  simp only [CollatzResearch.WordTrace]
  refine ⟨13240901293800916945349753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8827267529200611296899835 13240901293800916945349753)
  ·
    refine ⟨9930675970350687709012315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13240901293800916945349753 9930675970350687709012315)
    ·
      refine ⟨14896013955526031563518473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9930675970350687709012315 14896013955526031563518473)
      ·
        refine ⟨11172010466644523672638855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14896013955526031563518473 11172010466644523672638855)
        ·
          refine ⟨16758015699966785508958283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11172010466644523672638855 16758015699966785508958283)
          ·
            refine ⟨25137023549950178263437425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16758015699966785508958283 25137023549950178263437425)
            ·
              refine ⟨18852767662462633697578069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25137023549950178263437425 18852767662462633697578069)
              ·
                refine ⟨220930871044483988643493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 18852767662462633697578069 220930871044483988643493)
                ·
                  refine ⟨41424538320840747870655, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 220930871044483988643493 41424538320840747870655)
                  ·
                    rfl

theorem cell22_363033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 1, 2, 8, 4].length) (baseStart_363033 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363033 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363033 prefixEnd_363033 := by exact prefixLift 363033
  have htrace : WordTrace (prefixWord ++ tailWord_363033) baseStart_363033 baseEnd_363033 := by
    simpa [prefixWord, tailWord_363033, baseEnd_363033] using wordTrace_append hprefix tailTrace_363033
  have hstable : (prefixWord ++ tailWord_363033).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363033).length < 2 ^ (prefixWord ++ tailWord_363033).sum := by decide
  have hdescent : baseEnd_363033 < baseStart_363033 := by decide
  rcases family_descends (prefixWord ++ tailWord_363033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363082 : List Nat := [3, 1, 2, 1, 1, 6, 1, 2, 2, 3]
def baseStart_363082 : Nat := 118140960795 + 363082 * 2 ^ 59
def prefixEnd_363082 : Nat := 4983230072969 + 3 ^ 40 * 363082 * 2
def baseEnd_363082 : Nat := 124290388663902449136815

theorem tailTrace_363082 : CollatzResearch.WordTrace tailWord_363082 prefixEnd_363082 124290388663902449136815 := by
  unfold tailWord_363082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3310672117655849578470875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8828458980415598875922333 3310672117655849578470875)
  ·
    refine ⟨4966008176483774367706313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3310672117655849578470875 4966008176483774367706313)
    ·
      refine ⟨3724506132362830775779735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4966008176483774367706313 3724506132362830775779735)
      ·
        refine ⟨5586759198544246163669603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3724506132362830775779735 5586759198544246163669603)
        ·
          refine ⟨8380138797816369245504405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5586759198544246163669603 8380138797816369245504405)
          ·
            refine ⟨392819006147642308383019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8380138797816369245504405 392819006147642308383019)
            ·
              refine ⟨589228509221463462574529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 392819006147642308383019 589228509221463462574529)
              ·
                refine ⟨441921381916097596930897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589228509221463462574529 441921381916097596930897)
                ·
                  refine ⟨331441036437073197698173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 441921381916097596930897 331441036437073197698173)
                  ·
                    refine ⟨124290388663902449136815, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331441036437073197698173 124290388663902449136815)
                    ·
                      rfl

theorem cell22_363082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 6, 1, 2, 2, 3].length) (baseStart_363082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363082 prefixEnd_363082 := by exact prefixLift 363082
  have htrace : WordTrace (prefixWord ++ tailWord_363082) baseStart_363082 baseEnd_363082 := by
    simpa [prefixWord, tailWord_363082, baseEnd_363082] using wordTrace_append hprefix tailTrace_363082
  have hstable : (prefixWord ++ tailWord_363082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363082).length < 2 ^ (prefixWord ++ tailWord_363082).sum := by decide
  have hdescent : baseEnd_363082 < baseStart_363082 := by decide
  rcases family_descends (prefixWord ++ tailWord_363082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363112 : List Nat := [2, 1, 4, 3, 2, 2, 2, 6]
def baseStart_363112 : Nat := 118140960795 + 363112 * 2 ^ 59
def prefixEnd_363112 : Nat := 4983230072969 + 3 ^ 40 * 363112 * 2
def baseEnd_363112 : Nat := 13811184252999152320747

theorem tailTrace_363112 : CollatzResearch.WordTrace tailWord_363112 prefixEnd_363112 13811184252999152320747 := by
  unfold tailWord_363112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6621891330257356718737795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8829188440343142291650393 6621891330257356718737795)
  ·
    refine ⟨9932836995386035078106693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6621891330257356718737795 9932836995386035078106693)
    ·
      refine ⟨1862406936634881577145005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9932836995386035078106693 1862406936634881577145005)
      ·
        refine ⟨698402601238080591429377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1862406936634881577145005 698402601238080591429377)
        ·
          refine ⟨523801950928560443572033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 698402601238080591429377 523801950928560443572033)
          ·
            refine ⟨392851463196420332679025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 523801950928560443572033 392851463196420332679025)
            ·
              refine ⟨294638597397315249509269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 392851463196420332679025 294638597397315249509269)
              ·
                refine ⟨13811184252999152320747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 294638597397315249509269 13811184252999152320747)
                ·
                  rfl

theorem cell22_363112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 2, 2, 2, 6].length) (baseStart_363112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363112 prefixEnd_363112 := by exact prefixLift 363112
  have htrace : WordTrace (prefixWord ++ tailWord_363112) baseStart_363112 baseEnd_363112 := by
    simpa [prefixWord, tailWord_363112, baseEnd_363112] using wordTrace_append hprefix tailTrace_363112
  have hstable : (prefixWord ++ tailWord_363112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363112).length < 2 ^ (prefixWord ++ tailWord_363112).sum := by decide
  have hdescent : baseEnd_363112 < baseStart_363112 := by decide
  rcases family_descends (prefixWord ++ tailWord_363112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363127 : List Nat := [1, 1, 3, 1, 1, 3, 5, 3, 1, 3]
def baseStart_363127 : Nat := 118140960795 + 363127 * 2 ^ 59
def prefixEnd_363127 : Nat := 4983230072969 + 3 ^ 40 * 363127 * 2
def baseEnd_363127 : Nat := 124305793083537331761677

theorem tailTrace_363127 : CollatzResearch.WordTrace tailWord_363127 prefixEnd_363127 124305793083537331761677 := by
  unfold tailWord_363127
  simp only [CollatzResearch.WordTrace]
  refine ⟨13244329755460370999271635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8829553170306913999514423 13244329755460370999271635)
  ·
    refine ⟨19866494633190556498907453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13244329755460370999271635 19866494633190556498907453)
    ·
      refine ⟨7449935487446458687090295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19866494633190556498907453 7449935487446458687090295)
      ·
        refine ⟨11174903231169688030635443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7449935487446458687090295 11174903231169688030635443)
        ·
          refine ⟨16762354846754532045953165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11174903231169688030635443 16762354846754532045953165)
          ·
            refine ⟨6285883067532949517232437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16762354846754532045953165 6285883067532949517232437)
            ·
              refine ⟨589301537581214017240541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6285883067532949517232437 589301537581214017240541)
              ·
                refine ⟨220988076592955256465203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589301537581214017240541 220988076592955256465203)
                ·
                  refine ⟨331482114889432884697805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 220988076592955256465203 331482114889432884697805)
                  ·
                    refine ⟨124305793083537331761677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331482114889432884697805 124305793083537331761677)
                    ·
                      rfl

theorem cell22_363127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 5, 3, 1, 3].length) (baseStart_363127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363127 prefixEnd_363127 := by exact prefixLift 363127
  have htrace : WordTrace (prefixWord ++ tailWord_363127) baseStart_363127 baseEnd_363127 := by
    simpa [prefixWord, tailWord_363127, baseEnd_363127] using wordTrace_append hprefix tailTrace_363127
  have hstable : (prefixWord ++ tailWord_363127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363127).length < 2 ^ (prefixWord ++ tailWord_363127).sum := by decide
  have hdescent : baseEnd_363127 < baseStart_363127 := by decide
  rcases family_descends (prefixWord ++ tailWord_363127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363183 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 3, 5]
def baseStart_363183 : Nat := 118140960795 + 363183 * 2 ^ 59
def prefixEnd_363183 : Nat := 4983230072969 + 3 ^ 40 * 363183 * 2
def baseEnd_363183 : Nat := 124324963027971852361505

theorem tailTrace_363183 : CollatzResearch.WordTrace tailWord_363183 prefixEnd_363183 124324963027971852361505 := by
  unfold tailWord_363183
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246372243257492563310203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8830914828838328375540135 13246372243257492563310203)
  ·
    refine ⟨19869558364886238844965305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13246372243257492563310203 19869558364886238844965305)
    ·
      refine ⟨14902168773664679133723979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19869558364886238844965305 14902168773664679133723979)
      ·
        refine ⟨22353253160497018700585969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14902168773664679133723979 22353253160497018700585969)
        ·
          refine ⟨16764939870372764025439477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22353253160497018700585969 16764939870372764025439477)
          ·
            refine ⟨1571713112847446627384951, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16764939870372764025439477 1571713112847446627384951)
            ·
              refine ⟨2357569669271169941077427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1571713112847446627384951 2357569669271169941077427)
              ·
                refine ⟨3536354503906754911616141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2357569669271169941077427 3536354503906754911616141)
                ·
                  refine ⟨1326132938965033091856053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3536354503906754911616141 1326132938965033091856053)
                  ·
                    refine ⟨124324963027971852361505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1326132938965033091856053 124324963027971852361505)
                    ·
                      rfl

theorem cell22_363183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 3, 5].length) (baseStart_363183 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363183 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363183 prefixEnd_363183 := by exact prefixLift 363183
  have htrace : WordTrace (prefixWord ++ tailWord_363183) baseStart_363183 baseEnd_363183 := by
    simpa [prefixWord, tailWord_363183, baseEnd_363183] using wordTrace_append hprefix tailTrace_363183
  have hstable : (prefixWord ++ tailWord_363183).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363183).length < 2 ^ (prefixWord ++ tailWord_363183).sum := by decide
  have hdescent : baseEnd_363183 < baseStart_363183 := by decide
  rcases family_descends (prefixWord ++ tailWord_363183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363187 : List Nat := [1, 1, 1, 2, 3, 5, 3, 1, 1, 4]
def baseStart_363187 : Nat := 118140960795 + 363187 * 2 ^ 59
def prefixEnd_363187 : Nat := 4983230072969 + 3 ^ 40 * 363187 * 2
def baseEnd_363187 : Nat := 124326332309717175261493

theorem tailTrace_363187 : CollatzResearch.WordTrace tailWord_363187 prefixEnd_363187 124326332309717175261493 := by
  unfold tailWord_363187
  simp only [CollatzResearch.WordTrace]
  refine ⟨13246518135243001246455815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8831012090162000830970543 13246518135243001246455815)
  ·
    refine ⟨19869777202864501869683723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13246518135243001246455815 19869777202864501869683723)
    ·
      refine ⟨29804665804296752804525585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19869777202864501869683723 29804665804296752804525585)
      ·
        refine ⟨22353499353222564603394189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 29804665804296752804525585 22353499353222564603394189)
        ·
          refine ⟨8382562257458461726272821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22353499353222564603394189 8382562257458461726272821)
          ·
            refine ⟨785865211636730786838077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8382562257458461726272821 785865211636730786838077)
            ·
              refine ⟨294699454363774045064279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 785865211636730786838077 294699454363774045064279)
              ·
                refine ⟨442049181545661067596419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294699454363774045064279 442049181545661067596419)
                ·
                  refine ⟨663073772318491601394629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442049181545661067596419 663073772318491601394629)
                  ·
                    refine ⟨124326332309717175261493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663073772318491601394629 124326332309717175261493)
                    ·
                      rfl

theorem cell22_363187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 5, 3, 1, 1, 4].length) (baseStart_363187 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363187 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363187 prefixEnd_363187 := by exact prefixLift 363187
  have htrace : WordTrace (prefixWord ++ tailWord_363187) baseStart_363187 baseEnd_363187 := by
    simpa [prefixWord, tailWord_363187, baseEnd_363187] using wordTrace_append hprefix tailTrace_363187
  have hstable : (prefixWord ++ tailWord_363187).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363187).length < 2 ^ (prefixWord ++ tailWord_363187).sum := by decide
  have hdescent : baseEnd_363187 < baseStart_363187 := by decide
  rcases family_descends (prefixWord ++ tailWord_363187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363296 : List Nat := [2, 1, 1, 5, 1, 4, 1, 3, 1, 3]
def baseStart_363296 : Nat := 118140960795 + 363296 * 2 ^ 59
def prefixEnd_363296 : Nat := 4983230072969 + 3 ^ 40 * 363296 * 2
def baseEnd_363296 : Nat := 124363645237277224286159

theorem tailTrace_363296 : CollatzResearch.WordTrace tailWord_363296 prefixEnd_363296 124363645237277224286159 := by
  unfold tailWord_363296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6625246845924056431086871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8833662461232075241449161 6625246845924056431086871)
  ·
    refine ⟨9937870268886084646630307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6625246845924056431086871 9937870268886084646630307)
    ·
      refine ⟨14906805403329126969945461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9937870268886084646630307 14906805403329126969945461)
      ·
        refine ⟨1397513006562105653432387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14906805403329126969945461 1397513006562105653432387)
        ·
          refine ⟨2096269509843158480148581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1397513006562105653432387 2096269509843158480148581)
          ·
            refine ⟨393050533095592215027859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2096269509843158480148581 393050533095592215027859)
            ·
              refine ⟨589575799643388322541789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393050533095592215027859 589575799643388322541789)
              ·
                refine ⟨221090924866270620953171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 589575799643388322541789 221090924866270620953171)
                ·
                  refine ⟨331636387299405931429757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221090924866270620953171 331636387299405931429757)
                  ·
                    refine ⟨124363645237277224286159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331636387299405931429757 124363645237277224286159)
                    ·
                      rfl

theorem cell22_363296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 5, 1, 4, 1, 3, 1, 3].length) (baseStart_363296 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363296 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363296 prefixEnd_363296 := by exact prefixLift 363296
  have htrace : WordTrace (prefixWord ++ tailWord_363296) baseStart_363296 baseEnd_363296 := by
    simpa [prefixWord, tailWord_363296, baseEnd_363296] using wordTrace_append hprefix tailTrace_363296
  have hstable : (prefixWord ++ tailWord_363296).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363296).length < 2 ^ (prefixWord ++ tailWord_363296).sum := by decide
  have hdescent : baseEnd_363296 < baseStart_363296 := by decide
  rcases family_descends (prefixWord ++ tailWord_363296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363326 : List Nat := [4, 2, 1, 2, 3, 2, 2, 1, 5]
def baseStart_363326 : Nat := 118140960795 + 363326 * 2 ^ 59
def prefixEnd_363326 : Nat := 4983230072969 + 3 ^ 40 * 363326 * 2
def baseEnd_363326 : Nat := 41457971616789048678689

theorem tailTrace_363326 : CollatzResearch.WordTrace tailWord_363326 prefixEnd_363326 41457971616789048678689 := by
  unfold tailWord_363326
  simp only [CollatzResearch.WordTrace]
  refine ⟨1656448485217428498220729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8834391921159618657177221 1656448485217428498220729)
  ·
    refine ⟨1242336363913071373665547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1656448485217428498220729 1242336363913071373665547)
    ·
      refine ⟨1863504545869607060498321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1242336363913071373665547 1863504545869607060498321)
      ·
        refine ⟨1397628409402205295373741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1863504545869607060498321 1397628409402205295373741)
        ·
          refine ⟨524110653525826985765153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1397628409402205295373741 524110653525826985765153)
          ·
            refine ⟨393082990144370239323865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 524110653525826985765153 393082990144370239323865)
            ·
              refine ⟨294812242608277679492899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393082990144370239323865 294812242608277679492899)
              ·
                refine ⟨442218363912416519239349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294812242608277679492899 442218363912416519239349)
                ·
                  refine ⟨41457971616789048678689, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442218363912416519239349 41457971616789048678689)
                  ·
                    rfl

theorem cell22_363326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 2, 2, 1, 5].length) (baseStart_363326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363326 prefixEnd_363326 := by exact prefixLift 363326
  have htrace : WordTrace (prefixWord ++ tailWord_363326) baseStart_363326 baseEnd_363326 := by
    simpa [prefixWord, tailWord_363326, baseEnd_363326] using wordTrace_append hprefix tailTrace_363326
  have hstable : (prefixWord ++ tailWord_363326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363326).length < 2 ^ (prefixWord ++ tailWord_363326).sum := by decide
  have hdescent : baseEnd_363326 < baseStart_363326 := by decide
  rcases family_descends (prefixWord ++ tailWord_363326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363335 : List Nat := [1, 1, 4, 1, 2, 1, 1, 5, 1, 5]
def baseStart_363335 : Nat := 118140960795 + 363335 * 2 ^ 59
def prefixEnd_363335 : Nat := 4983230072969 + 3 ^ 40 * 363335 * 2
def baseEnd_363335 : Nat := 124376995734294122561039

theorem tailTrace_363335 : CollatzResearch.WordTrace tailWord_363335 prefixEnd_363335 124376995734294122561039 := by
  unfold tailWord_363335
  simp only [CollatzResearch.WordTrace]
  refine ⟨13251916138706822522843459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8834610759137881681895639 13251916138706822522843459)
  ·
    refine ⟨19877874208060233784265189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13251916138706822522843459 19877874208060233784265189)
    ·
      refine ⟨3727101414011293834549723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19877874208060233784265189 3727101414011293834549723)
      ·
        refine ⟨5590652121016940751824585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3727101414011293834549723 5590652121016940751824585)
        ·
          refine ⟨4192989090762705563868439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5590652121016940751824585 4192989090762705563868439)
          ·
            refine ⟨6289483636144058345802659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4192989090762705563868439 6289483636144058345802659)
            ·
              refine ⟨9434225454216087518703989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6289483636144058345802659 9434225454216087518703989)
              ·
                refine ⟨884458636332758204878499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 9434225454216087518703989 884458636332758204878499)
                ·
                  refine ⟨1326687954499137307317749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 884458636332758204878499 1326687954499137307317749)
                  ·
                    refine ⟨124376995734294122561039, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1326687954499137307317749 124376995734294122561039)
                    ·
                      rfl

theorem cell22_363335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_363335 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363335 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363335 prefixEnd_363335 := by exact prefixLift 363335
  have htrace : WordTrace (prefixWord ++ tailWord_363335) baseStart_363335 baseEnd_363335 := by
    simpa [prefixWord, tailWord_363335, baseEnd_363335] using wordTrace_append hprefix tailTrace_363335
  have hstable : (prefixWord ++ tailWord_363335).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363335).length < 2 ^ (prefixWord ++ tailWord_363335).sum := by decide
  have hdescent : baseEnd_363335 < baseStart_363335 := by decide
  rcases family_descends (prefixWord ++ tailWord_363335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363356 : List Nat := [2, 2, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_363356 : Nat := 118140960795 + 363356 * 2 ^ 59
def prefixEnd_363356 : Nat := 4983230072969 + 3 ^ 40 * 363356 * 2
def baseEnd_363356 : Nat := 124384184463457067785975

theorem tailTrace_363356 : CollatzResearch.WordTrace tailWord_363356 prefixEnd_363356 124384184463457067785975 := by
  unfold tailWord_363356
  simp only [CollatzResearch.WordTrace]
  refine ⟨6626341035815371554678961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8835121381087162072905281 6626341035815371554678961)
  ·
    refine ⟨4969755776861528666009221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6626341035815371554678961 4969755776861528666009221)
    ·
      refine ⟨931829208161536624876729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4969755776861528666009221 931829208161536624876729)
      ·
        refine ⟨698871906121152468657547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 931829208161536624876729 698871906121152468657547)
        ·
          refine ⟨1048307859181728702986321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 698871906121152468657547 1048307859181728702986321)
          ·
            refine ⟨786230894386296527239741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1048307859181728702986321 786230894386296527239741)
            ·
              refine ⟨294836585394861197714903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 786230894386296527239741 294836585394861197714903)
              ·
                refine ⟨442254878092291796572355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 294836585394861197714903 442254878092291796572355)
                ·
                  refine ⟨663382317138437694858533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442254878092291796572355 663382317138437694858533)
                  ·
                    refine ⟨124384184463457067785975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663382317138437694858533 124384184463457067785975)
                    ·
                      rfl

theorem cell22_363356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_363356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363356 prefixEnd_363356 := by exact prefixLift 363356
  have htrace : WordTrace (prefixWord ++ tailWord_363356) baseStart_363356 baseEnd_363356 := by
    simpa [prefixWord, tailWord_363356, baseEnd_363356] using wordTrace_append hprefix tailTrace_363356
  have hstable : (prefixWord ++ tailWord_363356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363356).length < 2 ^ (prefixWord ++ tailWord_363356).sum := by decide
  have hdescent : baseEnd_363356 < baseStart_363356 := by decide
  rcases family_descends (prefixWord ++ tailWord_363356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363367 : List Nat := [1, 1, 5, 1, 2, 2, 2, 2, 2, 4]
def baseStart_363367 : Nat := 118140960795 + 363367 * 2 ^ 59
def prefixEnd_363367 : Nat := 4983230072969 + 3 ^ 40 * 363367 * 2
def baseEnd_363367 : Nat := 124387949988256705760941

theorem tailTrace_363367 : CollatzResearch.WordTrace tailWord_363367 prefixEnd_363367 124387949988256705760941 := by
  unfold tailWord_363367
  simp only [CollatzResearch.WordTrace]
  refine ⟨13253083274590891988008355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8835388849727261325338903 13253083274590891988008355)
  ·
    refine ⟨19879624911886337982012533, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13253083274590891988008355 19879624911886337982012533)
    ·
      refine ⟨1863714835489344185813675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19879624911886337982012533 1863714835489344185813675)
      ·
        refine ⟨2795572253234016278720513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1863714835489344185813675 2795572253234016278720513)
        ·
          refine ⟨2096679189925512209040385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2795572253234016278720513 2096679189925512209040385)
          ·
            refine ⟨1572509392444134156780289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2096679189925512209040385 1572509392444134156780289)
            ·
              refine ⟨1179382044333100617585217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1572509392444134156780289 1179382044333100617585217)
              ·
                refine ⟨884536533249825463188913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1179382044333100617585217 884536533249825463188913)
                ·
                  refine ⟨663402399937369097391685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 884536533249825463188913 663402399937369097391685)
                  ·
                    refine ⟨124387949988256705760941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663402399937369097391685 124387949988256705760941)
                    ·
                      rfl

theorem cell22_363367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 2, 2, 4].length) (baseStart_363367 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363367 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363367 prefixEnd_363367 := by exact prefixLift 363367
  have htrace : WordTrace (prefixWord ++ tailWord_363367) baseStart_363367 baseEnd_363367 := by
    simpa [prefixWord, tailWord_363367, baseEnd_363367] using wordTrace_append hprefix tailTrace_363367
  have hstable : (prefixWord ++ tailWord_363367).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363367).length < 2 ^ (prefixWord ++ tailWord_363367).sum := by decide
  have hdescent : baseEnd_363367 < baseStart_363367 := by decide
  rcases family_descends (prefixWord ++ tailWord_363367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363395 : List Nat := [1, 1, 1, 3, 4, 1, 1, 2, 2, 6]
def baseStart_363395 : Nat := 118140960795 + 363395 * 2 ^ 59
def prefixEnd_363395 : Nat := 4983230072969 + 3 ^ 40 * 363395 * 2
def baseEnd_363395 : Nat := 124397534960473966060855

theorem tailTrace_363395 : CollatzResearch.WordTrace tailWord_363395 prefixEnd_363395 124397534960473966060855 := by
  unfold tailWord_363395
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254104518489452770027639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8836069678992968513351759 13254104518489452770027639)
  ·
    refine ⟨19881156777734179155041459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13254104518489452770027639 19881156777734179155041459)
    ·
      refine ⟨29821735166601268732562189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19881156777734179155041459 29821735166601268732562189)
      ·
        refine ⟨11183150687475475774710821, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 29821735166601268732562189 11183150687475475774710821)
        ·
          refine ⟨2096840753901651707758279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11183150687475475774710821 2096840753901651707758279)
          ·
            refine ⟨3145261130852477561637419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2096840753901651707758279 3145261130852477561637419)
            ·
              refine ⟨4717891696278716342456129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3145261130852477561637419 4717891696278716342456129)
              ·
                refine ⟨3538418772209037256842097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4717891696278716342456129 3538418772209037256842097)
                ·
                  refine ⟨2653814079156777942631573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3538418772209037256842097 2653814079156777942631573)
                  ·
                    refine ⟨124397534960473966060855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2653814079156777942631573 124397534960473966060855)
                    ·
                      rfl

theorem cell22_363395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 1, 1, 2, 2, 6].length) (baseStart_363395 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363395 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363395 prefixEnd_363395 := by exact prefixLift 363395
  have htrace : WordTrace (prefixWord ++ tailWord_363395) baseStart_363395 baseEnd_363395 := by
    simpa [prefixWord, tailWord_363395, baseEnd_363395] using wordTrace_append hprefix tailTrace_363395
  have hstable : (prefixWord ++ tailWord_363395).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363395).length < 2 ^ (prefixWord ++ tailWord_363395).sum := by decide
  have hdescent : baseEnd_363395 < baseStart_363395 := by decide
  rcases family_descends (prefixWord ++ tailWord_363395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363397 : List Nat := [1, 3, 1, 1, 3, 3, 1, 1, 5, 3]
def baseStart_363397 : Nat := 118140960795 + 363397 * 2 ^ 59
def prefixEnd_363397 : Nat := 4983230072969 + 3 ^ 40 * 363397 * 2
def baseEnd_363397 : Nat := 124398219601346627510849

theorem tailTrace_363397 : CollatzResearch.WordTrace tailWord_363397 prefixEnd_363397 124398219601346627510849 := by
  unfold tailWord_363397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13254177464482207111600445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8836118309654804741066963 13254177464482207111600445)
  ·
    refine ⟨4970316549180827666850167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13254177464482207111600445 4970316549180827666850167)
    ·
      refine ⟨7455474823771241500275251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4970316549180827666850167 7455474823771241500275251)
      ·
        refine ⟨11183212235656862250412877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7455474823771241500275251 11183212235656862250412877)
        ·
          refine ⟨4193704588371323343904829, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11183212235656862250412877 4193704588371323343904829)
          ·
            refine ⟨1572639220639246253964311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4193704588371323343904829 1572639220639246253964311)
            ·
              refine ⟨2358958830958869380946467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1572639220639246253964311 2358958830958869380946467)
              ·
                refine ⟨3538438246438304071419701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2358958830958869380946467 3538438246438304071419701)
                ·
                  refine ⟨331728585603591006695597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3538438246438304071419701 331728585603591006695597)
                  ·
                    refine ⟨124398219601346627510849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331728585603591006695597 124398219601346627510849)
                    ·
                      rfl

theorem cell22_363397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 1, 1, 5, 3].length) (baseStart_363397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363397 prefixEnd_363397 := by exact prefixLift 363397
  have htrace : WordTrace (prefixWord ++ tailWord_363397) baseStart_363397 baseEnd_363397 := by
    simpa [prefixWord, tailWord_363397, baseEnd_363397] using wordTrace_append hprefix tailTrace_363397
  have hstable : (prefixWord ++ tailWord_363397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363397).length < 2 ^ (prefixWord ++ tailWord_363397).sum := by decide
  have hdescent : baseEnd_363397 < baseStart_363397 := by decide
  rcases family_descends (prefixWord ++ tailWord_363397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363427 : List Nat := [1, 1, 1, 4, 1, 2, 5, 2, 5]
def baseStart_363427 : Nat := 118140960795 + 363427 * 2 ^ 59
def prefixEnd_363427 : Nat := 4983230072969 + 3 ^ 40 * 363427 * 2
def baseEnd_363427 : Nat := 41469496404812183086919

theorem tailTrace_363427 : CollatzResearch.WordTrace tailWord_363427 prefixEnd_363427 41469496404812183086919 := by
  unfold tailWord_363427
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255271654373522235192535, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8836847769582348156795023 13255271654373522235192535)
  ·
    refine ⟨19882907481560283352788803, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13255271654373522235192535 19882907481560283352788803)
    ·
      refine ⟨29824361222340425029183205, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19882907481560283352788803 29824361222340425029183205)
      ·
        refine ⟨5592067729188829692971851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 29824361222340425029183205 5592067729188829692971851)
        ·
          refine ⟨8388101593783244539457777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5592067729188829692971851 8388101593783244539457777)
          ·
            refine ⟨6291076195337433404593333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8388101593783244539457777 6291076195337433404593333)
            ·
              refine ⟨589788393312884381680625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6291076195337433404593333 589788393312884381680625)
              ·
                refine ⟨442341294984663286260469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 589788393312884381680625 442341294984663286260469)
                ·
                  refine ⟨41469496404812183086919, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442341294984663286260469 41469496404812183086919)
                  ·
                    rfl

theorem cell22_363427_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 5, 2, 5].length) (baseStart_363427 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363427 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363427 prefixEnd_363427 := by exact prefixLift 363427
  have htrace : WordTrace (prefixWord ++ tailWord_363427) baseStart_363427 baseEnd_363427 := by
    simpa [prefixWord, tailWord_363427, baseEnd_363427] using wordTrace_append hprefix tailTrace_363427
  have hstable : (prefixWord ++ tailWord_363427).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363427).length < 2 ^ (prefixWord ++ tailWord_363427).sum := by decide
  have hdescent : baseEnd_363427 < baseStart_363427 := by decide
  rcases family_descends (prefixWord ++ tailWord_363427) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363431 : List Nat := [1, 1, 6, 1, 3, 1, 2, 1, 3, 3]
def baseStart_363431 : Nat := 118140960795 + 363431 * 2 ^ 59
def prefixEnd_363431 : Nat := 4983230072969 + 3 ^ 40 * 363431 * 2
def baseEnd_363431 : Nat := 124409858496181872160745

theorem tailTrace_363431 : CollatzResearch.WordTrace tailWord_363431 prefixEnd_363431 124409858496181872160745 := by
  unfold tailWord_363431
  simp only [CollatzResearch.WordTrace]
  refine ⟨13255417546359030918338147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8836945030906020612225431 13255417546359030918338147)
  ·
    refine ⟨19883126319538546377507221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13255417546359030918338147 19883126319538546377507221)
    ·
      refine ⟨932021546228369361445651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19883126319538546377507221 932021546228369361445651)
      ·
        refine ⟨1398032319342554042168477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932021546228369361445651 1398032319342554042168477)
        ·
          refine ⟨524262119753457765813179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1398032319342554042168477 524262119753457765813179)
          ·
            refine ⟨786393179630186648719769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 524262119753457765813179 786393179630186648719769)
            ·
              refine ⟨589794884722639986539827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 786393179630186648719769 589794884722639986539827)
              ·
                refine ⟨884692327083959979809741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 589794884722639986539827 884692327083959979809741)
                ·
                  refine ⟨331759622656484992428653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 884692327083959979809741 331759622656484992428653)
                  ·
                    refine ⟨124409858496181872160745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331759622656484992428653 124409858496181872160745)
                    ·
                      rfl

theorem cell22_363431_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_363431 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363431 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363431 prefixEnd_363431 := by exact prefixLift 363431
  have htrace : WordTrace (prefixWord ++ tailWord_363431) baseStart_363431 baseEnd_363431 := by
    simpa [prefixWord, tailWord_363431, baseEnd_363431] using wordTrace_append hprefix tailTrace_363431
  have hstable : (prefixWord ++ tailWord_363431).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363431).length < 2 ^ (prefixWord ++ tailWord_363431).sum := by decide
  have hdescent : baseEnd_363431 < baseStart_363431 := by decide
  rcases family_descends (prefixWord ++ tailWord_363431) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363455 : List Nat := [1, 1, 2, 2, 2, 1, 2, 3, 8]
def baseStart_363455 : Nat := 118140960795 + 363455 * 2 ^ 59
def prefixEnd_363455 : Nat := 4983230072969 + 3 ^ 40 * 363455 * 2
def baseEnd_363455 : Nat := 41472691395551269853557

theorem tailTrace_363455 : CollatzResearch.WordTrace tailWord_363455 prefixEnd_363455 41472691395551269853557 := by
  unfold tailWord_363455
  simp only [CollatzResearch.WordTrace]
  refine ⟨13256292898272083017211819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8837528598848055344807879 13256292898272083017211819)
  ·
    refine ⟨19884439347408124525817729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13256292898272083017211819 19884439347408124525817729)
    ·
      refine ⟨14913329510556093394363297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19884439347408124525817729 14913329510556093394363297)
      ·
        refine ⟨11184997132917070045772473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14913329510556093394363297 11184997132917070045772473)
        ·
          refine ⟨8388747849687802534329355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11184997132917070045772473 8388747849687802534329355)
          ·
            refine ⟨12583121774531703801494033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8388747849687802534329355 12583121774531703801494033)
            ·
              refine ⟨9437341330898777851120525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12583121774531703801494033 9437341330898777851120525)
              ·
                refine ⟨3539002999087041694170197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9437341330898777851120525 3539002999087041694170197)
                ·
                  refine ⟨41472691395551269853557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3539002999087041694170197 41472691395551269853557)
                  ·
                    rfl

theorem cell22_363455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 2, 3, 8].length) (baseStart_363455 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363455 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363455 prefixEnd_363455 := by exact prefixLift 363455
  have htrace : WordTrace (prefixWord ++ tailWord_363455) baseStart_363455 baseEnd_363455 := by
    simpa [prefixWord, tailWord_363455, baseEnd_363455] using wordTrace_append hprefix tailTrace_363455
  have hstable : (prefixWord ++ tailWord_363455).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363455).length < 2 ^ (prefixWord ++ tailWord_363455).sum := by decide
  have hdescent : baseEnd_363455 < baseStart_363455 := by decide
  rcases family_descends (prefixWord ++ tailWord_363455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363566 : List Nat := [4, 1, 3, 1, 1, 1, 3, 2, 3, 3]
def baseStart_363566 : Nat := 118140960795 + 363566 * 2 ^ 59
def prefixEnd_363566 : Nat := 4983230072969 + 3 ^ 40 * 363566 * 2
def baseEnd_363566 : Nat := 124456071755086520035331

theorem tailTrace_363566 : CollatzResearch.WordTrace tailWord_363566 prefixEnd_363566 124456071755086520035331 := by
  unfold tailWord_363566
  simp only [CollatzResearch.WordTrace]
  refine ⟨1657542675108743621812819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8840227600579965983001701 1657542675108743621812819)
  ·
    refine ⟨2486314012663115432719229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1657542675108743621812819 2486314012663115432719229)
    ·
      refine ⟨932367754748668287269711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2486314012663115432719229 932367754748668287269711)
      ·
        refine ⟨1398551632123002430904567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 932367754748668287269711 1398551632123002430904567)
        ·
          refine ⟨2097827448184503646356851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398551632123002430904567 2097827448184503646356851)
          ·
            refine ⟨3146741172276755469535277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2097827448184503646356851 3146741172276755469535277)
            ·
              refine ⟨1180027939603783301075729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3146741172276755469535277 1180027939603783301075729)
              ·
                refine ⟨885020954702837475806797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1180027939603783301075729 885020954702837475806797)
                ·
                  refine ⟨331882858013564053427549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 885020954702837475806797 331882858013564053427549)
                  ·
                    refine ⟨124456071755086520035331, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331882858013564053427549 124456071755086520035331)
                    ·
                      rfl

theorem cell22_363566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 1, 3, 2, 3, 3].length) (baseStart_363566 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363566 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363566 prefixEnd_363566 := by exact prefixLift 363566
  have htrace : WordTrace (prefixWord ++ tailWord_363566) baseStart_363566 baseEnd_363566 := by
    simpa [prefixWord, tailWord_363566, baseEnd_363566] using wordTrace_append hprefix tailTrace_363566
  have hstable : (prefixWord ++ tailWord_363566).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363566).length < 2 ^ (prefixWord ++ tailWord_363566).sum := by decide
  have hdescent : baseEnd_363566 < baseStart_363566 := by decide
  rcases family_descends (prefixWord ++ tailWord_363566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363626 : List Nat := [3, 1, 3, 2, 2, 1, 1, 4, 1, 4]
def baseStart_363626 : Nat := 118140960795 + 363626 * 2 ^ 59
def prefixEnd_363626 : Nat := 4983230072969 + 3 ^ 40 * 363626 * 2
def baseEnd_363626 : Nat := 124476610981266363535147

theorem tailTrace_363626 : CollatzResearch.WordTrace tailWord_363626 prefixEnd_363626 124476610981266363535147 := by
  unfold tailWord_363626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315632445163144805421683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8841686520435052814457821 3315632445163144805421683)
  ·
    refine ⟨4973448667744717208132525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315632445163144805421683 4973448667744717208132525)
    ·
      refine ⟨1865043250404268953049697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4973448667744717208132525 1865043250404268953049697)
      ·
        refine ⟨1398782437803201714787273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1865043250404268953049697 1398782437803201714787273)
        ·
          refine ⟨1049086828352401286090455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1398782437803201714787273 1049086828352401286090455)
          ·
            refine ⟨1573630242528601929135683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1049086828352401286090455 1573630242528601929135683)
            ·
              refine ⟨2360445363792902893703525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1573630242528601929135683 2360445363792902893703525)
              ·
                refine ⟨442583505711169292569411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2360445363792902893703525 442583505711169292569411)
                ·
                  refine ⟨663875258566753938854117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442583505711169292569411 663875258566753938854117)
                  ·
                    refine ⟨124476610981266363535147, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 663875258566753938854117 124476610981266363535147)
                    ·
                      rfl

theorem cell22_363626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 4, 1, 4].length) (baseStart_363626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363626 prefixEnd_363626 := by exact prefixLift 363626
  have htrace : WordTrace (prefixWord ++ tailWord_363626) baseStart_363626 baseEnd_363626 := by
    simpa [prefixWord, tailWord_363626, baseEnd_363626] using wordTrace_append hprefix tailTrace_363626
  have hstable : (prefixWord ++ tailWord_363626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363626).length < 2 ^ (prefixWord ++ tailWord_363626).sum := by decide
  have hdescent : baseEnd_363626 < baseStart_363626 := by decide
  rcases family_descends (prefixWord ++ tailWord_363626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363639 : List Nat := [1, 1, 3, 1, 1, 4, 1, 1, 6, 3]
def baseStart_363639 : Nat := 118140960795 + 363639 * 2 ^ 59
def prefixEnd_363639 : Nat := 4983230072969 + 3 ^ 40 * 363639 * 2
def baseEnd_363639 : Nat := 124481061146938662960107

theorem tailTrace_363639 : CollatzResearch.WordTrace tailWord_363639 prefixEnd_363639 124481061146938662960107 := by
  unfold tailWord_363639
  simp only [CollatzResearch.WordTrace]
  refine ⟨13263003929605482441909971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8842002619736988294606647 13263003929605482441909971)
  ·
    refine ⟨19894505894408223662864957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13263003929605482441909971 19894505894408223662864957)
    ·
      refine ⟨7460439710403083873574359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19894505894408223662864957 7460439710403083873574359)
      ·
        refine ⟨11190659565604625810361539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7460439710403083873574359 11190659565604625810361539)
        ·
          refine ⟨16785989348406938715542309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11190659565604625810361539 16785989348406938715542309)
          ·
            refine ⟨3147373002826301009164183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 16785989348406938715542309 3147373002826301009164183)
            ·
              refine ⟨4721059504239451513746275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3147373002826301009164183 4721059504239451513746275)
              ·
                refine ⟨7081589256359177270619413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4721059504239451513746275 7081589256359177270619413)
                ·
                  refine ⟨331949496391836434560285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7081589256359177270619413 331949496391836434560285)
                  ·
                    refine ⟨124481061146938662960107, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 331949496391836434560285 124481061146938662960107)
                    ·
                      rfl

theorem cell22_363639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 1, 6, 3].length) (baseStart_363639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363639 prefixEnd_363639 := by exact prefixLift 363639
  have htrace : WordTrace (prefixWord ++ tailWord_363639) baseStart_363639 baseEnd_363639 := by
    simpa [prefixWord, tailWord_363639, baseEnd_363639] using wordTrace_append hprefix tailTrace_363639
  have hstable : (prefixWord ++ tailWord_363639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363639).length < 2 ^ (prefixWord ++ tailWord_363639).sum := by decide
  have hdescent : baseEnd_363639 < baseStart_363639 := by decide
  rcases family_descends (prefixWord ++ tailWord_363639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363658 : List Nat := [3, 1, 2, 3, 1, 1, 5, 2, 4]
def baseStart_363658 : Nat := 118140960795 + 363658 * 2 ^ 59
def prefixEnd_363658 : Nat := 4983230072969 + 3 ^ 40 * 363658 * 2
def baseEnd_363658 : Nat := 41495855078409648911683

theorem tailTrace_363658 : CollatzResearch.WordTrace tailWord_363658 prefixEnd_363658 41495855078409648911683 := by
  unfold tailWord_363658
  simp only [CollatzResearch.WordTrace]
  refine ⟨3315924229134162171712907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8842464611024432457901085 3315924229134162171712907)
  ·
    refine ⟨4973886343701243257569361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3315924229134162171712907 4973886343701243257569361)
    ·
      refine ⟨3730414757775932443177021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4973886343701243257569361 3730414757775932443177021)
      ·
        refine ⟨1398905534165974666191383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3730414757775932443177021 1398905534165974666191383)
        ·
          refine ⟨2098358301248961999287075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1398905534165974666191383 2098358301248961999287075)
          ·
            refine ⟨3147537451873442998930613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2098358301248961999287075 3147537451873442998930613)
            ·
              refine ⟨295081636113135281149745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3147537451873442998930613 295081636113135281149745)
              ·
                refine ⟨221311227084851460862309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295081636113135281149745 221311227084851460862309)
                ·
                  refine ⟨41495855078409648911683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221311227084851460862309 41495855078409648911683)
                  ·
                    rfl

theorem cell22_363658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 1, 5, 2, 4].length) (baseStart_363658 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363658 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363658 prefixEnd_363658 := by exact prefixLift 363658
  have htrace : WordTrace (prefixWord ++ tailWord_363658) baseStart_363658 baseEnd_363658 := by
    simpa [prefixWord, tailWord_363658, baseEnd_363658] using wordTrace_append hprefix tailTrace_363658
  have hstable : (prefixWord ++ tailWord_363658).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363658).length < 2 ^ (prefixWord ++ tailWord_363658).sum := by decide
  have hdescent : baseEnd_363658 < baseStart_363658 := by decide
  rcases family_descends (prefixWord ++ tailWord_363658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363846 : List Nat := [6, 1, 1, 3, 2, 1, 1, 2, 1, 4]
def baseStart_363846 : Nat := 118140960795 + 363846 * 2 ^ 59
def prefixEnd_363846 : Nat := 4983230072969 + 3 ^ 40 * 363846 * 2
def baseEnd_363846 : Nat := 124551921477259123034473

theorem tailTrace_363846 : CollatzResearch.WordTrace tailWord_363846 prefixEnd_363846 124551921477259123034473 := by
  unfold tailWord_363846
  simp only [CollatzResearch.WordTrace]
  refine ⟨414704807495486149834231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8847035893237037863130261 414704807495486149834231)
  ·
    refine ⟨622057211243229224751347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 414704807495486149834231 622057211243229224751347)
    ·
      refine ⟨933085816864843837127021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622057211243229224751347 933085816864843837127021)
      ·
        refine ⟨349907181324316438922633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 933085816864843837127021 349907181324316438922633)
        ·
          refine ⟨262430385993237329191975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 349907181324316438922633 262430385993237329191975)
          ·
            refine ⟨393645578989855993787963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262430385993237329191975 393645578989855993787963)
            ·
              refine ⟨590468368484783990681945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393645578989855993787963 590468368484783990681945)
              ·
                refine ⟨442851276363587993011459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590468368484783990681945 442851276363587993011459)
                ·
                  refine ⟨664276914545381989517189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 442851276363587993011459 664276914545381989517189)
                  ·
                    refine ⟨124551921477259123034473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 664276914545381989517189 124551921477259123034473)
                    ·
                      rfl

theorem cell22_363846_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 3, 2, 1, 1, 2, 1, 4].length) (baseStart_363846 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363846 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363846 prefixEnd_363846 := by exact prefixLift 363846
  have htrace : WordTrace (prefixWord ++ tailWord_363846) baseStart_363846 baseEnd_363846 := by
    simpa [prefixWord, tailWord_363846, baseEnd_363846] using wordTrace_append hprefix tailTrace_363846
  have hstable : (prefixWord ++ tailWord_363846).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363846).length < 2 ^ (prefixWord ++ tailWord_363846).sum := by decide
  have hdescent : baseEnd_363846 < baseStart_363846 := by decide
  rcases family_descends (prefixWord ++ tailWord_363846) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363911 : List Nat := [1, 1, 4, 2, 2, 2, 1, 1, 8]
def baseStart_363911 : Nat := 118140960795 + 363911 * 2 ^ 59
def prefixEnd_363911 : Nat := 4983230072969 + 3 ^ 40 * 363911 * 2
def baseEnd_363911 : Nat := 41524724101873540053091

theorem tailTrace_363911 : CollatzResearch.WordTrace tailWord_363911 prefixEnd_363911 41524724101873540053091 := by
  unfold tailWord_363911
  simp only [CollatzResearch.WordTrace]
  refine ⟨13272924584620072895811587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8848616389746715263874391 13272924584620072895811587)
  ·
    refine ⟨19909386876930109343717381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13272924584620072895811587 19909386876930109343717381)
    ·
      refine ⟨3733010039424395501947009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19909386876930109343717381 3733010039424395501947009)
      ·
        refine ⟨2799757529568296626460257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3733010039424395501947009 2799757529568296626460257)
        ·
          refine ⟨2099818147176222469845193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2799757529568296626460257 2099818147176222469845193)
          ·
            refine ⟨1574863610382166852383895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2099818147176222469845193 1574863610382166852383895)
            ·
              refine ⟨2362295415573250278575843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1574863610382166852383895 2362295415573250278575843)
              ·
                refine ⟨3543443123359875417863765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2362295415573250278575843 3543443123359875417863765)
                ·
                  refine ⟨41524724101873540053091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3543443123359875417863765 41524724101873540053091)
                  ·
                    rfl

theorem cell22_363911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 2, 1, 1, 8].length) (baseStart_363911 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363911 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363911 prefixEnd_363911 := by exact prefixLift 363911
  have htrace : WordTrace (prefixWord ++ tailWord_363911) baseStart_363911 baseEnd_363911 := by
    simpa [prefixWord, tailWord_363911, baseEnd_363911] using wordTrace_append hprefix tailTrace_363911
  have hstable : (prefixWord ++ tailWord_363911).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363911).length < 2 ^ (prefixWord ++ tailWord_363911).sum := by decide
  have hdescent : baseEnd_363911 < baseStart_363911 := by decide
  rcases family_descends (prefixWord ++ tailWord_363911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363934 : List Nat := [4, 3, 1, 2, 3, 1, 1, 2, 5]
def baseStart_363934 : Nat := 118140960795 + 363934 * 2 ^ 59
def prefixEnd_363934 : Nat := 4983230072969 + 3 ^ 40 * 363934 * 2
def baseEnd_363934 : Nat := 41527348558552075611401

theorem tailTrace_363934 : CollatzResearch.WordTrace tailWord_363934 prefixEnd_363934 41527348558552075611401 := by
  unfold tailWord_363934
  simp only [CollatzResearch.WordTrace]
  refine ⟨1659220432942093477987357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8849175642357831882599237 1659220432942093477987357)
  ·
    refine ⟨622207662353285054245259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1659220432942093477987357 622207662353285054245259)
    ·
      refine ⟨933311493529927581367889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622207662353285054245259 933311493529927581367889)
      ·
        refine ⟨699983620147445686025917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 933311493529927581367889 699983620147445686025917)
        ·
          refine ⟨262493857555292132259719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 699983620147445686025917 262493857555292132259719)
          ·
            refine ⟨393740786332938198389579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262493857555292132259719 393740786332938198389579)
            ·
              refine ⟨590611179499407297584369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 393740786332938198389579 590611179499407297584369)
              ·
                refine ⟨442958384624555473188277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 590611179499407297584369 442958384624555473188277)
                ·
                  refine ⟨41527348558552075611401, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 442958384624555473188277 41527348558552075611401)
                  ·
                    rfl

theorem cell22_363934_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 1, 2, 5].length) (baseStart_363934 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363934 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363934 prefixEnd_363934 := by exact prefixLift 363934
  have htrace : WordTrace (prefixWord ++ tailWord_363934) baseStart_363934 baseEnd_363934 := by
    simpa [prefixWord, tailWord_363934, baseEnd_363934] using wordTrace_append hprefix tailTrace_363934
  have hstable : (prefixWord ++ tailWord_363934).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363934).length < 2 ^ (prefixWord ++ tailWord_363934).sum := by decide
  have hdescent : baseEnd_363934 < baseStart_363934 := by decide
  rcases family_descends (prefixWord ++ tailWord_363934) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_363990 : List Nat := [5, 2, 1, 1, 1, 4, 8]
def baseStart_363990 : Nat := 118140960795 + 363990 * 2 ^ 59
def prefixEnd_363990 : Nat := 4983230072969 + 3 ^ 40 * 363990 * 2
def baseEnd_363990 : Nat := 4614859837781138793853

theorem tailTrace_363990 : CollatzResearch.WordTrace tailWord_363990 prefixEnd_363990 4614859837781138793853 := by
  unfold tailWord_363990
  simp only [CollatzResearch.WordTrace]
  refine ⟨829737871958366836746089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8850537300889246258624949 829737871958366836746089)
  ·
    refine ⟨622303403968775127559567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 829737871958366836746089 622303403968775127559567)
    ·
      refine ⟨933455105953162691339351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 622303403968775127559567 933455105953162691339351)
      ·
        refine ⟨1400182658929744037009027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933455105953162691339351 1400182658929744037009027)
        ·
          refine ⟨2100273988394616055513541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400182658929744037009027 2100273988394616055513541)
          ·
            refine ⟨393801372823990510408789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2100273988394616055513541 393801372823990510408789)
            ·
              refine ⟨4614859837781138793853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 393801372823990510408789 4614859837781138793853)
              ·
                rfl

theorem cell22_363990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 8].length) (baseStart_363990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_363990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_363990 prefixEnd_363990 := by exact prefixLift 363990
  have htrace : WordTrace (prefixWord ++ tailWord_363990) baseStart_363990 baseEnd_363990 := by
    simpa [prefixWord, tailWord_363990, baseEnd_363990] using wordTrace_append hprefix tailTrace_363990
  have hstable : (prefixWord ++ tailWord_363990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_363990).length < 2 ^ (prefixWord ++ tailWord_363990).sum := by decide
  have hdescent : baseEnd_363990 < baseStart_363990 := by decide
  rcases family_descends (prefixWord ++ tailWord_363990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364056 : List Nat := [2, 1, 2, 3, 4, 2, 2, 2, 1, 3]
def baseStart_364056 : Nat := 118140960795 + 364056 * 2 ^ 59
def prefixEnd_364056 : Nat := 4983230072969 + 3 ^ 40 * 364056 * 2
def baseEnd_364056 : Nat := 124623808768888575283829

theorem tailTrace_364056 : CollatzResearch.WordTrace tailWord_364056 prefixEnd_364056 124623808768888575283829 := by
  unfold tailWord_364056
  simp only [CollatzResearch.WordTrace]
  refine ⟨6639106584547381329920011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8852142112729841773226681 6639106584547381329920011)
  ·
    refine ⟨9958659876821071994880017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6639106584547381329920011 9958659876821071994880017)
    ·
      refine ⟨7468994907615803996160013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9958659876821071994880017 7468994907615803996160013)
      ·
        refine ⟨2800873090355926498560005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7468994907615803996160013 2800873090355926498560005)
        ·
          refine ⟨525163704441736218480001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2800873090355926498560005 525163704441736218480001)
          ·
            refine ⟨393872778331302163860001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525163704441736218480001 393872778331302163860001)
            ·
              refine ⟨295404583748476622895001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 393872778331302163860001 295404583748476622895001)
              ·
                refine ⟨221553437811357467171251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295404583748476622895001 221553437811357467171251)
                ·
                  refine ⟨332330156717036200756877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 221553437811357467171251 332330156717036200756877)
                  ·
                    refine ⟨124623808768888575283829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332330156717036200756877 124623808768888575283829)
                    ·
                      rfl

theorem cell22_364056_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 4, 2, 2, 2, 1, 3].length) (baseStart_364056 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364056 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364056 prefixEnd_364056 := by exact prefixLift 364056
  have htrace : WordTrace (prefixWord ++ tailWord_364056) baseStart_364056 baseEnd_364056 := by
    simpa [prefixWord, tailWord_364056, baseEnd_364056] using wordTrace_append hprefix tailTrace_364056
  have hstable : (prefixWord ++ tailWord_364056).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364056).length < 2 ^ (prefixWord ++ tailWord_364056).sum := by decide
  have hdescent : baseEnd_364056 < baseStart_364056 := by decide
  rcases family_descends (prefixWord ++ tailWord_364056) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364097 : List Nat := [1, 2, 5, 1, 1, 1, 4, 3, 4]
def baseStart_364097 : Nat := 118140960795 + 364097 * 2 ^ 59
def prefixEnd_364097 : Nat := 4983230072969 + 3 ^ 40 * 364097 * 2
def baseEnd_364097 : Nat := 41545947968926045002901

theorem tailTrace_364097 : CollatzResearch.WordTrace tailWord_364097 prefixEnd_364097 41545947968926045002901 := by
  unfold tailWord_364097
  simp only [CollatzResearch.WordTrace]
  refine ⟨13279708561946226662082545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8853139041297484441388363 13279708561946226662082545)
  ·
    refine ⟨9959781421459669996561909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13279708561946226662082545 9959781421459669996561909)
    ·
      refine ⟨933729508261844062177679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9959781421459669996561909 933729508261844062177679)
      ·
        refine ⟨1400594262392766093266519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 933729508261844062177679 1400594262392766093266519)
        ·
          refine ⟨2100891393589149139899779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400594262392766093266519 2100891393589149139899779)
          ·
            refine ⟨3151337090383723709849669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2100891393589149139899779 3151337090383723709849669)
            ·
              refine ⟨590875704446948195596813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3151337090383723709849669 590875704446948195596813)
              ·
                refine ⟨221578389167605573348805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 590875704446948195596813 221578389167605573348805)
                ·
                  refine ⟨41545947968926045002901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221578389167605573348805 41545947968926045002901)
                  ·
                    rfl

theorem cell22_364097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 4, 3, 4].length) (baseStart_364097 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364097 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364097 prefixEnd_364097 := by exact prefixLift 364097
  have htrace : WordTrace (prefixWord ++ tailWord_364097) baseStart_364097 baseEnd_364097 := by
    simpa [prefixWord, tailWord_364097, baseEnd_364097] using wordTrace_append hprefix tailTrace_364097
  have hstable : (prefixWord ++ tailWord_364097).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364097).length < 2 ^ (prefixWord ++ tailWord_364097).sum := by decide
  have hdescent : baseEnd_364097 < baseStart_364097 := by decide
  rcases family_descends (prefixWord ++ tailWord_364097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364108 : List Nat := [2, 2, 1, 3, 1, 4, 9]
def baseStart_364108 : Nat := 118140960795 + 364108 * 2 ^ 59
def prefixEnd_364108 : Nat := 4983230072969 + 3 ^ 40 * 364108 * 2
def baseEnd_364108 : Nat := 4616355904873250851247

theorem tailTrace_364108 : CollatzResearch.WordTrace tailWord_364108 prefixEnd_364108 4616355904873250851247 := by
  unfold tailWord_364108
  simp only [CollatzResearch.WordTrace]
  refine ⟨6640054882453187770366489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8853406509937583693821985 6640054882453187770366489)
  ·
    refine ⟨4980041161839890827774867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6640054882453187770366489 4980041161839890827774867)
    ·
      refine ⟨7470061742759836241662301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4980041161839890827774867 7470061742759836241662301)
      ·
        refine ⟨2801273153534938590623363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7470061742759836241662301 2801273153534938590623363)
        ·
          refine ⟨4201909730302407885935045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2801273153534938590623363 4201909730302407885935045)
          ·
            refine ⟨787858074431701478612821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4201909730302407885935045 787858074431701478612821)
            ·
              refine ⟨4616355904873250851247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 787858074431701478612821 4616355904873250851247)
              ·
                rfl

theorem cell22_364108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 9].length) (baseStart_364108 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364108 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364108 prefixEnd_364108 := by exact prefixLift 364108
  have htrace : WordTrace (prefixWord ++ tailWord_364108) baseStart_364108 baseEnd_364108 := by
    simpa [prefixWord, tailWord_364108, baseEnd_364108] using wordTrace_append hprefix tailTrace_364108
  have hstable : (prefixWord ++ tailWord_364108).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364108).length < 2 ^ (prefixWord ++ tailWord_364108).sum := by decide
  have hdescent : baseEnd_364108 < baseStart_364108 := by decide
  rcases family_descends (prefixWord ++ tailWord_364108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364153 : List Nat := [1, 2, 1, 3, 3, 1, 1, 1, 9]
def baseStart_364153 : Nat := 118140960795 + 364153 * 2 ^ 59
def prefixEnd_364153 : Nat := 4983230072969 + 3 ^ 40 * 364153 * 2
def baseEnd_364153 : Nat := 41552337950404218536177

theorem tailTrace_364153 : CollatzResearch.WordTrace tailWord_364153 prefixEnd_364153 41552337950404218536177 := by
  unfold tailWord_364153
  simp only [CollatzResearch.WordTrace]
  refine ⟨13281751049743348226121113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8854500699828898817414075 13281751049743348226121113)
  ·
    refine ⟨9961313287307511169590835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13281751049743348226121113 9961313287307511169590835)
    ·
      refine ⟨14941969930961266754386253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9961313287307511169590835 14941969930961266754386253)
      ·
        refine ⟨5603238724110475032894845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14941969930961266754386253 5603238724110475032894845)
        ·
          refine ⟨2101214521541428137335567, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5603238724110475032894845 2101214521541428137335567)
          ·
            refine ⟨3151821782312142206003351, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2101214521541428137335567 3151821782312142206003351)
            ·
              refine ⟨4727732673468213309005027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3151821782312142206003351 4727732673468213309005027)
              ·
                refine ⟨7091599010202319963507541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4727732673468213309005027 7091599010202319963507541)
                ·
                  refine ⟨41552337950404218536177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7091599010202319963507541 41552337950404218536177)
                  ·
                    rfl

theorem cell22_364153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 1, 1, 1, 9].length) (baseStart_364153 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364153 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364153 prefixEnd_364153 := by exact prefixLift 364153
  have htrace : WordTrace (prefixWord ++ tailWord_364153) baseStart_364153 baseEnd_364153 := by
    simpa [prefixWord, tailWord_364153, baseEnd_364153] using wordTrace_append hprefix tailTrace_364153
  have hstable : (prefixWord ++ tailWord_364153).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364153).length < 2 ^ (prefixWord ++ tailWord_364153).sum := by decide
  have hdescent : baseEnd_364153 < baseStart_364153 := by decide
  rcases family_descends (prefixWord ++ tailWord_364153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364170 : List Nat := [3, 1, 2, 3, 2, 1, 2, 1, 7]
def baseStart_364170 : Nat := 118140960795 + 364170 * 2 ^ 59
def prefixEnd_364170 : Nat := 4983230072969 + 3 ^ 40 * 364170 * 2
def baseEnd_364170 : Nat := 41554277766210092644493

theorem tailTrace_364170 : CollatzResearch.WordTrace tailWord_364170 prefixEnd_364170 41554277766210092644493 := by
  unfold tailWord_364170
  simp only [CollatzResearch.WordTrace]
  refine ⟨3320592772670440032372491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8854914060454506752993309 3320592772670440032372491)
  ·
    refine ⟨4980889159005660048558737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3320592772670440032372491 4980889159005660048558737)
    ·
      refine ⟨3735666869254245036419053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4980889159005660048558737 3735666869254245036419053)
      ·
        refine ⟨1400875075970341888657145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3735666869254245036419053 1400875075970341888657145)
        ·
          refine ⟨1050656306977756416492859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1400875075970341888657145 1050656306977756416492859)
          ·
            refine ⟨1575984460466634624739289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1050656306977756416492859 1575984460466634624739289)
            ·
              refine ⟨1181988345349975968554467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1575984460466634624739289 1181988345349975968554467)
              ·
                refine ⟨1772982518024963952831701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1181988345349975968554467 1772982518024963952831701)
                ·
                  refine ⟨41554277766210092644493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1772982518024963952831701 41554277766210092644493)
                  ·
                    rfl

theorem cell22_364170_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 1, 7].length) (baseStart_364170 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364170 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364170 prefixEnd_364170 := by exact prefixLift 364170
  have htrace : WordTrace (prefixWord ++ tailWord_364170) baseStart_364170 baseEnd_364170 := by
    simpa [prefixWord, tailWord_364170, baseEnd_364170] using wordTrace_append hprefix tailTrace_364170
  have hstable : (prefixWord ++ tailWord_364170).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364170).length < 2 ^ (prefixWord ++ tailWord_364170).sum := by decide
  have hdescent : baseEnd_364170 < baseStart_364170 := by decide
  rcases family_descends (prefixWord ++ tailWord_364170) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364174 : List Nat := [4, 1, 1, 3, 1, 4, 1, 1, 3, 3]
def baseStart_364174 : Nat := 118140960795 + 364174 * 2 ^ 59
def prefixEnd_364174 : Nat := 4983230072969 + 3 ^ 40 * 364174 * 2
def baseEnd_364174 : Nat := 124664202580375600833467

theorem tailTrace_364174 : CollatzResearch.WordTrace tailWord_364174 prefixEnd_364174 124664202580375600833467 := by
  unfold tailWord_364174
  simp only [CollatzResearch.WordTrace]
  refine ⟨1660314622833408601579447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8855011321778179208423717 1660314622833408601579447)
  ·
    refine ⟨2490471934250112902369171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1660314622833408601579447 2490471934250112902369171)
    ·
      refine ⟨3735707901375169353553757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2490471934250112902369171 3735707901375169353553757)
      ·
        refine ⟨1400890463015688507582659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3735707901375169353553757 1400890463015688507582659)
        ·
          refine ⟨2101335694523532761373989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1400890463015688507582659 2101335694523532761373989)
          ·
            refine ⟨394000442723162392757623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2101335694523532761373989 394000442723162392757623)
            ·
              refine ⟨591000664084743589136435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394000442723162392757623 591000664084743589136435)
              ·
                refine ⟨886500996127115383704653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 591000664084743589136435 886500996127115383704653)
                ·
                  refine ⟨332437873547668268889245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 886500996127115383704653 332437873547668268889245)
                  ·
                    refine ⟨124664202580375600833467, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332437873547668268889245 124664202580375600833467)
                    ·
                      rfl

theorem cell22_364174_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 4, 1, 1, 3, 3].length) (baseStart_364174 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364174 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364174 prefixEnd_364174 := by exact prefixLift 364174
  have htrace : WordTrace (prefixWord ++ tailWord_364174) baseStart_364174 baseEnd_364174 := by
    simpa [prefixWord, tailWord_364174, baseEnd_364174] using wordTrace_append hprefix tailTrace_364174
  have hstable : (prefixWord ++ tailWord_364174).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364174).length < 2 ^ (prefixWord ++ tailWord_364174).sum := by decide
  have hdescent : baseEnd_364174 < baseStart_364174 := by decide
  rcases family_descends (prefixWord ++ tailWord_364174) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364232 : List Nat := [2, 1, 3, 1, 2, 2, 3, 4, 4]
def baseStart_364232 : Nat := 118140960795 + 364232 * 2 ^ 59
def prefixEnd_364232 : Nat := 4983230072969 + 3 ^ 40 * 364232 * 2
def baseEnd_364232 : Nat := 41561352388560927627763

theorem tailTrace_364232 : CollatzResearch.WordTrace tailWord_364232 prefixEnd_364232 41561352388560927627763 := by
  unfold tailWord_364232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6642316208228572359123475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8856421610971429812164633 6642316208228572359123475)
  ·
    refine ⟨9963474312342858538685213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6642316208228572359123475 9963474312342858538685213)
    ·
      refine ⟨3736302867128571952006955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9963474312342858538685213 3736302867128571952006955)
      ·
        refine ⟨5604454300692857928010433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3736302867128571952006955 5604454300692857928010433)
        ·
          refine ⟨4203340725519643446007825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5604454300692857928010433 4203340725519643446007825)
          ·
            refine ⟨3152505544139732584505869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4203340725519643446007825 3152505544139732584505869)
            ·
              refine ⟨1182189579052399719189701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3152505544139732584505869 1182189579052399719189701)
              ·
                refine ⟨221660546072324947348069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1182189579052399719189701 221660546072324947348069)
                ·
                  refine ⟨41561352388560927627763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221660546072324947348069 41561352388560927627763)
                  ·
                    rfl

theorem cell22_364232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 2, 3, 4, 4].length) (baseStart_364232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364232 prefixEnd_364232 := by exact prefixLift 364232
  have htrace : WordTrace (prefixWord ++ tailWord_364232) baseStart_364232 baseEnd_364232 := by
    simpa [prefixWord, tailWord_364232, baseEnd_364232] using wordTrace_append hprefix tailTrace_364232
  have hstable : (prefixWord ++ tailWord_364232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364232).length < 2 ^ (prefixWord ++ tailWord_364232).sum := by decide
  have hdescent : baseEnd_364232 < baseStart_364232 := by decide
  rcases family_descends (prefixWord ++ tailWord_364232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364247 : List Nat := [1, 1, 3, 2, 1, 3, 1, 5, 2, 3]
def baseStart_364247 : Nat := 118140960795 + 364247 * 2 ^ 59
def prefixEnd_364247 : Nat := 4983230072969 + 3 ^ 40 * 364247 * 2
def baseEnd_364247 : Nat := 124689191972227743758243

theorem tailTrace_364247 : CollatzResearch.WordTrace tailWord_364247 prefixEnd_364247 124689191972227743758243 := by
  unfold tailWord_364247
  simp only [CollatzResearch.WordTrace]
  refine ⟨13285179511402802280042995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8856786340935201520028663 13285179511402802280042995)
  ·
    refine ⟨19927769267104203420064493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13285179511402802280042995 19927769267104203420064493)
    ·
      refine ⟨7472913475164076282524185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19927769267104203420064493 7472913475164076282524185)
      ·
        refine ⟨5604685106373057211893139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7472913475164076282524185 5604685106373057211893139)
        ·
          refine ⟨8407027659559585817839709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5604685106373057211893139 8407027659559585817839709)
          ·
            refine ⟨3152635372334844681689891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8407027659559585817839709 3152635372334844681689891)
            ·
              refine ⟨4728953058502267022534837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3152635372334844681689891 4728953058502267022534837)
              ·
                refine ⟨443339349234587533362641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4728953058502267022534837 443339349234587533362641)
                ·
                  refine ⟨332504511925940650021981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443339349234587533362641 332504511925940650021981)
                  ·
                    refine ⟨124689191972227743758243, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332504511925940650021981 124689191972227743758243)
                    ·
                      rfl

theorem cell22_364247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_364247 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364247 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364247 prefixEnd_364247 := by exact prefixLift 364247
  have htrace : WordTrace (prefixWord ++ tailWord_364247) baseStart_364247 baseEnd_364247 := by
    simpa [prefixWord, tailWord_364247, baseEnd_364247] using wordTrace_append hprefix tailTrace_364247
  have hstable : (prefixWord ++ tailWord_364247).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364247).length < 2 ^ (prefixWord ++ tailWord_364247).sum := by decide
  have hdescent : baseEnd_364247 < baseStart_364247 := by decide
  rcases family_descends (prefixWord ++ tailWord_364247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364369 : List Nat := [1, 2, 2, 1, 5, 1, 3, 2, 1, 4]
def baseStart_364369 : Nat := 118140960795 + 364369 * 2 ^ 59
def prefixEnd_364369 : Nat := 4983230072969 + 3 ^ 40 * 364369 * 2
def baseEnd_364369 : Nat := 124730955065460092207869

theorem tailTrace_364369 : CollatzResearch.WordTrace tailWord_364369 prefixEnd_364369 124730955065460092207869 := by
  unfold tailWord_364369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13289629216960817115984161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8859752811307211410656107 13289629216960817115984161)
  ·
    refine ⟨9967221912720612836988121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13289629216960817115984161 9967221912720612836988121)
    ·
      refine ⟨7475416434540459627741091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9967221912720612836988121 7475416434540459627741091)
      ·
        refine ⟨11213124651810689441611637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7475416434540459627741091 11213124651810689441611637)
        ·
          refine ⟨1051230436107252135151091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 11213124651810689441611637 1051230436107252135151091)
          ·
            refine ⟨1576845654160878202726637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051230436107252135151091 1576845654160878202726637)
            ·
              refine ⟨591317120310329326022489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1576845654160878202726637 591317120310329326022489)
              ·
                refine ⟨443487840232746994516867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591317120310329326022489 443487840232746994516867)
                ·
                  refine ⟨665231760349120491775301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443487840232746994516867 665231760349120491775301)
                  ·
                    refine ⟨124730955065460092207869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665231760349120491775301 124730955065460092207869)
                    ·
                      rfl

theorem cell22_364369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 3, 2, 1, 4].length) (baseStart_364369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364369 prefixEnd_364369 := by exact prefixLift 364369
  have htrace : WordTrace (prefixWord ++ tailWord_364369) baseStart_364369 baseEnd_364369 := by
    simpa [prefixWord, tailWord_364369, baseEnd_364369] using wordTrace_append hprefix tailTrace_364369
  have hstable : (prefixWord ++ tailWord_364369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364369).length < 2 ^ (prefixWord ++ tailWord_364369).sum := by decide
  have hdescent : baseEnd_364369 < baseStart_364369 := by decide
  rcases family_descends (prefixWord ++ tailWord_364369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364446 : List Nat := [4, 3, 1, 3, 1, 1, 9]
def baseStart_364446 : Nat := 118140960795 + 364446 * 2 ^ 59
def prefixEnd_364446 : Nat := 4983230072969 + 3 ^ 40 * 364446 * 2
def baseEnd_364446 : Nat := 4620641249594724371579

theorem tailTrace_364446 : CollatzResearch.WordTrace tailWord_364446 prefixEnd_364446 4620641249594724371579 := by
  unfold tailWord_364446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1661554704710232408317149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8861625091787906177691461 1661554704710232408317149)
  ·
    refine ⟨623083014266337153118931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1661554704710232408317149 623083014266337153118931)
    ·
      refine ⟨934624521399505729678397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 623083014266337153118931 934624521399505729678397)
      ·
        refine ⟨350484195524814648629399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 934624521399505729678397 350484195524814648629399)
        ·
          refine ⟨525726293287221972944099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350484195524814648629399 525726293287221972944099)
          ·
            refine ⟨788589439930832959416149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525726293287221972944099 788589439930832959416149)
            ·
              refine ⟨4620641249594724371579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 788589439930832959416149 4620641249594724371579)
              ·
                rfl

theorem cell22_364446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 9].length) (baseStart_364446 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364446 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364446 prefixEnd_364446 := by exact prefixLift 364446
  have htrace : WordTrace (prefixWord ++ tailWord_364446) baseStart_364446 baseEnd_364446 := by
    simpa [prefixWord, tailWord_364446, baseEnd_364446] using wordTrace_append hprefix tailTrace_364446
  have hstable : (prefixWord ++ tailWord_364446).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364446).length < 2 ^ (prefixWord ++ tailWord_364446).sum := by decide
  have hdescent : baseEnd_364446 < baseStart_364446 := by decide
  rcases family_descends (prefixWord ++ tailWord_364446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364450 : List Nat := [3, 3, 1, 2, 4, 1, 1, 2, 2, 3]
def baseStart_364450 : Nat := 118140960795 + 364450 * 2 ^ 59
def prefixEnd_364450 : Nat := 4983230072969 + 3 ^ 40 * 364450 * 2
def baseEnd_364450 : Nat := 124758683020802880932621

theorem tailTrace_364450 : CollatzResearch.WordTrace tailWord_364450 prefixEnd_364450 124758683020802880932621 := by
  unfold tailWord_364450
  simp only [CollatzResearch.WordTrace]
  refine ⟨3323145882416841987420701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8861722353111578633121869 3323145882416841987420701)
  ·
    refine ⟨1246179705906315745282763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3323145882416841987420701 1246179705906315745282763)
    ·
      refine ⟨1869269558859473617924145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1246179705906315745282763 1869269558859473617924145)
      ·
        refine ⟨1401952169144605213443109, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1869269558859473617924145 1401952169144605213443109)
        ·
          refine ⟨262866031714613477520583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1401952169144605213443109 262866031714613477520583)
          ·
            refine ⟨394299047571920216280875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 262866031714613477520583 394299047571920216280875)
            ·
              refine ⟨591448571357880324421313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394299047571920216280875 591448571357880324421313)
              ·
                refine ⟨443586428518410243315985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591448571357880324421313 443586428518410243315985)
                ·
                  refine ⟨332689821388807682486989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443586428518410243315985 332689821388807682486989)
                  ·
                    refine ⟨124758683020802880932621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332689821388807682486989 124758683020802880932621)
                    ·
                      rfl

theorem cell22_364450_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 4, 1, 1, 2, 2, 3].length) (baseStart_364450 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364450 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364450 prefixEnd_364450 := by exact prefixLift 364450
  have htrace : WordTrace (prefixWord ++ tailWord_364450) baseStart_364450 baseEnd_364450 := by
    simpa [prefixWord, tailWord_364450, baseEnd_364450] using wordTrace_append hprefix tailTrace_364450
  have hstable : (prefixWord ++ tailWord_364450).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364450).length < 2 ^ (prefixWord ++ tailWord_364450).sum := by decide
  have hdescent : baseEnd_364450 < baseStart_364450 := by decide
  rcases family_descends (prefixWord ++ tailWord_364450) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364457 : List Nat := [1, 2, 1, 1, 1, 1, 4, 6, 5]
def baseStart_364457 : Nat := 118140960795 + 364457 * 2 ^ 59
def prefixEnd_364457 : Nat := 4983230072969 + 3 ^ 40 * 364457 * 2
def baseEnd_364457 : Nat := 41587026421285732002533

theorem tailTrace_364457 : CollatzResearch.WordTrace tailWord_364457 prefixEnd_364457 41587026421285732002533 := by
  unfold tailWord_364457
  simp only [CollatzResearch.WordTrace]
  refine ⟨13292838840642008145187625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8861892560428005430125083 13292838840642008145187625)
  ·
    refine ⟨9969629130481506108890719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13292838840642008145187625 9969629130481506108890719)
    ·
      refine ⟨14954443695722259163336079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9969629130481506108890719 14954443695722259163336079)
      ·
        refine ⟨22431665543583388745004119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14954443695722259163336079 22431665543583388745004119)
        ·
          refine ⟨33647498315375083117506179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22431665543583388745004119 33647498315375083117506179)
          ·
            refine ⟨50471247473062624676259269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33647498315375083117506179 50471247473062624676259269)
            ·
              refine ⟨9463358901199242126798613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50471247473062624676259269 9463358901199242126798613)
              ·
                refine ⟨443594948493714474693685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 9463358901199242126798613 443594948493714474693685)
                ·
                  refine ⟨41587026421285732002533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443594948493714474693685 41587026421285732002533)
                  ·
                    rfl

theorem cell22_364457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 6, 5].length) (baseStart_364457 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364457 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364457 prefixEnd_364457 := by exact prefixLift 364457
  have htrace : WordTrace (prefixWord ++ tailWord_364457) baseStart_364457 baseEnd_364457 := by
    simpa [prefixWord, tailWord_364457, baseEnd_364457] using wordTrace_append hprefix tailTrace_364457
  have hstable : (prefixWord ++ tailWord_364457).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364457).length < 2 ^ (prefixWord ++ tailWord_364457).sum := by decide
  have hdescent : baseEnd_364457 < baseStart_364457 := by decide
  rcases family_descends (prefixWord ++ tailWord_364457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364472 : List Nat := [2, 1, 2, 1, 2, 3, 1, 3, 2, 5]
def baseStart_364472 : Nat := 118140960795 + 364472 * 2 ^ 59
def prefixEnd_364472 : Nat := 4983230072969 + 3 ^ 40 * 364472 * 2
def baseEnd_364472 : Nat := 124766214070402156882553

theorem tailTrace_364472 : CollatzResearch.WordTrace tailWord_364472 prefixEnd_364472 124766214070402156882553 := by
  unfold tailWord_364472
  simp only [CollatzResearch.WordTrace]
  refine ⟨6646692967793832853491835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8862257290391777137989113 6646692967793832853491835)
  ·
    refine ⟨9970039451690749280237753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6646692967793832853491835 9970039451690749280237753)
    ·
      refine ⟨7477529588768061960178315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9970039451690749280237753 7477529588768061960178315)
      ·
        refine ⟨11216294383152092940267473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7477529588768061960178315 11216294383152092940267473)
        ·
          refine ⟨8412220787364069705200605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11216294383152092940267473 8412220787364069705200605)
          ·
            refine ⟨3154582795261526139450227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8412220787364069705200605 3154582795261526139450227)
            ·
              refine ⟨4731874192892289209175341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154582795261526139450227 4731874192892289209175341)
              ·
                refine ⟨1774452822334608453440753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4731874192892289209175341 1774452822334608453440753)
                ·
                  refine ⟨1330839616750956340080565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1774452822334608453440753 1330839616750956340080565)
                  ·
                    refine ⟨124766214070402156882553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1330839616750956340080565 124766214070402156882553)
                    ·
                      rfl

theorem cell22_364472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 3, 2, 5].length) (baseStart_364472 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364472 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364472 prefixEnd_364472 := by exact prefixLift 364472
  have htrace : WordTrace (prefixWord ++ tailWord_364472) baseStart_364472 baseEnd_364472 := by
    simpa [prefixWord, tailWord_364472, baseEnd_364472] using wordTrace_append hprefix tailTrace_364472
  have hstable : (prefixWord ++ tailWord_364472).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364472).length < 2 ^ (prefixWord ++ tailWord_364472).sum := by decide
  have hdescent : baseEnd_364472 < baseStart_364472 := by decide
  rcases family_descends (prefixWord ++ tailWord_364472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364504 : List Nat := [2, 1, 2, 2, 2, 2, 1, 5, 1, 4]
def baseStart_364504 : Nat := 118140960795 + 364504 * 2 ^ 59
def prefixEnd_364504 : Nat := 4983230072969 + 3 ^ 40 * 364504 * 2
def baseEnd_364504 : Nat := 124777168324364740082455

theorem tailTrace_364504 : CollatzResearch.WordTrace tailWord_364504 prefixEnd_364504 124777168324364740082455 := by
  unfold tailWord_364504
  simp only [CollatzResearch.WordTrace]
  refine ⟨6647276535735867586074283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8863035380981156781432377 6647276535735867586074283)
  ·
    refine ⟨9970914803603801379111425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6647276535735867586074283 9970914803603801379111425)
    ·
      refine ⟨7478186102702851034333569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9970914803603801379111425 7478186102702851034333569)
      ·
        refine ⟨5608639577027138275750177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7478186102702851034333569 5608639577027138275750177)
        ·
          refine ⟨4206479682770353706812633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5608639577027138275750177 4206479682770353706812633)
          ·
            refine ⟨3154859762077765280109475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4206479682770353706812633 3154859762077765280109475)
            ·
              refine ⟨4732289643116647920164213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3154859762077765280109475 4732289643116647920164213)
              ·
                refine ⟨443652154042185742515395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4732289643116647920164213 443652154042185742515395)
                ·
                  refine ⟨665478231063278613773093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443652154042185742515395 665478231063278613773093)
                  ·
                    refine ⟨124777168324364740082455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665478231063278613773093 124777168324364740082455)
                    ·
                      rfl

theorem cell22_364504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 5, 1, 4].length) (baseStart_364504 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364504 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364504 prefixEnd_364504 := by exact prefixLift 364504
  have htrace : WordTrace (prefixWord ++ tailWord_364504) baseStart_364504 baseEnd_364504 := by
    simpa [prefixWord, tailWord_364504, baseEnd_364504] using wordTrace_append hprefix tailTrace_364504
  have hstable : (prefixWord ++ tailWord_364504).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364504).length < 2 ^ (prefixWord ++ tailWord_364504).sum := by decide
  have hdescent : baseEnd_364504 < baseStart_364504 := by decide
  rcases family_descends (prefixWord ++ tailWord_364504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364525 : List Nat := [1, 5, 1, 4, 1, 2, 2, 1, 5]
def baseStart_364525 : Nat := 118140960795 + 364525 * 2 ^ 59
def prefixEnd_364525 : Nat := 4983230072969 + 3 ^ 40 * 364525 * 2
def baseEnd_364525 : Nat := 41594785684509228435797

theorem tailTrace_364525 : CollatzResearch.WordTrace tailWord_364525 prefixEnd_364525 41594785684509228435797 := by
  unfold tailWord_364525
  simp only [CollatzResearch.WordTrace]
  refine ⟨13295319004395655758663029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8863546002930437172442019 13295319004395655758663029)
  ·
    refine ⟨1246436156662092727374659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13295319004395655758663029 1246436156662092727374659)
    ·
      refine ⟨1869654234993139091061989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1246436156662092727374659 1869654234993139091061989)
      ·
        refine ⟨350560169061213579574123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1869654234993139091061989 350560169061213579574123)
        ·
          refine ⟨525840253591820369361185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350560169061213579574123 525840253591820369361185)
          ·
            refine ⟨394380190193865277020889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 525840253591820369361185 394380190193865277020889)
            ·
              refine ⟨295785142645398957765667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 394380190193865277020889 295785142645398957765667)
              ·
                refine ⟨443677713968098436648501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 295785142645398957765667 443677713968098436648501)
                ·
                  refine ⟨41594785684509228435797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443677713968098436648501 41594785684509228435797)
                  ·
                    rfl

theorem cell22_364525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 2, 2, 1, 5].length) (baseStart_364525 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364525 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364525 prefixEnd_364525 := by exact prefixLift 364525
  have htrace : WordTrace (prefixWord ++ tailWord_364525) baseStart_364525 baseEnd_364525 := by
    simpa [prefixWord, tailWord_364525, baseEnd_364525] using wordTrace_append hprefix tailTrace_364525
  have hstable : (prefixWord ++ tailWord_364525).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364525).length < 2 ^ (prefixWord ++ tailWord_364525).sum := by decide
  have hdescent : baseEnd_364525 < baseStart_364525 := by decide
  rcases family_descends (prefixWord ++ tailWord_364525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364549 : List Nat := [1, 3, 1, 1, 2, 4, 1, 3, 2, 4]
def baseStart_364549 : Nat := 118140960795 + 364549 * 2 ^ 59
def prefixEnd_364549 : Nat := 4983230072969 + 3 ^ 40 * 364549 * 2
def baseEnd_364549 : Nat := 124792572743999622707317

theorem tailTrace_364549 : CollatzResearch.WordTrace tailWord_364549 prefixEnd_364549 124792572743999622707317 := by
  unfold tailWord_364549
  simp only [CollatzResearch.WordTrace]
  refine ⟨13296194356308707857536701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8864129570872471905024467 13296194356308707857536701)
  ·
    refine ⟨4986072883615765446576263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13296194356308707857536701 4986072883615765446576263)
    ·
      refine ⟨7479109325423648169864395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4986072883615765446576263 7479109325423648169864395)
      ·
        refine ⟨11218663988135472254796593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7479109325423648169864395 11218663988135472254796593)
        ·
          refine ⟨8413997991101604191097445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11218663988135472254796593 8413997991101604191097445)
          ·
            refine ⟨1577624623331550785830771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8413997991101604191097445 1577624623331550785830771)
            ·
              refine ⟨2366436934997326178746157, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577624623331550785830771 2366436934997326178746157)
              ·
                refine ⟨887413850623997317029809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2366436934997326178746157 887413850623997317029809)
                ·
                  refine ⟨665560387967997987772357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 887413850623997317029809 665560387967997987772357)
                  ·
                    refine ⟨124792572743999622707317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665560387967997987772357 124792572743999622707317)
                    ·
                      rfl

theorem cell22_364549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 3, 2, 4].length) (baseStart_364549 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364549 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364549 prefixEnd_364549 := by exact prefixLift 364549
  have htrace : WordTrace (prefixWord ++ tailWord_364549) baseStart_364549 baseEnd_364549 := by
    simpa [prefixWord, tailWord_364549, baseEnd_364549] using wordTrace_append hprefix tailTrace_364549
  have hstable : (prefixWord ++ tailWord_364549).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364549).length < 2 ^ (prefixWord ++ tailWord_364549).sum := by decide
  have hdescent : baseEnd_364549 < baseStart_364549 := by decide
  rcases family_descends (prefixWord ++ tailWord_364549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364626 : List Nat := [3, 2, 2, 1, 4, 1, 1, 1, 7]
def baseStart_364626 : Nat := 118140960795 + 364626 * 2 ^ 59
def prefixEnd_364626 : Nat := 4983230072969 + 3 ^ 40 * 364626 * 2
def baseEnd_364626 : Nat := 41606310472532362844027

theorem tailTrace_364626 : CollatzResearch.WordTrace tailWord_364626 prefixEnd_364626 41606310472532362844027 := by
  unfold tailWord_364626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3324750694257437502022433, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8866001851353166672059821 3324750694257437502022433)
  ·
    refine ⟨2493563020693078126516825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3324750694257437502022433 2493563020693078126516825)
    ·
      refine ⟨1870172265519808594887619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2493563020693078126516825 1870172265519808594887619)
      ·
        refine ⟨2805258398279712892331429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1870172265519808594887619 2805258398279712892331429)
        ·
          refine ⟨525985949677446167312143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2805258398279712892331429 525985949677446167312143)
          ·
            refine ⟨788978924516169250968215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 525985949677446167312143 788978924516169250968215)
            ·
              refine ⟨1183468386774253876452323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 788978924516169250968215 1183468386774253876452323)
              ·
                refine ⟨1775202580161380814678485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1183468386774253876452323 1775202580161380814678485)
                ·
                  refine ⟨41606310472532362844027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1775202580161380814678485 41606310472532362844027)
                  ·
                    rfl

theorem cell22_364626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 1, 7].length) (baseStart_364626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364626 prefixEnd_364626 := by exact prefixLift 364626
  have htrace : WordTrace (prefixWord ++ tailWord_364626) baseStart_364626 baseEnd_364626 := by
    simpa [prefixWord, tailWord_364626, baseEnd_364626] using wordTrace_append hprefix tailTrace_364626
  have hstable : (prefixWord ++ tailWord_364626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364626).length < 2 ^ (prefixWord ++ tailWord_364626).sum := by decide
  have hdescent : baseEnd_364626 < baseStart_364626 := by decide
  rcases family_descends (prefixWord ++ tailWord_364626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364630 : List Nat := [5, 2, 2, 1, 1, 1, 1, 3, 3, 3]
def baseStart_364630 : Nat := 118140960795 + 364630 * 2 ^ 59
def prefixEnd_364630 : Nat := 4983230072969 + 3 ^ 40 * 364630 * 2
def baseEnd_364630 : Nat := 124820300699342411432069

theorem tailTrace_364630 : CollatzResearch.WordTrace tailWord_364630 prefixEnd_364630 124820300699342411432069 := by
  unfold tailWord_364630
  simp only [CollatzResearch.WordTrace]
  refine ⟨831196791813453668202209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8866099112676839127490229 831196791813453668202209)
  ·
    refine ⟨623397593860090251151657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 831196791813453668202209 623397593860090251151657)
    ·
      refine ⟨467548195395067688363743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 623397593860090251151657 467548195395067688363743)
      ·
        refine ⟨701322293092601532545615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467548195395067688363743 701322293092601532545615)
        ·
          refine ⟨1051983439638902298818423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701322293092601532545615 1051983439638902298818423)
          ·
            refine ⟨1577975159458353448227635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1051983439638902298818423 1577975159458353448227635)
            ·
              refine ⟨2366962739187530172341453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1577975159458353448227635 2366962739187530172341453)
              ·
                refine ⟨887611027195323814628045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2366962739187530172341453 887611027195323814628045)
                ·
                  refine ⟨332854135198246430485517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887611027195323814628045 332854135198246430485517)
                  ·
                    refine ⟨124820300699342411432069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332854135198246430485517 124820300699342411432069)
                    ·
                      rfl

theorem cell22_364630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 1, 1, 3, 3, 3].length) (baseStart_364630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364630 prefixEnd_364630 := by exact prefixLift 364630
  have htrace : WordTrace (prefixWord ++ tailWord_364630) baseStart_364630 baseEnd_364630 := by
    simpa [prefixWord, tailWord_364630, baseEnd_364630] using wordTrace_append hprefix tailTrace_364630
  have hstable : (prefixWord ++ tailWord_364630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364630).length < 2 ^ (prefixWord ++ tailWord_364630).sum := by decide
  have hdescent : baseEnd_364630 < baseStart_364630 := by decide
  rcases family_descends (prefixWord ++ tailWord_364630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364639 : List Nat := [1, 1, 2, 3, 1, 1, 2, 4, 3, 4]
def baseStart_364639 : Nat := 118140960795 + 364639 * 2 ^ 59
def prefixEnd_364639 : Nat := 4983230072969 + 3 ^ 40 * 364639 * 2
def baseEnd_364639 : Nat := 124823381583269387957041

theorem tailTrace_364639 : CollatzResearch.WordTrace tailWord_364639 prefixEnd_364639 124823381583269387957041 := by
  unfold tailWord_364639
  simp only [CollatzResearch.WordTrace]
  refine ⟨13299476925982653228312971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8866317950655102152208647 13299476925982653228312971)
  ·
    refine ⟨19949215388973979842469457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13299476925982653228312971 19949215388973979842469457)
    ·
      refine ⟨14961911541730484881852093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19949215388973979842469457 14961911541730484881852093)
      ·
        refine ⟨5610716828148931830694535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14961911541730484881852093 5610716828148931830694535)
        ·
          refine ⟨8416075242223397746041803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5610716828148931830694535 8416075242223397746041803)
          ·
            refine ⟨12624112863335096619062705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8416075242223397746041803 12624112863335096619062705)
            ·
              refine ⟨9468084647501322464297029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12624112863335096619062705 9468084647501322464297029)
              ·
                refine ⟨1775265871406497962055693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9468084647501322464297029 1775265871406497962055693)
                ·
                  refine ⟨665724701777436735770885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1775265871406497962055693 665724701777436735770885)
                  ·
                    refine ⟨124823381583269387957041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665724701777436735770885 124823381583269387957041)
                    ·
                      rfl

theorem cell22_364639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 4, 3, 4].length) (baseStart_364639 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364639 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364639 prefixEnd_364639 := by exact prefixLift 364639
  have htrace : WordTrace (prefixWord ++ tailWord_364639) baseStart_364639 baseEnd_364639 := by
    simpa [prefixWord, tailWord_364639, baseEnd_364639] using wordTrace_append hprefix tailTrace_364639
  have hstable : (prefixWord ++ tailWord_364639).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364639).length < 2 ^ (prefixWord ++ tailWord_364639).sum := by decide
  have hdescent : baseEnd_364639 < baseStart_364639 := by decide
  rcases family_descends (prefixWord ++ tailWord_364639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364656 : List Nat := [2, 1, 1, 1, 5, 2, 1, 4, 1, 4]
def baseStart_364656 : Nat := 118140960795 + 364656 * 2 ^ 59
def prefixEnd_364656 : Nat := 4983230072969 + 3 ^ 40 * 364656 * 2
def baseEnd_364656 : Nat := 124829201030687010281989

theorem tailTrace_364656 : CollatzResearch.WordTrace tailWord_364656 prefixEnd_364656 124829201030687010281989 := by
  unfold tailWord_364656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650048483460532565840911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8866731311280710087787881 6650048483460532565840911)
  ·
    refine ⟨9975072725190798848761367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6650048483460532565840911 9975072725190798848761367)
    ·
      refine ⟨14962609087786198273142051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975072725190798848761367 14962609087786198273142051)
      ·
        refine ⟨22443913631679297409713077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14962609087786198273142051 22443913631679297409713077)
        ·
          refine ⟨2104116902969934132160601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 22443913631679297409713077 2104116902969934132160601)
          ·
            refine ⟨1578087677227450599120451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2104116902969934132160601 1578087677227450599120451)
            ·
              refine ⟨2367131515841175898680677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1578087677227450599120451 2367131515841175898680677)
              ·
                refine ⟨443837159220220481002627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2367131515841175898680677 443837159220220481002627)
                ·
                  refine ⟨665755738830330721503941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 443837159220220481002627 665755738830330721503941)
                  ·
                    refine ⟨124829201030687010281989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 665755738830330721503941 124829201030687010281989)
                    ·
                      rfl

theorem cell22_364656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 4, 1, 4].length) (baseStart_364656 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364656 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364656 prefixEnd_364656 := by exact prefixLift 364656
  have htrace : WordTrace (prefixWord ++ tailWord_364656) baseStart_364656 baseEnd_364656 := by
    simpa [prefixWord, tailWord_364656, baseEnd_364656] using wordTrace_append hprefix tailTrace_364656
  have hstable : (prefixWord ++ tailWord_364656).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364656).length < 2 ^ (prefixWord ++ tailWord_364656).sum := by decide
  have hdescent : baseEnd_364656 < baseStart_364656 := by decide
  rcases family_descends (prefixWord ++ tailWord_364656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364688 : List Nat := [2, 1, 1, 1, 1, 1, 9, 2, 4]
def baseStart_364688 : Nat := 118140960795 + 364688 * 2 ^ 59
def prefixEnd_364688 : Nat := 4983230072969 + 3 ^ 40 * 364688 * 2
def baseEnd_364688 : Nat := 41613385094883197827297

theorem tailTrace_364688 : CollatzResearch.WordTrace tailWord_364688 prefixEnd_364688 41613385094883197827297 := by
  unfold tailWord_364688
  simp only [CollatzResearch.WordTrace]
  refine ⟨6650632051402567298423359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8867509401870089731231145 6650632051402567298423359)
  ·
    refine ⟨9975948077103850947635039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6650632051402567298423359 9975948077103850947635039)
    ·
      refine ⟨14963922115655776421452559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9975948077103850947635039 14963922115655776421452559)
      ·
        refine ⟨22445883173483664632178839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14963922115655776421452559 22445883173483664632178839)
        ·
          refine ⟨33668824760225496948268259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22445883173483664632178839 33668824760225496948268259)
          ·
            refine ⟨50503237140338245422402389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33668824760225496948268259 50503237140338245422402389)
            ·
              refine ⟨295917405119169406771889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 50503237140338245422402389 295917405119169406771889)
              ·
                refine ⟨221938053839377055078917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 295917405119169406771889 221938053839377055078917)
                ·
                  refine ⟨41613385094883197827297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 221938053839377055078917 41613385094883197827297)
                  ·
                    rfl

theorem cell22_364688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 9, 2, 4].length) (baseStart_364688 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364688 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364688 prefixEnd_364688 := by exact prefixLift 364688
  have htrace : WordTrace (prefixWord ++ tailWord_364688) baseStart_364688 baseEnd_364688 := by
    simpa [prefixWord, tailWord_364688, baseEnd_364688] using wordTrace_append hprefix tailTrace_364688
  have hstable : (prefixWord ++ tailWord_364688).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364688).length < 2 ^ (prefixWord ++ tailWord_364688).sum := by decide
  have hdescent : baseEnd_364688 < baseStart_364688 := by decide
  rcases family_descends (prefixWord ++ tailWord_364688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364694 : List Nat := [5, 3, 2, 1, 1, 1, 1, 3, 5]
def baseStart_364694 : Nat := 118140960795 + 364694 * 2 ^ 59
def prefixEnd_364694 : Nat := 4983230072969 + 3 ^ 40 * 364694 * 2
def baseEnd_364694 : Nat := 41614069735755859277291

theorem tailTrace_364694 : CollatzResearch.WordTrace tailWord_364694 prefixEnd_364694 41614069735755859277291 := by
  unfold tailWord_364694
  simp only [CollatzResearch.WordTrace]
  refine ⟨831342683798962351347821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8867655293855598414376757 831342683798962351347821)
  ·
    refine ⟨311753506424610881755433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 831342683798962351347821 311753506424610881755433)
    ·
      refine ⟨233815129818458161316575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 311753506424610881755433 233815129818458161316575)
      ·
        refine ⟨350722694727687241974863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 233815129818458161316575 350722694727687241974863)
        ·
          refine ⟨526084042091530862962295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 350722694727687241974863 526084042091530862962295)
          ·
            refine ⟨789126063137296294443443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526084042091530862962295 789126063137296294443443)
            ·
              refine ⟨1183689094705944441665165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789126063137296294443443 1183689094705944441665165)
              ·
                refine ⟨443883410514729165624437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183689094705944441665165 443883410514729165624437)
                ·
                  refine ⟨41614069735755859277291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443883410514729165624437 41614069735755859277291)
                  ·
                    rfl

theorem cell22_364694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 2, 1, 1, 1, 1, 3, 5].length) (baseStart_364694 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364694 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364694 prefixEnd_364694 := by exact prefixLift 364694
  have htrace : WordTrace (prefixWord ++ tailWord_364694) baseStart_364694 baseEnd_364694 := by
    simpa [prefixWord, tailWord_364694, baseEnd_364694] using wordTrace_append hprefix tailTrace_364694
  have hstable : (prefixWord ++ tailWord_364694).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364694).length < 2 ^ (prefixWord ++ tailWord_364694).sum := by decide
  have hdescent : baseEnd_364694 < baseStart_364694 := by decide
  rcases family_descends (prefixWord ++ tailWord_364694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364737 : List Nat := [1, 2, 6, 1, 2, 1, 2, 2, 2, 3]
def baseStart_364737 : Nat := 118140960795 + 364737 * 2 ^ 59
def prefixEnd_364737 : Nat := 4983230072969 + 3 ^ 40 * 364737 * 2
def baseEnd_364737 : Nat := 124856928986029799006741

theorem tailTrace_364737 : CollatzResearch.WordTrace tailWord_364737 prefixEnd_364737 124856928986029799006741 := by
  unfold tailWord_364737
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303051279627615965380465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8868700853085077310253643 13303051279627615965380465)
  ·
    refine ⟨9977288459720711974035349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13303051279627615965380465 9977288459720711974035349)
    ·
      refine ⟨467685396549408373782907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9977288459720711974035349 467685396549408373782907)
      ·
        refine ⟨701528094824112560674361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 467685396549408373782907 701528094824112560674361)
        ·
          refine ⟨526146071118084420505771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 701528094824112560674361 526146071118084420505771)
          ·
            refine ⟨789219106677126630758657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 526146071118084420505771 789219106677126630758657)
            ·
              refine ⟨591914330007844973068993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 789219106677126630758657 591914330007844973068993)
              ·
                refine ⟨443935747505883729801745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 591914330007844973068993 443935747505883729801745)
                ·
                  refine ⟨332951810629412797351309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 443935747505883729801745 332951810629412797351309)
                  ·
                    refine ⟨124856928986029799006741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332951810629412797351309 124856928986029799006741)
                    ·
                      rfl

theorem cell22_364737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 2, 2, 2, 3].length) (baseStart_364737 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364737 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364737 prefixEnd_364737 := by exact prefixLift 364737
  have htrace : WordTrace (prefixWord ++ tailWord_364737) baseStart_364737 baseEnd_364737 := by
    simpa [prefixWord, tailWord_364737, baseEnd_364737] using wordTrace_append hprefix tailTrace_364737
  have hstable : (prefixWord ++ tailWord_364737).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364737).length < 2 ^ (prefixWord ++ tailWord_364737).sum := by decide
  have hdescent : baseEnd_364737 < baseStart_364737 := by decide
  rcases family_descends (prefixWord ++ tailWord_364737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364761 : List Nat := [1, 2, 1, 2, 3, 1, 4, 3, 5]
def baseStart_364761 : Nat := 118140960795 + 364761 * 2 ^ 59
def prefixEnd_364761 : Nat := 4983230072969 + 3 ^ 40 * 364761 * 2
def baseEnd_364761 : Nat := 41621714892167245468889

theorem tailTrace_364761 : CollatzResearch.WordTrace tailWord_364761 prefixEnd_364761 41621714892167245468889 := by
  unfold tailWord_364761
  simp only [CollatzResearch.WordTrace]
  refine ⟨13303926631540668064254137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8869284421027112042836091 13303926631540668064254137)
  ·
    refine ⟨9977944973655501048190603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13303926631540668064254137 9977944973655501048190603)
    ·
      refine ⟨14966917460483251572285905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9977944973655501048190603 14966917460483251572285905)
      ·
        refine ⟨11225188095362438679214429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14966917460483251572285905 11225188095362438679214429)
        ·
          refine ⟨4209445535760914504705411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11225188095362438679214429 4209445535760914504705411)
          ·
            refine ⟨6314168303641371757058117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4209445535760914504705411 6314168303641371757058117)
            ·
              refine ⟨1183906556932757204448397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6314168303641371757058117 1183906556932757204448397)
              ·
                refine ⟨443964958849783951668149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1183906556932757204448397 443964958849783951668149)
                ·
                  refine ⟨41621714892167245468889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 443964958849783951668149 41621714892167245468889)
                  ·
                    rfl

theorem cell22_364761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 4, 3, 5].length) (baseStart_364761 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364761 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364761 prefixEnd_364761 := by exact prefixLift 364761
  have htrace : WordTrace (prefixWord ++ tailWord_364761) baseStart_364761 baseEnd_364761 := by
    simpa [prefixWord, tailWord_364761, baseEnd_364761] using wordTrace_append hprefix tailTrace_364761
  have hstable : (prefixWord ++ tailWord_364761).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364761).length < 2 ^ (prefixWord ++ tailWord_364761).sum := by decide
  have hdescent : baseEnd_364761 < baseStart_364761 := by decide
  rcases family_descends (prefixWord ++ tailWord_364761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364765 : List Nat := [1, 4, 3, 2, 1, 2, 1, 2, 3, 3]
def baseStart_364765 : Nat := 118140960795 + 364765 * 2 ^ 59
def prefixEnd_364765 : Nat := 4983230072969 + 3 ^ 40 * 364765 * 2
def baseEnd_364765 : Nat := 124866513958247059306655

theorem tailTrace_364765 : CollatzResearch.WordTrace tailWord_364765 prefixEnd_364765 124866513958247059306655 := by
  unfold tailWord_364765
  simp only [CollatzResearch.WordTrace]
  refine ⟨13304072523526176747399749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8869381682350784498266499 13304072523526176747399749)
  ·
    refine ⟨2494513598161158140137453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13304072523526176747399749 2494513598161158140137453)
    ·
      refine ⟨935442599310434302551545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2494513598161158140137453 935442599310434302551545)
      ·
        refine ⟨701581949482825726913659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 935442599310434302551545 701581949482825726913659)
        ·
          refine ⟨1052372924224238590370489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701581949482825726913659 1052372924224238590370489)
          ·
            refine ⟨789279693168178942777867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052372924224238590370489 789279693168178942777867)
            ·
              refine ⟨1183919539752268414166801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789279693168178942777867 1183919539752268414166801)
              ·
                refine ⟨887939654814201310625101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1183919539752268414166801 887939654814201310625101)
                ·
                  refine ⟨332977370555325491484413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 887939654814201310625101 332977370555325491484413)
                  ·
                    refine ⟨124866513958247059306655, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 332977370555325491484413 124866513958247059306655)
                    ·
                      rfl

theorem cell22_364765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 2, 1, 2, 3, 3].length) (baseStart_364765 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364765 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364765 prefixEnd_364765 := by exact prefixLift 364765
  have htrace : WordTrace (prefixWord ++ tailWord_364765) baseStart_364765 baseEnd_364765 := by
    simpa [prefixWord, tailWord_364765, baseEnd_364765] using wordTrace_append hprefix tailTrace_364765
  have hstable : (prefixWord ++ tailWord_364765).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364765).length < 2 ^ (prefixWord ++ tailWord_364765).sum := by decide
  have hdescent : baseEnd_364765 < baseStart_364765 := by decide
  rcases family_descends (prefixWord ++ tailWord_364765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364853 : List Nat := [1, 3, 3, 1, 2, 1, 3, 2, 2, 4]
def baseStart_364853 : Nat := 118140960795 + 364853 * 2 ^ 59
def prefixEnd_364853 : Nat := 4983230072969 + 3 ^ 40 * 364853 * 2
def baseEnd_364853 : Nat := 124896638156644163106385

theorem tailTrace_364853 : CollatzResearch.WordTrace tailWord_364853 prefixEnd_364853 124896638156644163106385 := by
  unfold tailWord_364853
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307282147207367776603213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8871521431471578517735475 13307282147207367776603213)
  ·
    refine ⟨4990230805202762916226205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13307282147207367776603213 4990230805202762916226205)
    ·
      refine ⟨1871336551951036093584827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4990230805202762916226205 1871336551951036093584827)
      ·
        refine ⟨2807004827926554140377241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1871336551951036093584827 2807004827926554140377241)
        ·
          refine ⟨2105253620944915605282931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2807004827926554140377241 2105253620944915605282931)
          ·
            refine ⟨3157880431417373407924397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2105253620944915605282931 3157880431417373407924397)
            ·
              refine ⟨1184205161781515027971649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3157880431417373407924397 1184205161781515027971649)
              ·
                refine ⟨888153871336136270978737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1184205161781515027971649 888153871336136270978737)
                ·
                  refine ⟨666115403502102203234053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 888153871336136270978737 666115403502102203234053)
                  ·
                    refine ⟨124896638156644163106385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 666115403502102203234053 124896638156644163106385)
                    ·
                      rfl

theorem cell22_364853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 2, 2, 4].length) (baseStart_364853 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364853 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364853 prefixEnd_364853 := by exact prefixLift 364853
  have htrace : WordTrace (prefixWord ++ tailWord_364853) baseStart_364853 baseEnd_364853 := by
    simpa [prefixWord, tailWord_364853, baseEnd_364853] using wordTrace_append hprefix tailTrace_364853
  have hstable : (prefixWord ++ tailWord_364853).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364853).length < 2 ^ (prefixWord ++ tailWord_364853).sum := by decide
  have hdescent : baseEnd_364853 < baseStart_364853 := by decide
  rcases family_descends (prefixWord ++ tailWord_364853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364857 : List Nat := [1, 2, 1, 6, 1, 2, 3, 2, 4]
def baseStart_364857 : Nat := 118140960795 + 364857 * 2 ^ 59
def prefixEnd_364857 : Nat := 4983230072969 + 3 ^ 40 * 364857 * 2
def baseEnd_364857 : Nat := 41632669146129828668791

theorem tailTrace_364857 : CollatzResearch.WordTrace tailWord_364857 prefixEnd_364857 41632669146129828668791 := by
  unfold tailWord_364857
  simp only [CollatzResearch.WordTrace]
  refine ⟨13307428039192876459748825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8871618692795250973165883 13307428039192876459748825)
  ·
    refine ⟨9980571029394657344811619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13307428039192876459748825 9980571029394657344811619)
    ·
      refine ⟨14970856544091986017217429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9980571029394657344811619 14970856544091986017217429)
      ·
        refine ⟨701758900504311844557067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14970856544091986017217429 701758900504311844557067)
        ·
          refine ⟨1052638350756467766835601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 701758900504311844557067 1052638350756467766835601)
          ·
            refine ⟨789478763067350825126701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1052638350756467766835601 789478763067350825126701)
            ·
              refine ⟨296054536150256559422513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 789478763067350825126701 296054536150256559422513)
              ·
                refine ⟨222040902112692419566885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296054536150256559422513 222040902112692419566885)
                ·
                  refine ⟨41632669146129828668791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222040902112692419566885 41632669146129828668791)
                  ·
                    rfl

theorem cell22_364857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 3, 2, 4].length) (baseStart_364857 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364857 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364857 prefixEnd_364857 := by exact prefixLift 364857
  have htrace : WordTrace (prefixWord ++ tailWord_364857) baseStart_364857 baseEnd_364857 := by
    simpa [prefixWord, tailWord_364857, baseEnd_364857] using wordTrace_append hprefix tailTrace_364857
  have hstable : (prefixWord ++ tailWord_364857).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364857).length < 2 ^ (prefixWord ++ tailWord_364857).sum := by decide
  have hdescent : baseEnd_364857 < baseStart_364857 := by decide
  rcases family_descends (prefixWord ++ tailWord_364857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364960 : List Nat := [2, 1, 1, 4, 1, 4, 1, 3, 1, 4]
def baseStart_364960 : Nat := 118140960795 + 364960 * 2 ^ 59
def prefixEnd_364960 : Nat := 4983230072969 + 3 ^ 40 * 364960 * 2
def baseEnd_364960 : Nat := 124933266443331550681057

theorem tailTrace_364960 : CollatzResearch.WordTrace tailWord_364960 prefixEnd_364960 124933266443331550681057 := by
  unfold tailWord_364960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6655592378909862525374167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8874123171879816700498889 6655592378909862525374167)
  ·
    refine ⟨9983388568364793788061251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6655592378909862525374167 9983388568364793788061251)
    ·
      refine ⟨14975082852547190682091877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9983388568364793788061251 14975082852547190682091877)
      ·
        refine ⟨2807828034852598252892227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14975082852547190682091877 2807828034852598252892227)
        ·
          refine ⟨4211742052278897379338341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2807828034852598252892227 4211742052278897379338341)
          ·
            refine ⟨789701634802293258625939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4211742052278897379338341 789701634802293258625939)
            ·
              refine ⟨1184552452203439887938909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 789701634802293258625939 1184552452203439887938909)
              ·
                refine ⟨444207169576289957977091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1184552452203439887938909 444207169576289957977091)
                ·
                  refine ⟨666310754364434936965637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 444207169576289957977091 666310754364434936965637)
                  ·
                    refine ⟨124933266443331550681057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 666310754364434936965637 124933266443331550681057)
                    ·
                      rfl

theorem cell22_364960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 4, 1, 3, 1, 4].length) (baseStart_364960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364960 prefixEnd_364960 := by exact prefixLift 364960
  have htrace : WordTrace (prefixWord ++ tailWord_364960) baseStart_364960 baseEnd_364960 := by
    simpa [prefixWord, tailWord_364960, baseEnd_364960] using wordTrace_append hprefix tailTrace_364960
  have hstable : (prefixWord ++ tailWord_364960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364960).length < 2 ^ (prefixWord ++ tailWord_364960).sum := by decide
  have hdescent : baseEnd_364960 < baseStart_364960 := by decide
  rcases family_descends (prefixWord ++ tailWord_364960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_364990 : List Nat := [4, 2, 1, 1, 1, 1, 5, 1, 1, 5]
def baseStart_364990 : Nat := 118140960795 + 364990 * 2 ^ 59
def prefixEnd_364990 : Nat := 4983230072969 + 3 ^ 40 * 364990 * 2
def baseEnd_364990 : Nat := 124943536056421472430965

theorem tailTrace_364990 : CollatzResearch.WordTrace tailWord_364990 prefixEnd_364990 124943536056421472430965 := by
  unfold tailWord_364990
  simp only [CollatzResearch.WordTrace]
  refine ⟨1664034868463880021792553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8874852631807360116226949 1664034868463880021792553)
  ·
    refine ⟨1248026151347910016344415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1664034868463880021792553 1248026151347910016344415)
    ·
      refine ⟨1872039227021865024516623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1248026151347910016344415 1872039227021865024516623)
      ·
        refine ⟨2808058840532797536774935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1872039227021865024516623 2808058840532797536774935)
        ·
          refine ⟨4212088260799196305162403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2808058840532797536774935 4212088260799196305162403)
          ·
            refine ⟨6318132391198794457743605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4212088260799196305162403 6318132391198794457743605)
            ·
              refine ⟨592324911674886980413463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6318132391198794457743605 592324911674886980413463)
              ·
                refine ⟨888487367512330470620195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592324911674886980413463 888487367512330470620195)
                ·
                  refine ⟨1332731051268495705930293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888487367512330470620195 1332731051268495705930293)
                  ·
                    refine ⟨124943536056421472430965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1332731051268495705930293 124943536056421472430965)
                    ·
                      rfl

theorem cell22_364990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 5, 1, 1, 5].length) (baseStart_364990 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_364990 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_364990 prefixEnd_364990 := by exact prefixLift 364990
  have htrace : WordTrace (prefixWord ++ tailWord_364990) baseStart_364990 baseEnd_364990 := by
    simpa [prefixWord, tailWord_364990, baseEnd_364990] using wordTrace_append hprefix tailTrace_364990
  have hstable : (prefixWord ++ tailWord_364990).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_364990).length < 2 ^ (prefixWord ++ tailWord_364990).sum := by decide
  have hdescent : baseEnd_364990 < baseStart_364990 := by decide
  rcases family_descends (prefixWord ++ tailWord_364990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365026 : List Nat := [3, 3, 3, 2, 2, 1, 1, 1, 6]
def baseStart_365026 : Nat := 118140960795 + 365026 * 2 ^ 59
def prefixEnd_365026 : Nat := 4983230072969 + 3 ^ 40 * 365026 * 2
def baseEnd_365026 : Nat := 41651953197376459510285

theorem tailTrace_365026 : CollatzResearch.WordTrace tailWord_365026 prefixEnd_365026 41651953197376459510285 := by
  unfold tailWord_365026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3328397993895154580662733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8875727983720412215100621 3328397993895154580662733)
  ·
    refine ⟨1248149247710682967748525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3328397993895154580662733 1248149247710682967748525)
    ·
      refine ⟨468055967891506112905697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1248149247710682967748525 468055967891506112905697)
      ·
        refine ⟨351041975918629584679273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 468055967891506112905697 351041975918629584679273)
        ·
          refine ⟨263281481938972188509455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351041975918629584679273 263281481938972188509455)
          ·
            refine ⟨394922222908458282764183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263281481938972188509455 394922222908458282764183)
            ·
              refine ⟨592383334362687424146275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 394922222908458282764183 592383334362687424146275)
              ·
                refine ⟨888575001544031136219413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592383334362687424146275 888575001544031136219413)
                ·
                  refine ⟨41651953197376459510285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 888575001544031136219413 41651953197376459510285)
                  ·
                    rfl

theorem cell22_365026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 2, 1, 1, 1, 6].length) (baseStart_365026 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365026 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365026 prefixEnd_365026 := by exact prefixLift 365026
  have htrace : WordTrace (prefixWord ++ tailWord_365026) baseStart_365026 baseEnd_365026 := by
    simpa [prefixWord, tailWord_365026, baseEnd_365026] using wordTrace_append hprefix tailTrace_365026
  have hstable : (prefixWord ++ tailWord_365026).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365026).length < 2 ^ (prefixWord ++ tailWord_365026).sum := by decide
  have hdescent : baseEnd_365026 < baseStart_365026 := by decide
  rcases family_descends (prefixWord ++ tailWord_365026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365125 : List Nat := [1, 3, 1, 1, 1, 5, 2, 2, 1, 5]
def baseStart_365125 : Nat := 118140960795 + 365125 * 2 ^ 59
def prefixEnd_365125 : Nat := 4983230072969 + 3 ^ 40 * 365125 * 2
def baseEnd_365125 : Nat := 124989749315326120305551

theorem tailTrace_365125 : CollatzResearch.WordTrace tailWord_365125 prefixEnd_365125 124989749315326120305551 := by
  unfold tailWord_365125
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317202802221958230504829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8878135201481305487003219 13317202802221958230504829)
  ·
    refine ⟨4993951050833234336439311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13317202802221958230504829 4993951050833234336439311)
    ·
      refine ⟨7490926576249851504658967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4993951050833234336439311 7490926576249851504658967)
      ·
        refine ⟨11236389864374777256988451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7490926576249851504658967 11236389864374777256988451)
        ·
          refine ⟨16854584796562165885482677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11236389864374777256988451 16854584796562165885482677)
          ·
            refine ⟨1580117324677703051764001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16854584796562165885482677 1580117324677703051764001)
            ·
              refine ⟨1185087993508277288823001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1580117324677703051764001 1185087993508277288823001)
              ·
                refine ⟨888815995131207966617251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1185087993508277288823001 888815995131207966617251)
                ·
                  refine ⟨1333223992696811949925877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 888815995131207966617251 1333223992696811949925877)
                  ·
                    refine ⟨124989749315326120305551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1333223992696811949925877 124989749315326120305551)
                    ·
                      rfl

theorem cell22_365125_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 2, 2, 1, 5].length) (baseStart_365125 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365125 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365125 prefixEnd_365125 := by exact prefixLift 365125
  have htrace : WordTrace (prefixWord ++ tailWord_365125) baseStart_365125 baseEnd_365125 := by
    simpa [prefixWord, tailWord_365125, baseEnd_365125] using wordTrace_append hprefix tailTrace_365125
  have hstable : (prefixWord ++ tailWord_365125).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365125).length < 2 ^ (prefixWord ++ tailWord_365125).sum := by decide
  have hdescent : baseEnd_365125 < baseStart_365125 := by decide
  rcases family_descends (prefixWord ++ tailWord_365125) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365127 : List Nat := [1, 1, 4, 1, 4, 1, 1, 5, 4]
def baseStart_365127 : Nat := 118140960795 + 365127 * 2 ^ 59
def prefixEnd_365127 : Nat := 4983230072969 + 3 ^ 40 * 365127 * 2
def baseEnd_365127 : Nat := 41663477985399593918515

theorem tailTrace_365127 : CollatzResearch.WordTrace tailWord_365127 prefixEnd_365127 41663477985399593918515 := by
  unfold tailWord_365127
  simp only [CollatzResearch.WordTrace]
  refine ⟨13317275748214712572077635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8878183832143141714718423 13317275748214712572077635)
  ·
    refine ⟨19975913622322068858116453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13317275748214712572077635 19975913622322068858116453)
    ·
      refine ⟨3745483804185387910896835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19975913622322068858116453 3745483804185387910896835)
      ·
        refine ⟨5618225706278081866345253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3745483804185387910896835 5618225706278081866345253)
        ·
          refine ⟨1053417319927140349939735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5618225706278081866345253 1053417319927140349939735)
          ·
            refine ⟨1580125979890710524909603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1053417319927140349939735 1580125979890710524909603)
            ·
              refine ⟨2370188969836065787364405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1580125979890710524909603 2370188969836065787364405)
              ·
                refine ⟨222205215922131167565413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2370188969836065787364405 222205215922131167565413)
                ·
                  refine ⟨41663477985399593918515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222205215922131167565413 41663477985399593918515)
                  ·
                    rfl

theorem cell22_365127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 4, 1, 1, 5, 4].length) (baseStart_365127 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365127 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365127 prefixEnd_365127 := by exact prefixLift 365127
  have htrace : WordTrace (prefixWord ++ tailWord_365127) baseStart_365127 baseEnd_365127 := by
    simpa [prefixWord, tailWord_365127, baseEnd_365127] using wordTrace_append hprefix tailTrace_365127
  have hstable : (prefixWord ++ tailWord_365127).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365127).length < 2 ^ (prefixWord ++ tailWord_365127).sum := by decide
  have hdescent : baseEnd_365127 < baseStart_365127 := by decide
  rcases family_descends (prefixWord ++ tailWord_365127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365210 : List Nat := [3, 1, 1, 6, 2, 1, 2, 1, 2, 3]
def baseStart_365210 : Nat := 118140960795 + 365210 * 2 ^ 59
def prefixEnd_365210 : Nat := 4983230072969 + 3 ^ 40 * 365210 * 2
def baseEnd_365210 : Nat := 125018846552414231930291

theorem tailTrace_365210 : CollatzResearch.WordTrace tailWord_365210 prefixEnd_365210 125018846552414231930291 := by
  unfold tailWord_365210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3330075751728504436837271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8880202004609345164899389 3330075751728504436837271)
  ·
    refine ⟨4995113627592756655255907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3330075751728504436837271 4995113627592756655255907)
    ·
      refine ⟨7492670441389134982883861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4995113627592756655255907 7492670441389134982883861)
      ·
        refine ⟨351218926940115702322681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 7492670441389134982883861 351218926940115702322681)
        ·
          refine ⟨263414195205086776742011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 351218926940115702322681 263414195205086776742011)
          ·
            refine ⟨395121292807630165113017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 263414195205086776742011 395121292807630165113017)
            ·
              refine ⟨296340969605722623834763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 395121292807630165113017 296340969605722623834763)
              ·
                refine ⟨444511454408583935752145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296340969605722623834763 444511454408583935752145)
                ·
                  refine ⟨333383590806437951814109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 444511454408583935752145 333383590806437951814109)
                  ·
                    refine ⟨125018846552414231930291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333383590806437951814109 125018846552414231930291)
                    ·
                      rfl

theorem cell22_365210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 6, 2, 1, 2, 1, 2, 3].length) (baseStart_365210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365210 prefixEnd_365210 := by exact prefixLift 365210
  have htrace : WordTrace (prefixWord ++ tailWord_365210) baseStart_365210 baseEnd_365210 := by
    simpa [prefixWord, tailWord_365210, baseEnd_365210] using wordTrace_append hprefix tailTrace_365210
  have hstable : (prefixWord ++ tailWord_365210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365210).length < 2 ^ (prefixWord ++ tailWord_365210).sum := by decide
  have hdescent : baseEnd_365210 < baseStart_365210 := by decide
  rcases family_descends (prefixWord ++ tailWord_365210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365305 : List Nat := [1, 2, 1, 3, 1, 1, 1, 2, 1, 9]
def baseStart_365305 : Nat := 118140960795 + 365305 * 2 ^ 59
def prefixEnd_365305 : Nat := 4983230072969 + 3 ^ 40 * 365305 * 2
def baseEnd_365305 : Nat := 125051366993865650804999

theorem tailTrace_365305 : CollatzResearch.WordTrace tailWord_365305 prefixEnd_365305 125051366993865650804999 := by
  unfold tailWord_365305
  simp only [CollatzResearch.WordTrace]
  refine ⟨13323767941569848972057369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8882511961046565981371579 13323767941569848972057369)
  ·
    refine ⟨9992825956177386729043027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13323767941569848972057369 9992825956177386729043027)
    ·
      refine ⟨14989238934266080093564541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9992825956177386729043027 14989238934266080093564541)
      ·
        refine ⟨5620964600349780035086703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14989238934266080093564541 5620964600349780035086703)
        ·
          refine ⟨8431446900524670052630055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5620964600349780035086703 8431446900524670052630055)
          ·
            refine ⟨12647170350787005078945083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8431446900524670052630055 12647170350787005078945083)
            ·
              refine ⟨18970755526180507618417625, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12647170350787005078945083 18970755526180507618417625)
              ·
                refine ⟨14228066644635380713813219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 18970755526180507618417625 14228066644635380713813219)
                ·
                  refine ⟨21342099966953071070719829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14228066644635380713813219 21342099966953071070719829)
                  ·
                    refine ⟨125051366993865650804999, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 21342099966953071070719829 125051366993865650804999)
                    ·
                      rfl

theorem cell22_365305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 2, 1, 9].length) (baseStart_365305 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365305 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365305 prefixEnd_365305 := by exact prefixLift 365305
  have htrace : WordTrace (prefixWord ++ tailWord_365305) baseStart_365305 baseEnd_365305 := by
    simpa [prefixWord, tailWord_365305, baseEnd_365305] using wordTrace_append hprefix tailTrace_365305
  have hstable : (prefixWord ++ tailWord_365305).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365305).length < 2 ^ (prefixWord ++ tailWord_365305).sum := by decide
  have hdescent : baseEnd_365305 < baseStart_365305 := by decide
  rcases family_descends (prefixWord ++ tailWord_365305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365352 : List Nat := [2, 1, 5, 1, 1, 1, 1, 1, 9]
def baseStart_365352 : Nat := 118140960795 + 365352 * 2 ^ 59
def prefixEnd_365352 : Nat := 4983230072969 + 3 ^ 40 * 365352 * 2
def baseEnd_365352 : Nat := 41689152018124398293285

theorem tailTrace_365352 : CollatzResearch.WordTrace tailWord_365352 prefixEnd_365352 41689152018124398293285 := by
  unfold tailWord_365352
  simp only [CollatzResearch.WordTrace]
  refine ⟨6662741086199787999509155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8883654781599717332678873 6662741086199787999509155)
  ·
    refine ⟨9994111629299681999263733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6662741086199787999509155 9994111629299681999263733)
    ·
      refine ⟨936947965246845187430975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9994111629299681999263733 936947965246845187430975)
      ·
        refine ⟨1405421947870267781146463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 936947965246845187430975 1405421947870267781146463)
        ·
          refine ⟨2108132921805401671719695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1405421947870267781146463 2108132921805401671719695)
          ·
            refine ⟨3162199382708102507579543, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108132921805401671719695 3162199382708102507579543)
            ·
              refine ⟨4743299074062153761369315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3162199382708102507579543 4743299074062153761369315)
              ·
                refine ⟨7114948611093230642053973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4743299074062153761369315 7114948611093230642053973)
                ·
                  refine ⟨41689152018124398293285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 7114948611093230642053973 41689152018124398293285)
                  ·
                    rfl

theorem cell22_365352_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 1, 1, 1, 9].length) (baseStart_365352 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365352 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365352 prefixEnd_365352 := by exact prefixLift 365352
  have htrace : WordTrace (prefixWord ++ tailWord_365352) baseStart_365352 baseEnd_365352 := by
    simpa [prefixWord, tailWord_365352, baseEnd_365352] using wordTrace_append hprefix tailTrace_365352
  have hstable : (prefixWord ++ tailWord_365352).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365352).length < 2 ^ (prefixWord ++ tailWord_365352).sum := by decide
  have hdescent : baseEnd_365352 < baseStart_365352 := by decide
  rcases family_descends (prefixWord ++ tailWord_365352) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365373 : List Nat := [1, 4, 1, 4, 2, 2, 1, 1, 3, 3]
def baseStart_365373 : Nat := 118140960795 + 365373 * 2 ^ 59
def prefixEnd_365373 : Nat := 4983230072969 + 3 ^ 40 * 365373 * 2
def baseEnd_365373 : Nat := 125074644783536140104791

theorem tailTrace_365373 : CollatzResearch.WordTrace tailWord_365373 prefixEnd_365373 125074644783536140104791 := by
  unfold tailWord_365373
  simp only [CollatzResearch.WordTrace]
  refine ⟨13326248105323496585532773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8884165403548997723688515 13326248105323496585532773)
  ·
    refine ⟨2498671519748155609787395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 13326248105323496585532773 2498671519748155609787395)
    ·
      refine ⟨3748007279622233414681093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2498671519748155609787395 3748007279622233414681093)
      ·
        refine ⟨702751364929168765252705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3748007279622233414681093 702751364929168765252705)
        ·
          refine ⟨527063523696876573939529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 702751364929168765252705 527063523696876573939529)
          ·
            refine ⟨395297642772657430454647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 527063523696876573939529 395297642772657430454647)
            ·
              refine ⟨592946464158986145681971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395297642772657430454647 592946464158986145681971)
              ·
                refine ⟨889419696238479218522957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 592946464158986145681971 889419696238479218522957)
                ·
                  refine ⟨333532386089429706946109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 889419696238479218522957 333532386089429706946109)
                  ·
                    refine ⟨125074644783536140104791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333532386089429706946109 125074644783536140104791)
                    ·
                      rfl

theorem cell22_365373_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 2, 1, 1, 3, 3].length) (baseStart_365373 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365373 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365373 prefixEnd_365373 := by exact prefixLift 365373
  have htrace : WordTrace (prefixWord ++ tailWord_365373) baseStart_365373 baseEnd_365373 := by
    simpa [prefixWord, tailWord_365373, baseEnd_365373] using wordTrace_append hprefix tailTrace_365373
  have hstable : (prefixWord ++ tailWord_365373).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365373).length < 2 ^ (prefixWord ++ tailWord_365373).sum := by decide
  have hdescent : baseEnd_365373 < baseStart_365373 := by decide
  rcases family_descends (prefixWord ++ tailWord_365373) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365397 : List Nat := [1, 3, 2, 2, 2, 1, 2, 1, 8]
def baseStart_365397 : Nat := 118140960795 + 365397 * 2 ^ 59
def prefixEnd_365397 : Nat := 4983230072969 + 3 ^ 40 * 365397 * 2
def baseEnd_365397 : Nat := 41694286824669359168239

theorem tailTrace_365397 : CollatzResearch.WordTrace tailWord_365397 prefixEnd_365397 41694286824669359168239 := by
  unfold tailWord_365397
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327123457236548684406445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8884748971491032456270963 13327123457236548684406445)
  ·
    refine ⟨4997671296463705756652417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13327123457236548684406445 4997671296463705756652417)
    ·
      refine ⟨3748253472347779317489313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4997671296463705756652417 3748253472347779317489313)
      ·
        refine ⟨2811190104260834488116985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3748253472347779317489313 2811190104260834488116985)
        ·
          refine ⟨2108392578195625866087739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2811190104260834488116985 2108392578195625866087739)
          ·
            refine ⟨3162588867293438799131609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2108392578195625866087739 3162588867293438799131609)
            ·
              refine ⟨2371941650470079099348707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3162588867293438799131609 2371941650470079099348707)
              ·
                refine ⟨3557912475705118649023061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2371941650470079099348707 3557912475705118649023061)
                ·
                  refine ⟨41694286824669359168239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 3557912475705118649023061 41694286824669359168239)
                  ·
                    rfl

theorem cell22_365397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 2, 1, 8].length) (baseStart_365397 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365397 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365397 prefixEnd_365397 := by exact prefixLift 365397
  have htrace : WordTrace (prefixWord ++ tailWord_365397) baseStart_365397 baseEnd_365397 := by
    simpa [prefixWord, tailWord_365397, baseEnd_365397] using wordTrace_append hprefix tailTrace_365397
  have hstable : (prefixWord ++ tailWord_365397).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365397).length < 2 ^ (prefixWord ++ tailWord_365397).sum := by decide
  have hdescent : baseEnd_365397 < baseStart_365397 := by decide
  rcases family_descends (prefixWord ++ tailWord_365397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365399 : List Nat := [1, 1, 3, 2, 4, 2, 1, 1, 3, 4]
def baseStart_365399 : Nat := 118140960795 + 365399 * 2 ^ 59
def prefixEnd_365399 : Nat := 4983230072969 + 3 ^ 40 * 365399 * 2
def baseEnd_365399 : Nat := 125083545114880738954711

theorem tailTrace_365399 : CollatzResearch.WordTrace tailWord_365399 prefixEnd_365399 125083545114880738954711 := by
  unfold tailWord_365399
  simp only [CollatzResearch.WordTrace]
  refine ⟨13327196403229303025979251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8884797602152868683986167 13327196403229303025979251)
  ·
    refine ⟨19990794604843954538968877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13327196403229303025979251 19990794604843954538968877)
    ·
      refine ⟨7496547976816482952113329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19990794604843954538968877 7496547976816482952113329)
      ·
        refine ⟨5622410982612362214084997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7496547976816482952113329 5622410982612362214084997)
        ·
          refine ⟨1054202059239817915140937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5622410982612362214084997 1054202059239817915140937)
          ·
            refine ⟨790651544429863436355703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1054202059239817915140937 790651544429863436355703)
            ·
              refine ⟨1185977316644795154533555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 790651544429863436355703 1185977316644795154533555)
              ·
                refine ⟨1778965974967192731800333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1185977316644795154533555 1778965974967192731800333)
                ·
                  refine ⟨667112240612697274425125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1778965974967192731800333 667112240612697274425125)
                  ·
                    refine ⟨125083545114880738954711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667112240612697274425125 125083545114880738954711)
                    ·
                      rfl

theorem cell22_365399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_365399 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365399 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365399 prefixEnd_365399 := by exact prefixLift 365399
  have htrace : WordTrace (prefixWord ++ tailWord_365399) baseStart_365399 baseEnd_365399 := by
    simpa [prefixWord, tailWord_365399, baseEnd_365399] using wordTrace_append hprefix tailTrace_365399
  have hstable : (prefixWord ++ tailWord_365399).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365399).length < 2 ^ (prefixWord ++ tailWord_365399).sum := by decide
  have hdescent : baseEnd_365399 < baseStart_365399 := by decide
  rcases family_descends (prefixWord ++ tailWord_365399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365461 : List Nat := [1, 3, 2, 1, 1, 6, 1, 1, 2, 4]
def baseStart_365461 : Nat := 118140960795 + 365461 * 2 ^ 59
def prefixEnd_365461 : Nat := 4983230072969 + 3 ^ 40 * 365461 * 2
def baseEnd_365461 : Nat := 125104768981933243904521

theorem tailTrace_365461 : CollatzResearch.WordTrace tailWord_365461 prefixEnd_365461 125104768981933243904521 := by
  unfold tailWord_365461
  simp only [CollatzResearch.WordTrace]
  refine ⟨13329457729004687614736237, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8886305152669791743157491 13329457729004687614736237)
  ·
    refine ⟨4998546648376757855526089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13329457729004687614736237 4998546648376757855526089)
    ·
      refine ⟨3748909986282568391644567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4998546648376757855526089 3748909986282568391644567)
      ·
        refine ⟨5623364979423852587466851, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3748909986282568391644567 5623364979423852587466851)
        ·
          refine ⟨8435047469135778881200277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5623364979423852587466851 8435047469135778881200277)
          ·
            refine ⟨395392850115739635056263, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8435047469135778881200277 395392850115739635056263)
            ·
              refine ⟨593089275173609452584395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395392850115739635056263 593089275173609452584395)
              ·
                refine ⟨889633912760414178876593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593089275173609452584395 889633912760414178876593)
                ·
                  refine ⟨667225434570310634157445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 889633912760414178876593 667225434570310634157445)
                  ·
                    refine ⟨125104768981933243904521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667225434570310634157445 125104768981933243904521)
                    ·
                      rfl

theorem cell22_365461_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 1, 2, 4].length) (baseStart_365461 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365461 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365461 prefixEnd_365461 := by exact prefixLift 365461
  have htrace : WordTrace (prefixWord ++ tailWord_365461) baseStart_365461 baseEnd_365461 := by
    simpa [prefixWord, tailWord_365461, baseEnd_365461] using wordTrace_append hprefix tailTrace_365461
  have hstable : (prefixWord ++ tailWord_365461).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365461).length < 2 ^ (prefixWord ++ tailWord_365461).sum := by decide
  have hdescent : baseEnd_365461 < baseStart_365461 := by decide
  rcases family_descends (prefixWord ++ tailWord_365461) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365600 : List Nat := [2, 1, 1, 7, 1, 1, 1, 4, 4]
def baseStart_365600 : Nat := 118140960795 + 365600 * 2 ^ 59
def prefixEnd_365600 : Nat := 4983230072969 + 3 ^ 40 * 365600 * 2
def baseEnd_365600 : Nat := 41717450507527738226365

theorem tailTrace_365600 : CollatzResearch.WordTrace tailWord_365600 prefixEnd_365600 41717450507527738226365 := by
  unfold tailWord_365600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6667263737750557177023127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8889684983667409569364169 6667263737750557177023127)
  ·
    refine ⟨10000895606625835765534691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6667263737750557177023127 10000895606625835765534691)
    ·
      refine ⟨15001343409938753648302037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10000895606625835765534691 15001343409938753648302037)
      ·
        refine ⟨351593986170439538632079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 15001343409938753648302037 351593986170439538632079)
        ·
          refine ⟨527390979255659307948119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 351593986170439538632079 527390979255659307948119)
          ·
            refine ⟨791086468883488961922179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 527390979255659307948119 791086468883488961922179)
            ·
              refine ⟨1186629703325233442883269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 791086468883488961922179 1186629703325233442883269)
              ·
                refine ⟨222493069373481270540613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1186629703325233442883269 222493069373481270540613)
                ·
                  refine ⟨41717450507527738226365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222493069373481270540613 41717450507527738226365)
                  ·
                    rfl

theorem cell22_365600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 1, 1, 1, 4, 4].length) (baseStart_365600 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365600 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365600 prefixEnd_365600 := by exact prefixLift 365600
  have htrace : WordTrace (prefixWord ++ tailWord_365600) baseStart_365600 baseEnd_365600 := by
    simpa [prefixWord, tailWord_365600, baseEnd_365600] using wordTrace_append hprefix tailTrace_365600
  have hstable : (prefixWord ++ tailWord_365600).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365600).length < 2 ^ (prefixWord ++ tailWord_365600).sum := by decide
  have hdescent : baseEnd_365600 < baseStart_365600 := by decide
  rcases family_descends (prefixWord ++ tailWord_365600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365626 : List Nat := [3, 1, 1, 1, 3, 1, 3, 1, 5, 3]
def baseStart_365626 : Nat := 118140960795 + 365626 * 2 ^ 59
def prefixEnd_365626 : Nat := 4983230072969 + 3 ^ 40 * 365626 * 2
def baseEnd_365626 : Nat := 125161251853927813529015

theorem tailTrace_365626 : CollatzResearch.WordTrace tailWord_365626 prefixEnd_365626 125161251853927813529015 := by
  unfold tailWord_365626
  simp only [CollatzResearch.WordTrace]
  refine ⟨3333868943351730198623183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8890317182271280529661821 3333868943351730198623183)
  ·
    refine ⟨5000803415027595297934775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3333868943351730198623183 5000803415027595297934775)
    ·
      refine ⟨7501205122541392946902163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5000803415027595297934775 7501205122541392946902163)
      ·
        refine ⟨11251807683812089420353245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7501205122541392946902163 11251807683812089420353245)
        ·
          refine ⟨4219427881429533532632467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11251807683812089420353245 4219427881429533532632467)
          ·
            refine ⟨6329141822144300298948701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4219427881429533532632467 6329141822144300298948701)
            ·
              refine ⟨2373428183304112612105763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6329141822144300298948701 2373428183304112612105763)
              ·
                refine ⟨3560142274956168918158645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2373428183304112612105763 3560142274956168918158645)
                ·
                  refine ⟨333763338277140836077373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3560142274956168918158645 333763338277140836077373)
                  ·
                    refine ⟨125161251853927813529015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333763338277140836077373 125161251853927813529015)
                    ·
                      rfl

theorem cell22_365626_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 3, 1, 5, 3].length) (baseStart_365626 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365626 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365626 prefixEnd_365626 := by exact prefixLift 365626
  have htrace : WordTrace (prefixWord ++ tailWord_365626) baseStart_365626 baseEnd_365626 := by
    simpa [prefixWord, tailWord_365626, baseEnd_365626] using wordTrace_append hprefix tailTrace_365626
  have hstable : (prefixWord ++ tailWord_365626).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365626).length < 2 ^ (prefixWord ++ tailWord_365626).sum := by decide
  have hdescent : baseEnd_365626 < baseStart_365626 := by decide
  rcases family_descends (prefixWord ++ tailWord_365626) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365630 : List Nat := [4, 2, 1, 3, 1, 3, 1, 1, 2, 4]
def baseStart_365630 : Nat := 118140960795 + 365630 * 2 ^ 59
def prefixEnd_365630 : Nat := 4983230072969 + 3 ^ 40 * 365630 * 2
def baseEnd_365630 : Nat := 125162621135673136429003

theorem tailTrace_365630 : CollatzResearch.WordTrace tailWord_365630 prefixEnd_365630 125162621135673136429003 := by
  unfold tailWord_365630
  simp only [CollatzResearch.WordTrace]
  refine ⟨1666952708174053684704793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8890414443594952985092229 1666952708174053684704793)
  ·
    refine ⟨1250214531130540263528595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1666952708174053684704793 1250214531130540263528595)
    ·
      refine ⟨1875321796695810395292893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1250214531130540263528595 1875321796695810395292893)
      ·
        refine ⟨703245673760928898234835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1875321796695810395292893 703245673760928898234835)
        ·
          refine ⟨1054868510641393347352253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 703245673760928898234835 1054868510641393347352253)
          ·
            refine ⟨395575691490522505257095, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1054868510641393347352253 395575691490522505257095)
            ·
              refine ⟨593363537235783757885643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395575691490522505257095 593363537235783757885643)
              ·
                refine ⟨890045305853675636828465, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 593363537235783757885643 890045305853675636828465)
                ·
                  refine ⟨667533979390256727621349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 890045305853675636828465 667533979390256727621349)
                  ·
                    refine ⟨125162621135673136429003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 667533979390256727621349 125162621135673136429003)
                    ·
                      rfl

theorem cell22_365630_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 1, 3, 1, 1, 2, 4].length) (baseStart_365630 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365630 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365630 prefixEnd_365630 := by exact prefixLift 365630
  have htrace : WordTrace (prefixWord ++ tailWord_365630) baseStart_365630 baseEnd_365630 := by
    simpa [prefixWord, tailWord_365630, baseEnd_365630] using wordTrace_append hprefix tailTrace_365630
  have hstable : (prefixWord ++ tailWord_365630).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365630).length < 2 ^ (prefixWord ++ tailWord_365630).sum := by decide
  have hdescent : baseEnd_365630 < baseStart_365630 := by decide
  rcases family_descends (prefixWord ++ tailWord_365630) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365660 : List Nat := [2, 2, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_365660 : Nat := 118140960795 + 365660 * 2 ^ 59
def prefixEnd_365660 : Nat := 4983230072969 + 3 ^ 40 * 365660 * 2
def baseEnd_365660 : Nat := 125172890748763058178911

theorem tailTrace_365660 : CollatzResearch.WordTrace tailWord_365660 prefixEnd_365660 125172890748763058178911 := by
  unfold tailWord_365660
  simp only [CollatzResearch.WordTrace]
  refine ⟨6668357927641872300615217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8891143903522496400820289 6668357927641872300615217)
  ·
    refine ⟨5001268445731404225461413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6668357927641872300615217 5001268445731404225461413)
    ·
      refine ⟨937737833574638292274015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5001268445731404225461413 937737833574638292274015)
      ·
        refine ⟨1406606750361957438411023, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 937737833574638292274015 1406606750361957438411023)
        ·
          refine ⟨2109910125542936157616535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1406606750361957438411023 2109910125542936157616535)
          ·
            refine ⟨3164865188314404236424803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2109910125542936157616535 3164865188314404236424803)
            ·
              refine ⟨4747297782471606354637205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3164865188314404236424803 4747297782471606354637205)
              ·
                refine ⟨222529583553356547873619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4747297782471606354637205 222529583553356547873619)
                ·
                  refine ⟨333794375330034821810429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222529583553356547873619 333794375330034821810429)
                  ·
                    refine ⟨125172890748763058178911, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 333794375330034821810429 125172890748763058178911)
                    ·
                      rfl

theorem cell22_365660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_365660 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365660 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365660 prefixEnd_365660 := by exact prefixLift 365660
  have htrace : WordTrace (prefixWord ++ tailWord_365660) baseStart_365660 baseEnd_365660 := by
    simpa [prefixWord, tailWord_365660, baseEnd_365660] using wordTrace_append hprefix tailTrace_365660
  have hstable : (prefixWord ++ tailWord_365660).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365660).length < 2 ^ (prefixWord ++ tailWord_365660).sum := by decide
  have hdescent : baseEnd_365660 < baseStart_365660 := by decide
  rcases family_descends (prefixWord ++ tailWord_365660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365671 : List Nat := [1, 1, 5, 1, 1, 3, 2, 1, 2, 5]
def baseStart_365671 : Nat := 118140960795 + 365671 * 2 ^ 59
def prefixEnd_365671 : Nat := 4983230072969 + 3 ^ 40 * 365671 * 2
def baseEnd_365671 : Nat := 125176656273562696153877

theorem tailTrace_365671 : CollatzResearch.WordTrace tailWord_365671 prefixEnd_365671 125176656273562696153877 := by
  unfold tailWord_365671
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337117058243893479880867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8891411372162595653253911 13337117058243893479880867)
  ·
    refine ⟨20005675587365840219821301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13337117058243893479880867 20005675587365840219821301)
    ·
      refine ⟨1875532086315547520608247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 20005675587365840219821301 1875532086315547520608247)
      ·
        refine ⟨2813298129473321280912371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1875532086315547520608247 2813298129473321280912371)
        ·
          refine ⟨4219947194209981921368557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2813298129473321280912371 4219947194209981921368557)
          ·
            refine ⟨1582480197828743220513209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4219947194209981921368557 1582480197828743220513209)
            ·
              refine ⟨1186860148371557415384907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582480197828743220513209 1186860148371557415384907)
              ·
                refine ⟨1780290222557336123077361, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1186860148371557415384907 1780290222557336123077361)
                ·
                  refine ⟨1335217666918002092308021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1780290222557336123077361 1335217666918002092308021)
                  ·
                    refine ⟨125176656273562696153877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1335217666918002092308021 125176656273562696153877)
                    ·
                      rfl

theorem cell22_365671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 1, 2, 5].length) (baseStart_365671 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365671 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365671 prefixEnd_365671 := by exact prefixLift 365671
  have htrace : WordTrace (prefixWord ++ tailWord_365671) baseStart_365671 baseEnd_365671 := by
    simpa [prefixWord, tailWord_365671, baseEnd_365671] using wordTrace_append hprefix tailTrace_365671
  have hstable : (prefixWord ++ tailWord_365671).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365671).length < 2 ^ (prefixWord ++ tailWord_365671).sum := by decide
  have hdescent : baseEnd_365671 < baseStart_365671 := by decide
  rcases family_descends (prefixWord ++ tailWord_365671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365673 : List Nat := [1, 2, 1, 1, 1, 7, 3, 1, 5]
def baseStart_365673 : Nat := 118140960795 + 365673 * 2 ^ 59
def prefixEnd_365673 : Nat := 4983230072969 + 3 ^ 40 * 365673 * 2
def baseEnd_365673 : Nat := 41725780304811785867957

theorem tailTrace_365673 : CollatzResearch.WordTrace tailWord_365673 prefixEnd_365673 41725780304811785867957 := by
  unfold tailWord_365673
  simp only [CollatzResearch.WordTrace]
  refine ⟨13337190004236647821453673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8891460002824431880969115 13337190004236647821453673)
  ·
    refine ⟨10002892503177485866090255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13337190004236647821453673 10002892503177485866090255)
    ·
      refine ⟨15004338754766228799135383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10002892503177485866090255 15004338754766228799135383)
      ·
        refine ⟨22506508132149343198703075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15004338754766228799135383 22506508132149343198703075)
        ·
          refine ⟨33759762198224014798054613, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22506508132149343198703075 33759762198224014798054613)
          ·
            refine ⟨791244426520875346829405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 33759762198224014798054613 791244426520875346829405)
            ·
              refine ⟨296716659945328255061027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 791244426520875346829405 296716659945328255061027)
              ·
                refine ⟨445074989917992382591541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 296716659945328255061027 445074989917992382591541)
                ·
                  refine ⟨41725780304811785867957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445074989917992382591541 41725780304811785867957)
                  ·
                    rfl

theorem cell22_365673_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 7, 3, 1, 5].length) (baseStart_365673 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365673 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365673 prefixEnd_365673 := by exact prefixLift 365673
  have htrace : WordTrace (prefixWord ++ tailWord_365673) baseStart_365673 baseEnd_365673 := by
    simpa [prefixWord, tailWord_365673, baseEnd_365673] using wordTrace_append hprefix tailTrace_365673
  have hstable : (prefixWord ++ tailWord_365673).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365673).length < 2 ^ (prefixWord ++ tailWord_365673).sum := by decide
  have hdescent : baseEnd_365673 < baseStart_365673 := by decide
  rcases family_descends (prefixWord ++ tailWord_365673) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365746 : List Nat := [3, 2, 1, 1, 1, 4, 2, 8]
def baseStart_365746 : Nat := 118140960795 + 365746 * 2 ^ 59
def prefixEnd_365746 : Nat := 4983230072969 + 3 ^ 40 * 365746 * 2
def baseEnd_365746 : Nat := 13911370034031944503183

theorem tailTrace_365746 : CollatzResearch.WordTrace tailWord_365746 prefixEnd_365746 13911370034031944503183 := by
  unfold tailWord_365746
  simp only [CollatzResearch.WordTrace]
  refine ⟨3334963133243045322215273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8893235021981454192574061 3334963133243045322215273)
  ·
    refine ⟨2501222349932283991661455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3334963133243045322215273 2501222349932283991661455)
    ·
      refine ⟨3751833524898425987492183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2501222349932283991661455 3751833524898425987492183)
      ·
        refine ⟨5627750287347638981238275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3751833524898425987492183 5627750287347638981238275)
        ·
          refine ⟨8441625431021458471857413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5627750287347638981238275 8441625431021458471857413)
          ·
            refine ⟨1582804768316523463473265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 8441625431021458471857413 1582804768316523463473265)
            ·
              refine ⟨1187103576237392597604949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1582804768316523463473265 1187103576237392597604949)
              ·
                refine ⟨13911370034031944503183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1187103576237392597604949 13911370034031944503183)
                ·
                  rfl

theorem cell22_365746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 4, 2, 8].length) (baseStart_365746 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365746 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365746 prefixEnd_365746 := by exact prefixLift 365746
  have htrace : WordTrace (prefixWord ++ tailWord_365746) baseStart_365746 baseEnd_365746 := by
    simpa [prefixWord, tailWord_365746, baseEnd_365746] using wordTrace_append hprefix tailTrace_365746
  have hstable : (prefixWord ++ tailWord_365746).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365746).length < 2 ^ (prefixWord ++ tailWord_365746).sum := by decide
  have hdescent : baseEnd_365746 < baseStart_365746 := by decide
  rcases family_descends (prefixWord ++ tailWord_365746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365825 : List Nat := [1, 2, 4, 1, 1, 5, 1, 2, 5]
def baseStart_365825 : Nat := 118140960795 + 365825 * 2 ^ 59
def prefixEnd_365825 : Nat := 4983230072969 + 3 ^ 40 * 365825 * 2
def baseEnd_365825 : Nat := 41743124540252542601135

theorem tailTrace_365825 : CollatzResearch.WordTrace tailWord_365825 prefixEnd_365825 41743124540252542601135 := by
  unfold tailWord_365825
  simp only [CollatzResearch.WordTrace]
  refine ⟨13342733899685977780986929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8895155933123985187324619 13342733899685977780986929)
  ·
    refine ⟨10007050424764483335740197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13342733899685977780986929 10007050424764483335740197)
    ·
      refine ⟨1876321954643340625451287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10007050424764483335740197 1876321954643340625451287)
      ·
        refine ⟨2814482931965010938176931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1876321954643340625451287 2814482931965010938176931)
        ·
          refine ⟨4221724397947516407265397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2814482931965010938176931 4221724397947516407265397)
          ·
            refine ⟨395786662307579663181131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4221724397947516407265397 395786662307579663181131)
            ·
              refine ⟨593679993461369494771697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 395786662307579663181131 593679993461369494771697)
              ·
                refine ⟨445259995096027121078773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 593679993461369494771697 445259995096027121078773)
                ·
                  refine ⟨41743124540252542601135, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445259995096027121078773 41743124540252542601135)
                  ·
                    rfl

theorem cell22_365825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 1, 2, 5].length) (baseStart_365825 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365825 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365825 prefixEnd_365825 := by exact prefixLift 365825
  have htrace : WordTrace (prefixWord ++ tailWord_365825) baseStart_365825 baseEnd_365825 := by
    simpa [prefixWord, tailWord_365825, baseEnd_365825] using wordTrace_append hprefix tailTrace_365825
  have hstable : (prefixWord ++ tailWord_365825).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365825).length < 2 ^ (prefixWord ++ tailWord_365825).sum := by decide
  have hdescent : baseEnd_365825 < baseStart_365825 := by decide
  rcases family_descends (prefixWord ++ tailWord_365825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365887 : List Nat := [1, 1, 2, 2, 4, 3, 3, 2, 4]
def baseStart_365887 : Nat := 118140960795 + 365887 * 2 ^ 59
def prefixEnd_365887 : Nat := 4983230072969 + 3 ^ 40 * 365887 * 2
def baseEnd_365887 : Nat := 41750199162603377584405

theorem tailTrace_365887 : CollatzResearch.WordTrace tailWord_365887 prefixEnd_365887 41750199162603377584405 := by
  unfold tailWord_365887
  simp only [CollatzResearch.WordTrace]
  refine ⟨13344995225461362369743915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8896663483640908246495943 13344995225461362369743915)
  ·
    refine ⟨20017492838192043554615873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13344995225461362369743915 20017492838192043554615873)
    ·
      refine ⟨15013119628644032665961905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20017492838192043554615873 15013119628644032665961905)
      ·
        refine ⟨11259839721483024499471429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15013119628644032665961905 11259839721483024499471429)
        ·
          refine ⟨2111219947778067093650893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11259839721483024499471429 2111219947778067093650893)
          ·
            refine ⟨791707480416775160119085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2111219947778067093650893 791707480416775160119085)
            ·
              refine ⟨296890305156290685044657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 791707480416775160119085 296890305156290685044657)
              ·
                refine ⟨222667728867218013783493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 296890305156290685044657 222667728867218013783493)
                ·
                  refine ⟨41750199162603377584405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222667728867218013783493 41750199162603377584405)
                  ·
                    rfl

theorem cell22_365887_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 4, 3, 3, 2, 4].length) (baseStart_365887 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365887 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365887 prefixEnd_365887 := by exact prefixLift 365887
  have htrace : WordTrace (prefixWord ++ tailWord_365887) baseStart_365887 baseEnd_365887 := by
    simpa [prefixWord, tailWord_365887, baseEnd_365887] using wordTrace_append hprefix tailTrace_365887
  have hstable : (prefixWord ++ tailWord_365887).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365887).length < 2 ^ (prefixWord ++ tailWord_365887).sum := by decide
  have hdescent : baseEnd_365887 < baseStart_365887 := by decide
  rcases family_descends (prefixWord ++ tailWord_365887) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365947 : List Nat := [1, 1, 1, 1, 1, 6, 3, 4, 1, 3]
def baseStart_365947 : Nat := 118140960795 + 365947 * 2 ^ 59
def prefixEnd_365947 : Nat := 4983230072969 + 3 ^ 40 * 365947 * 2
def baseEnd_365947 : Nat := 125271136713989976253031

theorem tailTrace_365947 : CollatzResearch.WordTrace tailWord_365947 prefixEnd_365947 125271136713989976253031 := by
  unfold tailWord_365947
  simp only [CollatzResearch.WordTrace]
  refine ⟨13347183605243992616928095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8898122403495995077952063 13347183605243992616928095)
  ·
    refine ⟨20020775407865988925392143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13347183605243992616928095 20020775407865988925392143)
    ·
      refine ⟨30031163111798983388088215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20020775407865988925392143 30031163111798983388088215)
      ·
        refine ⟨45046744667698475082132323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30031163111798983388088215 45046744667698475082132323)
        ·
          refine ⟨67570117001547712623198485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45046744667698475082132323 67570117001547712623198485)
          ·
            refine ⟨3167349234447549029212429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 67570117001547712623198485 3167349234447549029212429)
            ·
              refine ⟨1187755962917830885954661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3167349234447549029212429 1187755962917830885954661)
              ·
                refine ⟨222704243047093291116499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1187755962917830885954661 222704243047093291116499)
                ·
                  refine ⟨334056364570639936674749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222704243047093291116499 334056364570639936674749)
                  ·
                    refine ⟨125271136713989976253031, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334056364570639936674749 125271136713989976253031)
                    ·
                      rfl

theorem cell22_365947_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 6, 3, 4, 1, 3].length) (baseStart_365947 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365947 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365947 prefixEnd_365947 := by exact prefixLift 365947
  have htrace : WordTrace (prefixWord ++ tailWord_365947) baseStart_365947 baseEnd_365947 := by
    simpa [prefixWord, tailWord_365947, baseEnd_365947] using wordTrace_append hprefix tailTrace_365947
  have hstable : (prefixWord ++ tailWord_365947).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365947).length < 2 ^ (prefixWord ++ tailWord_365947).sum := by decide
  have hdescent : baseEnd_365947 < baseStart_365947 := by decide
  rcases family_descends (prefixWord ++ tailWord_365947) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365960 : List Nat := [2, 1, 3, 3, 1, 2, 2, 3, 5]
def baseStart_365960 : Nat := 118140960795 + 365960 * 2 ^ 59
def prefixEnd_365960 : Nat := 4983230072969 + 3 ^ 40 * 365960 * 2
def baseEnd_365960 : Nat := 41758528959887425225997

theorem tailTrace_365960 : CollatzResearch.WordTrace tailWord_365960 prefixEnd_365960 41758528959887425225997 := by
  unfold tailWord_365960
  simp only [CollatzResearch.WordTrace]
  refine ⟨6673828877098447918575667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8898438502797930558100889 6673828877098447918575667)
  ·
    refine ⟨10010743315647671877863501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6673828877098447918575667 10010743315647671877863501)
    ·
      refine ⟨3754028743367876954198813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10010743315647671877863501 3754028743367876954198813)
      ·
        refine ⟨1407760778762953857824555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3754028743367876954198813 1407760778762953857824555)
        ·
          refine ⟨2111641168144430786736833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1407760778762953857824555 2111641168144430786736833)
          ·
            refine ⟨1583730876108323090052625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2111641168144430786736833 1583730876108323090052625)
            ·
              refine ⟨1187798157081242317539469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1583730876108323090052625 1187798157081242317539469)
              ·
                refine ⟨445424308905465869077301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1187798157081242317539469 445424308905465869077301)
                ·
                  refine ⟨41758528959887425225997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445424308905465869077301 41758528959887425225997)
                  ·
                    rfl

theorem cell22_365960_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 2, 3, 5].length) (baseStart_365960 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365960 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365960 prefixEnd_365960 := by exact prefixLift 365960
  have htrace : WordTrace (prefixWord ++ tailWord_365960) baseStart_365960 baseEnd_365960 := by
    simpa [prefixWord, tailWord_365960, baseEnd_365960] using wordTrace_append hprefix tailTrace_365960
  have hstable : (prefixWord ++ tailWord_365960).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365960).length < 2 ^ (prefixWord ++ tailWord_365960).sum := by decide
  have hdescent : baseEnd_365960 < baseStart_365960 := by decide
  rcases family_descends (prefixWord ++ tailWord_365960) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_365988 : List Nat := [2, 3, 1, 2, 1, 1, 1, 1, 10]
def baseStart_365988 : Nat := 118140960795 + 365988 * 2 ^ 59
def prefixEnd_365988 : Nat := 4983230072969 + 3 ^ 40 * 365988 * 2
def baseEnd_365988 : Nat := 41761723950626511992635

theorem tailTrace_365988 : CollatzResearch.WordTrace tailWord_365988 prefixEnd_365988 41761723950626511992635 := by
  unfold tailWord_365988
  simp only [CollatzResearch.WordTrace]
  refine ⟨6674339499047728309585309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8899119332063637746113745 6674339499047728309585309)
  ·
    refine ⟨2502877312142898116094491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6674339499047728309585309 2502877312142898116094491)
    ·
      refine ⟨3754315968214347174141737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2502877312142898116094491 3754315968214347174141737)
      ·
        refine ⟨2815736976160760380606303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3754315968214347174141737 2815736976160760380606303)
        ·
          refine ⟨4223605464241140570909455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2815736976160760380606303 4223605464241140570909455)
          ·
            refine ⟨6335408196361710856364183, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4223605464241140570909455 6335408196361710856364183)
            ·
              refine ⟨9503112294542566284546275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6335408196361710856364183 9503112294542566284546275)
              ·
                refine ⟨14254668441813849426819413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9503112294542566284546275 14254668441813849426819413)
                ·
                  refine ⟨41761723950626511992635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 14254668441813849426819413 41761723950626511992635)
                  ·
                    rfl

theorem cell22_365988_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 1, 10].length) (baseStart_365988 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_365988 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_365988 prefixEnd_365988 := by exact prefixLift 365988
  have htrace : WordTrace (prefixWord ++ tailWord_365988) baseStart_365988 baseEnd_365988 := by
    simpa [prefixWord, tailWord_365988, baseEnd_365988] using wordTrace_append hprefix tailTrace_365988
  have hstable : (prefixWord ++ tailWord_365988).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_365988).length < 2 ^ (prefixWord ++ tailWord_365988).sum := by decide
  have hdescent : baseEnd_365988 < baseStart_365988 := by decide
  rcases family_descends (prefixWord ++ tailWord_365988) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366003 : List Nat := [1, 1, 1, 2, 3, 1, 1, 4, 3, 5]
def baseStart_366003 : Nat := 118140960795 + 366003 * 2 ^ 59
def prefixEnd_366003 : Nat := 4983230072969 + 3 ^ 40 * 366003 * 2
def baseEnd_366003 : Nat := 125290306658424496852859

theorem tailTrace_366003 : CollatzResearch.WordTrace tailWord_366003 prefixEnd_366003 125290306658424496852859 := by
  unfold tailWord_366003
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349226093041114180966663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8899484062027409453977775 13349226093041114180966663)
  ·
    refine ⟨20023839139561671271449995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13349226093041114180966663 20023839139561671271449995)
    ·
      refine ⟨30035758709342506907174993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20023839139561671271449995 30035758709342506907174993)
      ·
        refine ⟨22526819032006880180381245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30035758709342506907174993 22526819032006880180381245)
        ·
          refine ⟨8447557137002580067642967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22526819032006880180381245 8447557137002580067642967)
          ·
            refine ⟨12671335705503870101464451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8447557137002580067642967 12671335705503870101464451)
            ·
              refine ⟨19007003558255805152196677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12671335705503870101464451 19007003558255805152196677)
              ·
                refine ⟨3563813167172963466036877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19007003558255805152196677 3563813167172963466036877)
                ·
                  refine ⟨1336429937689861299763829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3563813167172963466036877 1336429937689861299763829)
                  ·
                    refine ⟨125290306658424496852859, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1336429937689861299763829 125290306658424496852859)
                    ·
                      rfl

theorem cell22_366003_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 4, 3, 5].length) (baseStart_366003 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366003 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366003 prefixEnd_366003 := by exact prefixLift 366003
  have htrace : WordTrace (prefixWord ++ tailWord_366003) baseStart_366003 baseEnd_366003 := by
    simpa [prefixWord, tailWord_366003, baseEnd_366003] using wordTrace_append hprefix tailTrace_366003
  have hstable : (prefixWord ++ tailWord_366003).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366003).length < 2 ^ (prefixWord ++ tailWord_366003).sum := by decide
  have hdescent : baseEnd_366003 < baseStart_366003 := by decide
  rcases family_descends (prefixWord ++ tailWord_366003) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366005 : List Nat := [1, 3, 3, 2, 2, 1, 1, 3, 6]
def baseStart_366005 : Nat := 118140960795 + 366005 * 2 ^ 59
def prefixEnd_366005 : Nat := 4983230072969 + 3 ^ 40 * 366005 * 2
def baseEnd_366005 : Nat := 41763663766432386100951

theorem tailTrace_366005 : CollatzResearch.WordTrace tailWord_366005 prefixEnd_366005 41763663766432386100951 := by
  unfold tailWord_366005
  simp only [CollatzResearch.WordTrace]
  refine ⟨13349299039033868522539469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8899532692689245681692979 13349299039033868522539469)
  ·
    refine ⟨5005987139637700695952301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13349299039033868522539469 5005987139637700695952301)
    ·
      refine ⟨1877245177364137760982113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5005987139637700695952301 1877245177364137760982113)
      ·
        refine ⟨1407933883023103320736585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1877245177364137760982113 1407933883023103320736585)
        ·
          refine ⟨1055950412267327490552439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1407933883023103320736585 1055950412267327490552439)
          ·
            refine ⟨1583925618400991235828659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1055950412267327490552439 1583925618400991235828659)
            ·
              refine ⟨2375888427601486853742989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1583925618400991235828659 2375888427601486853742989)
              ·
                refine ⟨890958160350557570153621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2375888427601486853742989 890958160350557570153621)
                ·
                  refine ⟨41763663766432386100951, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 890958160350557570153621 41763663766432386100951)
                  ·
                    rfl

theorem cell22_366005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 1, 1, 3, 6].length) (baseStart_366005 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366005 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366005 prefixEnd_366005 := by exact prefixLift 366005
  have htrace : WordTrace (prefixWord ++ tailWord_366005) baseStart_366005 baseEnd_366005 := by
    simpa [prefixWord, tailWord_366005, baseEnd_366005] using wordTrace_append hprefix tailTrace_366005
  have hstable : (prefixWord ++ tailWord_366005).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366005).length < 2 ^ (prefixWord ++ tailWord_366005).sum := by decide
  have hdescent : baseEnd_366005 < baseStart_366005 := by decide
  rcases family_descends (prefixWord ++ tailWord_366005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366112 : List Nat := [2, 1, 1, 6, 1, 1, 1, 4, 5]
def baseStart_366112 : Nat := 118140960795 + 366112 * 2 ^ 59
def prefixEnd_366112 : Nat := 4983230072969 + 3 ^ 40 * 366112 * 2
def baseEnd_366112 : Nat := 41775873195328181959175

theorem tailTrace_366112 : CollatzResearch.WordTrace tailWord_366112 prefixEnd_366112 41775873195328181959175 := by
  unfold tailWord_366112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6676600824823112898342295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8902134433097483864456393 6676600824823112898342295)
  ·
    refine ⟨10014901237234669347513443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6676600824823112898342295 10014901237234669347513443)
    ·
      refine ⟨15022351855852004021270165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10014901237234669347513443 15022351855852004021270165)
      ·
        refine ⟨704172743243062688497039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 15022351855852004021270165 704172743243062688497039)
        ·
          refine ⟨1056259114864594032745559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704172743243062688497039 1056259114864594032745559)
          ·
            refine ⟨1584388672296891049118339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1056259114864594032745559 1584388672296891049118339)
            ·
              refine ⟨2376583008445336573677509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1584388672296891049118339 2376583008445336573677509)
              ·
                refine ⟨445609314083500607564533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2376583008445336573677509 445609314083500607564533)
                ·
                  refine ⟨41775873195328181959175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 445609314083500607564533 41775873195328181959175)
                  ·
                    rfl

theorem cell22_366112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 1, 1, 1, 4, 5].length) (baseStart_366112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366112 prefixEnd_366112 := by exact prefixLift 366112
  have htrace : WordTrace (prefixWord ++ tailWord_366112) baseStart_366112 baseEnd_366112 := by
    simpa [prefixWord, tailWord_366112, baseEnd_366112] using wordTrace_append hprefix tailTrace_366112
  have hstable : (prefixWord ++ tailWord_366112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366112).length < 2 ^ (prefixWord ++ tailWord_366112).sum := by decide
  have hdescent : baseEnd_366112 < baseStart_366112 := by decide
  rcases family_descends (prefixWord ++ tailWord_366112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366150 : List Nat := [6, 1, 1, 1, 3, 1, 2, 3, 1, 3]
def baseStart_366150 : Nat := 118140960795 + 366150 * 2 ^ 59
def prefixEnd_366150 : Nat := 4983230072969 + 3 ^ 40 * 366150 * 2
def baseEnd_366150 : Nat := 125340627762565113427409

theorem tailTrace_366150 : CollatzResearch.WordTrace tailWord_366150 prefixEnd_366150 125340627762565113427409 := by
  unfold tailWord_366150
  simp only [CollatzResearch.WordTrace]
  refine ⟨417330863234642446455247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8903058415672372191045269 417330863234642446455247)
  ·
    refine ⟨625996294851963669682871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 417330863234642446455247 625996294851963669682871)
    ·
      refine ⟨938994442277945504524307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 625996294851963669682871 938994442277945504524307)
      ·
        refine ⟨1408491663416918256786461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 938994442277945504524307 1408491663416918256786461)
        ·
          refine ⟨528184373781344346294923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1408491663416918256786461 528184373781344346294923)
          ·
            refine ⟨792276560672016519442385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528184373781344346294923 792276560672016519442385)
            ·
              refine ⟨594207420504012389581789, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 792276560672016519442385 594207420504012389581789)
              ·
                refine ⟨222827782689004646093171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 594207420504012389581789 222827782689004646093171)
                ·
                  refine ⟨334241674033506969139757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222827782689004646093171 334241674033506969139757)
                  ·
                    refine ⟨125340627762565113427409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334241674033506969139757 125340627762565113427409)
                    ·
                      rfl

theorem cell22_366150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 3, 1, 2, 3, 1, 3].length) (baseStart_366150 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366150 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366150 prefixEnd_366150 := by exact prefixLift 366150
  have htrace : WordTrace (prefixWord ++ tailWord_366150) baseStart_366150 baseEnd_366150 := by
    simpa [prefixWord, tailWord_366150, baseEnd_366150] using wordTrace_append hprefix tailTrace_366150
  have hstable : (prefixWord ++ tailWord_366150).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366150).length < 2 ^ (prefixWord ++ tailWord_366150).sum := by decide
  have hdescent : baseEnd_366150 < baseStart_366150 := by decide
  rcases family_descends (prefixWord ++ tailWord_366150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366217 : List Nat := [1, 2, 1, 1, 4, 1, 2, 2, 5, 3]
def baseStart_366217 : Nat := 118140960795 + 366217 * 2 ^ 59
def prefixEnd_366217 : Nat := 4983230072969 + 3 ^ 40 * 366217 * 2
def baseEnd_366217 : Nat := 125363563231799272002203

theorem tailTrace_366217 : CollatzResearch.WordTrace tailWord_366217 prefixEnd_366217 125363563231799272002203 := by
  unfold tailWord_366217
  simp only [CollatzResearch.WordTrace]
  refine ⟨13357031314265828729256905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8904687542843885819504603 13357031314265828729256905)
  ·
    refine ⟨10017773485699371546942679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13357031314265828729256905 10017773485699371546942679)
    ·
      refine ⟨15026660228549057320414019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10017773485699371546942679 15026660228549057320414019)
      ·
        refine ⟨22539990342823585980621029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15026660228549057320414019 22539990342823585980621029)
        ·
          refine ⟨4226248189279422371366443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22539990342823585980621029 4226248189279422371366443)
          ·
            refine ⟨6339372283919133557049665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4226248189279422371366443 6339372283919133557049665)
            ·
              refine ⟨4754529212939350167787249, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6339372283919133557049665 4754529212939350167787249)
              ·
                refine ⟨3565896909704512625840437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4754529212939350167787249 3565896909704512625840437)
                ·
                  refine ⟨334302835284798058672541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3565896909704512625840437 334302835284798058672541)
                  ·
                    refine ⟨125363563231799272002203, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334302835284798058672541 125363563231799272002203)
                    ·
                      rfl

theorem cell22_366217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 2, 2, 5, 3].length) (baseStart_366217 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366217 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366217 prefixEnd_366217 := by exact prefixLift 366217
  have htrace : WordTrace (prefixWord ++ tailWord_366217) baseStart_366217 baseEnd_366217 := by
    simpa [prefixWord, tailWord_366217, baseEnd_366217] using wordTrace_append hprefix tailTrace_366217
  have hstable : (prefixWord ++ tailWord_366217).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366217).length < 2 ^ (prefixWord ++ tailWord_366217).sum := by decide
  have hdescent : baseEnd_366217 < baseStart_366217 := by decide
  rcases family_descends (prefixWord ++ tailWord_366217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366285 : List Nat := [1, 6, 2, 1, 1, 2, 1, 4, 1, 3]
def baseStart_366285 : Nat := 118140960795 + 366285 * 2 ^ 59
def prefixEnd_366285 : Nat := 4983230072969 + 3 ^ 40 * 366285 * 2
def baseEnd_366285 : Nat := 125386841021469761301995

theorem tailTrace_366285 : CollatzResearch.WordTrace tailWord_366285 prefixEnd_366285 125386841021469761301995 := by
  unfold tailWord_366285
  simp only [CollatzResearch.WordTrace]
  refine ⟨13359511478019476342732309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8906340985346317561821539 13359511478019476342732309)
  ·
    refine ⟨626227100532162953565577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 13359511478019476342732309 626227100532162953565577)
    ·
      refine ⟨469670325399122215174183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 626227100532162953565577 469670325399122215174183)
      ·
        refine ⟨704505488098683322761275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 469670325399122215174183 704505488098683322761275)
        ·
          refine ⟨1056758232148024984141913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 704505488098683322761275 1056758232148024984141913)
          ·
            refine ⟨792568674111018738106435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1056758232148024984141913 792568674111018738106435)
            ·
              refine ⟨1188853011166528107159653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792568674111018738106435 1188853011166528107159653)
              ·
                refine ⟨222909939593724020092435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1188853011166528107159653 222909939593724020092435)
                ·
                  refine ⟨334364909390586030138653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 222909939593724020092435 334364909390586030138653)
                  ·
                    refine ⟨125386841021469761301995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334364909390586030138653 125386841021469761301995)
                    ·
                      rfl

theorem cell22_366285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 2, 1, 4, 1, 3].length) (baseStart_366285 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366285 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366285 prefixEnd_366285 := by exact prefixLift 366285
  have htrace : WordTrace (prefixWord ++ tailWord_366285) baseStart_366285 baseEnd_366285 := by
    simpa [prefixWord, tailWord_366285, baseEnd_366285] using wordTrace_append hprefix tailTrace_366285
  have hstable : (prefixWord ++ tailWord_366285).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366285).length < 2 ^ (prefixWord ++ tailWord_366285).sum := by decide
  have hdescent : baseEnd_366285 < baseStart_366285 := by decide
  rcases family_descends (prefixWord ++ tailWord_366285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366326 : List Nat := [5, 1, 1, 1, 1, 3, 1, 5, 4]
def baseStart_366326 : Nat := 118140960795 + 366326 * 2 ^ 59
def prefixEnd_366326 : Nat := 4983230072969 + 3 ^ 40 * 366326 * 2
def baseEnd_366326 : Nat := 41800292053119773675623

theorem tailTrace_366326 : CollatzResearch.WordTrace tailWord_366326 prefixEnd_366326 41800292053119773675623 := by
  unfold tailWord_366326
  simp only [CollatzResearch.WordTrace]
  refine ⟨835062929429433771560927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8907337913913960229983221 835062929429433771560927)
  ·
    refine ⟨1252594394144150657341391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835062929429433771560927 1252594394144150657341391)
    ·
      refine ⟨1878891591216225986012087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1252594394144150657341391 1878891591216225986012087)
      ·
        refine ⟨2818337386824338979018131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1878891591216225986012087 2818337386824338979018131)
        ·
          refine ⟨4227506080236508468527197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2818337386824338979018131 4227506080236508468527197)
          ·
            refine ⟨1585314780088690675697699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4227506080236508468527197 1585314780088690675697699)
            ·
              refine ⟨2377972170133036013546549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1585314780088690675697699 2377972170133036013546549)
              ·
                refine ⟨222934890949972126269989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2377972170133036013546549 222934890949972126269989)
                ·
                  refine ⟨41800292053119773675623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 222934890949972126269989 41800292053119773675623)
                  ·
                    rfl

theorem cell22_366326_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 3, 1, 5, 4].length) (baseStart_366326 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366326 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366326 prefixEnd_366326 := by exact prefixLift 366326
  have htrace : WordTrace (prefixWord ++ tailWord_366326) baseStart_366326 baseEnd_366326 := by
    simpa [prefixWord, tailWord_366326, baseEnd_366326] using wordTrace_append hprefix tailTrace_366326
  have hstable : (prefixWord ++ tailWord_366326).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366326).length < 2 ^ (prefixWord ++ tailWord_366326).sum := by decide
  have hdescent : baseEnd_366326 < baseStart_366326 := by decide
  rcases family_descends (prefixWord ++ tailWord_366326) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366454 : List Nat := [5, 1, 1, 3, 2, 2, 2, 2, 1, 3]
def baseStart_366454 : Nat := 118140960795 + 366454 * 2 ^ 59
def prefixEnd_366454 : Nat := 4983230072969 + 3 ^ 40 * 366454 * 2
def baseEnd_366454 : Nat := 125444693175209653826477

theorem tailTrace_366454 : CollatzResearch.WordTrace tailWord_366454 prefixEnd_366454 125444693175209653826477 := by
  unfold tailWord_366454
  simp only [CollatzResearch.WordTrace]
  refine ⟨835354713400451137852151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8910450276271478803756277 835354713400451137852151)
  ·
    refine ⟨1253032070100676706778227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 835354713400451137852151 1253032070100676706778227)
    ·
      refine ⟨1879548105151015060167341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1253032070100676706778227 1879548105151015060167341)
      ·
        refine ⟨704830539431630647562753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1879548105151015060167341 704830539431630647562753)
        ·
          refine ⟨528622904573722985672065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 704830539431630647562753 528622904573722985672065)
          ·
            refine ⟨396467178430292239254049, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 528622904573722985672065 396467178430292239254049)
            ·
              refine ⟨297350383822719179440537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396467178430292239254049 297350383822719179440537)
              ·
                refine ⟨223012787867039384580403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297350383822719179440537 223012787867039384580403)
                ·
                  refine ⟨334519181800559076870605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223012787867039384580403 334519181800559076870605)
                  ·
                    refine ⟨125444693175209653826477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334519181800559076870605 125444693175209653826477)
                    ·
                      rfl

theorem cell22_366454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 2, 2, 2, 2, 1, 3].length) (baseStart_366454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366454 prefixEnd_366454 := by exact prefixLift 366454
  have htrace : WordTrace (prefixWord ++ tailWord_366454) baseStart_366454 baseEnd_366454 := by
    simpa [prefixWord, tailWord_366454, baseEnd_366454] using wordTrace_append hprefix tailTrace_366454
  have hstable : (prefixWord ++ tailWord_366454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366454).length < 2 ^ (prefixWord ++ tailWord_366454).sum := by decide
  have hdescent : baseEnd_366454 < baseStart_366454 := by decide
  rcases family_descends (prefixWord ++ tailWord_366454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366478 : List Nat := [4, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_366478 : Nat := 118140960795 + 366478 * 2 ^ 59
def prefixEnd_366478 : Nat := 4983230072969 + 3 ^ 40 * 366478 * 2
def baseEnd_366478 : Nat := 41817636288560530408801

theorem tailTrace_366478 : CollatzResearch.WordTrace tailWord_366478 prefixEnd_366478 41817636288560530408801 := by
  unfold tailWord_366478
  simp only [CollatzResearch.WordTrace]
  refine ⟨1670818845790033788063511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8911033844213513536338725 1670818845790033788063511)
  ·
    refine ⟨2506228268685050682095267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1670818845790033788063511 2506228268685050682095267)
    ·
      refine ⟨3759342403027576023142901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2506228268685050682095267 3759342403027576023142901)
      ·
        refine ⟨352438350283835252169647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3759342403027576023142901 352438350283835252169647)
        ·
          refine ⟨528657525425752878254471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352438350283835252169647 528657525425752878254471)
          ·
            refine ⟨792986288138629317381707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 528657525425752878254471 792986288138629317381707)
            ·
              refine ⟨1189479432207943976072561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 792986288138629317381707 1189479432207943976072561)
              ·
                refine ⟨892109574155957982054421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1189479432207943976072561 892109574155957982054421)
                ·
                  refine ⟨41817636288560530408801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 892109574155957982054421 41817636288560530408801)
                  ·
                    rfl

theorem cell22_366478_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_366478 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366478 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366478 prefixEnd_366478 := by exact prefixLift 366478
  have htrace : WordTrace (prefixWord ++ tailWord_366478) baseStart_366478 baseEnd_366478 := by
    simpa [prefixWord, tailWord_366478, baseEnd_366478] using wordTrace_append hprefix tailTrace_366478
  have hstable : (prefixWord ++ tailWord_366478).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366478).length < 2 ^ (prefixWord ++ tailWord_366478).sum := by decide
  have hdescent : baseEnd_366478 < baseStart_366478 := by decide
  rcases family_descends (prefixWord ++ tailWord_366478) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366497 : List Nat := [1, 2, 3, 4, 3, 1, 2, 1, 1, 4]
def baseStart_366497 : Nat := 118140960795 + 366497 * 2 ^ 59
def prefixEnd_366497 : Nat := 4983230072969 + 3 ^ 40 * 366497 * 2
def baseEnd_366497 : Nat := 125459412953971875001345

theorem tailTrace_366497 : CollatzResearch.WordTrace tailWord_366497 prefixEnd_366497 125459412953971875001345 := by
  unfold tailWord_366497
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367243753251436549449745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8911495835500957699633163 13367243753251436549449745)
  ·
    refine ⟨10025432814938577412087309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13367243753251436549449745 10025432814938577412087309)
    ·
      refine ⟨3759537305601966529532741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10025432814938577412087309 3759537305601966529532741)
      ·
        refine ⟨704913244800368724287389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3759537305601966529532741 704913244800368724287389)
        ·
          refine ⟨264342466800138271607771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 704913244800368724287389 264342466800138271607771)
          ·
            refine ⟨396513700200207407411657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264342466800138271607771 396513700200207407411657)
            ·
              refine ⟨297385275150155555558743, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 396513700200207407411657 297385275150155555558743)
              ·
                refine ⟨446077912725233333338115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 297385275150155555558743 446077912725233333338115)
                ·
                  refine ⟨669116869087850000007173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 446077912725233333338115 669116869087850000007173)
                  ·
                    refine ⟨125459412953971875001345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669116869087850000007173 125459412953971875001345)
                    ·
                      rfl

theorem cell22_366497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_366497 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366497 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366497 prefixEnd_366497 := by exact prefixLift 366497
  have htrace : WordTrace (prefixWord ++ tailWord_366497) baseStart_366497 baseEnd_366497 := by
    simpa [prefixWord, tailWord_366497, baseEnd_366497] using wordTrace_append hprefix tailTrace_366497
  have hstable : (prefixWord ++ tailWord_366497).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366497).length < 2 ^ (prefixWord ++ tailWord_366497).sum := by decide
  have hdescent : baseEnd_366497 < baseStart_366497 := by decide
  rcases family_descends (prefixWord ++ tailWord_366497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366611 : List Nat := [1, 1, 1, 2, 1, 4, 2, 1, 6, 3]
def baseStart_366611 : Nat := 118140960795 + 366611 * 2 ^ 59
def prefixEnd_366611 : Nat := 4983230072969 + 3 ^ 40 * 366611 * 2
def baseEnd_366611 : Nat := 125498437483713577650995

theorem tailTrace_366611 : CollatzResearch.WordTrace tailWord_366611 prefixEnd_366611 125498437483713577650995 := by
  unfold tailWord_366611
  simp only [CollatzResearch.WordTrace]
  refine ⟨13371401674838434019099687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8914267783225622679399791 13371401674838434019099687)
  ·
    refine ⟨20057102512257651028649531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13371401674838434019099687 20057102512257651028649531)
    ·
      refine ⟨30085653768386476542974297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20057102512257651028649531 30085653768386476542974297)
      ·
        refine ⟨22564240326289857407230723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30085653768386476542974297 22564240326289857407230723)
        ·
          refine ⟨33846360489434786110846085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22564240326289857407230723 33846360489434786110846085)
          ·
            refine ⟨6346192591769022395783641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33846360489434786110846085 6346192591769022395783641)
            ·
              refine ⟨4759644443826766796837731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6346192591769022395783641 4759644443826766796837731)
              ·
                refine ⟨7139466665740150195256597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759644443826766796837731 7139466665740150195256597)
                ·
                  refine ⟨334662499956569540402653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7139466665740150195256597 334662499956569540402653)
                  ·
                    refine ⟨125498437483713577650995, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334662499956569540402653 125498437483713577650995)
                    ·
                      rfl

theorem cell22_366611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 1, 6, 3].length) (baseStart_366611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366611 prefixEnd_366611 := by exact prefixLift 366611
  have htrace : WordTrace (prefixWord ++ tailWord_366611) baseStart_366611 baseEnd_366611 := by
    simpa [prefixWord, tailWord_366611, baseEnd_366611] using wordTrace_append hprefix tailTrace_366611
  have hstable : (prefixWord ++ tailWord_366611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366611).length < 2 ^ (prefixWord ++ tailWord_366611).sum := by decide
  have hdescent : baseEnd_366611 < baseStart_366611 := by decide
  rcases family_descends (prefixWord ++ tailWord_366611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366624 : List Nat := [2, 1, 1, 18]
def baseStart_366624 : Nat := 118140960795 + 366624 * 2 ^ 59
def prefixEnd_366624 : Nat := 4983230072969 + 3 ^ 40 * 366624 * 2
def baseEnd_366624 : Nat := 172157596226866772395

theorem tailTrace_366624 : CollatzResearch.WordTrace tailWord_366624 prefixEnd_366624 172157596226866772395 := by
  unfold tailWord_366624
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685937911895668619661463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8914583882527558159548617 6685937911895668619661463)
  ·
    refine ⟨10028906867843502929492195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6685937911895668619661463 10028906867843502929492195)
    ·
      refine ⟨15043360301765254394238293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10028906867843502929492195 15043360301765254394238293)
      ·
        refine ⟨172157596226866772395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 18 15043360301765254394238293 172157596226866772395)
        ·
          rfl

theorem cell22_366624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 18].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 18].length) (baseStart_366624 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366624 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366624 prefixEnd_366624 := by exact prefixLift 366624
  have htrace : WordTrace (prefixWord ++ tailWord_366624) baseStart_366624 baseEnd_366624 := by
    simpa [prefixWord, tailWord_366624, baseEnd_366624] using wordTrace_append hprefix tailTrace_366624
  have hstable : (prefixWord ++ tailWord_366624).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366624).length < 2 ^ (prefixWord ++ tailWord_366624).sum := by decide
  have hdescent : baseEnd_366624 < baseStart_366624 := by decide
  rcases family_descends (prefixWord ++ tailWord_366624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366641 : List Nat := [1, 2, 2, 3, 1, 3, 3, 7]
def baseStart_366641 : Nat := 118140960795 + 366641 * 2 ^ 59
def prefixEnd_366641 : Nat := 4983230072969 + 3 ^ 40 * 366641 * 2
def baseEnd_366641 : Nat := 13945411899644833266767

theorem tailTrace_366641 : CollatzResearch.WordTrace tailWord_366641 prefixEnd_366641 13945411899644833266767 := by
  unfold tailWord_366641
  simp only [CollatzResearch.WordTrace]
  refine ⟨13372495864729749142691777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8914997243153166095127851 13372495864729749142691777)
  ·
    refine ⟨10029371898547311857018833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13372495864729749142691777 10029371898547311857018833)
    ·
      refine ⟨7522028923910483892764125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10029371898547311857018833 7522028923910483892764125)
      ·
        refine ⟨2820760846466431459786547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7522028923910483892764125 2820760846466431459786547)
        ·
          refine ⟨4231141269699647189679821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2820760846466431459786547 4231141269699647189679821)
          ·
            refine ⟨1586677976137367696129933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4231141269699647189679821 1586677976137367696129933)
            ·
              refine ⟨595004241051512886048725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1586677976137367696129933 595004241051512886048725)
              ·
                refine ⟨13945411899644833266767, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 595004241051512886048725 13945411899644833266767)
                ·
                  rfl

theorem cell22_366641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 3, 7].length) (baseStart_366641 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366641 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366641 prefixEnd_366641 := by exact prefixLift 366641
  have htrace : WordTrace (prefixWord ++ tailWord_366641) baseStart_366641 baseEnd_366641 := by
    simpa [prefixWord, tailWord_366641, baseEnd_366641] using wordTrace_append hprefix tailTrace_366641
  have hstable : (prefixWord ++ tailWord_366641).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366641).length < 2 ^ (prefixWord ++ tailWord_366641).sum := by decide
  have hdescent : baseEnd_366641 < baseStart_366641 := by decide
  rcases family_descends (prefixWord ++ tailWord_366641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366776 : List Nat := [2, 1, 2, 1, 2, 1, 3, 10]
def baseStart_366776 : Nat := 118140960795 + 366776 * 2 ^ 59
def prefixEnd_366776 : Nat := 4983230072969 + 3 ^ 40 * 366776 * 2
def baseEnd_366776 : Nat := 13950546706189794141721

theorem tailTrace_366776 : CollatzResearch.WordTrace tailWord_366776 prefixEnd_366776 13950546706189794141721 := by
  unfold tailWord_366776
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688709859620333599428091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8918279812827111465904121 6688709859620333599428091)
  ·
    refine ⟨10033064789430500399142137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6688709859620333599428091 10033064789430500399142137)
    ·
      refine ⟨7524798592072875299356603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10033064789430500399142137 7524798592072875299356603)
      ·
        refine ⟨11287197888109312949034905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7524798592072875299356603 11287197888109312949034905)
        ·
          refine ⟨8465398416081984711776179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11287197888109312949034905 8465398416081984711776179)
          ·
            refine ⟨12698097624122977067664269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8465398416081984711776179 12698097624122977067664269)
            ·
              refine ⟨4761786609046116400374101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12698097624122977067664269 4761786609046116400374101)
              ·
                refine ⟨13950546706189794141721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 4761786609046116400374101 13950546706189794141721)
                ·
                  rfl

theorem cell22_366776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 3, 10].length) (baseStart_366776 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366776 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366776 prefixEnd_366776 := by exact prefixLift 366776
  have htrace : WordTrace (prefixWord ++ tailWord_366776) baseStart_366776 baseEnd_366776 := by
    simpa [prefixWord, tailWord_366776, baseEnd_366776] using wordTrace_append hprefix tailTrace_366776
  have hstable : (prefixWord ++ tailWord_366776).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366776).length < 2 ^ (prefixWord ++ tailWord_366776).sum := by decide
  have hdescent : baseEnd_366776 < baseStart_366776 := by decide
  rcases family_descends (prefixWord ++ tailWord_366776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366778 : List Nat := [3, 1, 1, 1, 2, 2, 3, 3, 2, 4]
def baseStart_366778 : Nat := 118140960795 + 366778 * 2 ^ 59
def prefixEnd_366778 : Nat := 4983230072969 + 3 ^ 40 * 366778 * 2
def baseEnd_366778 : Nat := 125555604996580808725483

theorem tailTrace_366778 : CollatzResearch.WordTrace tailWord_366778 prefixEnd_366778 125555604996580808725483 := by
  unfold tailWord_366778
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344373166308355385107247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8918328443488947693619325 3344373166308355385107247)
  ·
    refine ⟨5016559749462533077660871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3344373166308355385107247 5016559749462533077660871)
    ·
      refine ⟨7524839624193799616491307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5016559749462533077660871 7524839624193799616491307)
      ·
        refine ⟨11287259436290699424736961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7524839624193799616491307 11287259436290699424736961)
        ·
          refine ⟨8465444577218024568552721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11287259436290699424736961 8465444577218024568552721)
          ·
            refine ⟨6349083432913518426414541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8465444577218024568552721 6349083432913518426414541)
            ·
              refine ⟨2380906287342569409905453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6349083432913518426414541 2380906287342569409905453)
              ·
                refine ⟨892839857753463528714545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2380906287342569409905453 892839857753463528714545)
                ·
                  refine ⟨669629893315097646535909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892839857753463528714545 669629893315097646535909)
                  ·
                    refine ⟨125555604996580808725483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669629893315097646535909 125555604996580808725483)
                    ·
                      rfl

theorem cell22_366778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 2, 3, 3, 2, 4].length) (baseStart_366778 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366778 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366778 prefixEnd_366778 := by exact prefixLift 366778
  have htrace : WordTrace (prefixWord ++ tailWord_366778) baseStart_366778 baseEnd_366778 := by
    simpa [prefixWord, tailWord_366778, baseEnd_366778] using wordTrace_append hprefix tailTrace_366778
  have hstable : (prefixWord ++ tailWord_366778).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366778).length < 2 ^ (prefixWord ++ tailWord_366778).sum := by decide
  have hdescent : baseEnd_366778 < baseStart_366778 := by decide
  rcases family_descends (prefixWord ++ tailWord_366778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366780 : List Nat := [2, 2, 2, 3, 3, 1, 1, 2, 1, 5]
def baseStart_366780 : Nat := 118140960795 + 366780 * 2 ^ 59
def prefixEnd_366780 : Nat := 4983230072969 + 3 ^ 40 * 366780 * 2
def baseEnd_366780 : Nat := 125556289637453470175477

theorem tailTrace_366780 : CollatzResearch.WordTrace tailWord_366780 prefixEnd_366780 125556289637453470175477 := by
  unfold tailWord_366780
  simp only [CollatzResearch.WordTrace]
  refine ⟨6688782805613087941000897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8918377074150783921334529 6688782805613087941000897)
  ·
    refine ⟨5016587104209815955750673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6688782805613087941000897 5016587104209815955750673)
    ·
      refine ⟨3762440328157361966813005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5016587104209815955750673 3762440328157361966813005)
      ·
        refine ⟨1410915123059010737554877, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3762440328157361966813005 1410915123059010737554877)
        ·
          refine ⟨529093171147129026583079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1410915123059010737554877 529093171147129026583079)
          ·
            refine ⟨793639756720693539874619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529093171147129026583079 793639756720693539874619)
            ·
              refine ⟨1190459635081040309811929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 793639756720693539874619 1190459635081040309811929)
              ·
                refine ⟨892844726310780232358947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1190459635081040309811929 892844726310780232358947)
                ·
                  refine ⟨1339267089466170348538421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 892844726310780232358947 1339267089466170348538421)
                  ·
                    refine ⟨125556289637453470175477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1339267089466170348538421 125556289637453470175477)
                    ·
                      rfl

theorem cell22_366780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 3, 1, 1, 2, 1, 5].length) (baseStart_366780 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366780 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366780 prefixEnd_366780 := by exact prefixLift 366780
  have htrace : WordTrace (prefixWord ++ tailWord_366780) baseStart_366780 baseEnd_366780 := by
    simpa [prefixWord, tailWord_366780, baseEnd_366780] using wordTrace_append hprefix tailTrace_366780
  have hstable : (prefixWord ++ tailWord_366780).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366780).length < 2 ^ (prefixWord ++ tailWord_366780).sum := by decide
  have hdescent : baseEnd_366780 < baseStart_366780 := by decide
  rcases family_descends (prefixWord ++ tailWord_366780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366829 : List Nat := [1, 5, 1, 2, 4, 1, 1, 1, 2, 4]
def baseStart_366829 : Nat := 118140960795 + 366829 * 2 ^ 59
def prefixEnd_366829 : Nat := 4983230072969 + 3 ^ 40 * 366829 * 2
def baseEnd_366829 : Nat := 125573063338833675700327

theorem tailTrace_366829 : CollatzResearch.WordTrace tailWord_366829 prefixEnd_366829 125573063338833675700327 := by
  unfold tailWord_366829
  simp only [CollatzResearch.WordTrace]
  refine ⟨13379352788048657250535541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8919568525365771500357027 13379352788048657250535541)
  ·
    refine ⟨1254314323879561617237707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13379352788048657250535541 1254314323879561617237707)
    ·
      refine ⟨1881471485819342425856561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1254314323879561617237707 1881471485819342425856561)
      ·
        refine ⟨1411103614364506819392421, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1881471485819342425856561 1411103614364506819392421)
        ·
          refine ⟨264581927693345028636079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1411103614364506819392421 264581927693345028636079)
          ·
            refine ⟨396872891540017542954119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 264581927693345028636079 396872891540017542954119)
            ·
              refine ⟨595309337310026314431179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396872891540017542954119 595309337310026314431179)
              ·
                refine ⟨892964005965039471646769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595309337310026314431179 892964005965039471646769)
                ·
                  refine ⟨669723004473779603735077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 892964005965039471646769 669723004473779603735077)
                  ·
                    refine ⟨125573063338833675700327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 669723004473779603735077 125573063338833675700327)
                    ·
                      rfl

theorem cell22_366829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 4, 1, 1, 1, 2, 4].length) (baseStart_366829 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366829 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366829 prefixEnd_366829 := by exact prefixLift 366829
  have htrace : WordTrace (prefixWord ++ tailWord_366829) baseStart_366829 baseEnd_366829 := by
    simpa [prefixWord, tailWord_366829, baseEnd_366829] using wordTrace_append hprefix tailTrace_366829
  have hstable : (prefixWord ++ tailWord_366829).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366829).length < 2 ^ (prefixWord ++ tailWord_366829).sum := by decide
  have hdescent : baseEnd_366829 < baseStart_366829 := by decide
  rcases family_descends (prefixWord ++ tailWord_366829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366842 : List Nat := [3, 1, 1, 1, 1, 5, 1, 5, 1, 3]
def baseStart_366842 : Nat := 118140960795 + 366842 * 2 ^ 59
def prefixEnd_366842 : Nat := 4983230072969 + 3 ^ 40 * 366842 * 2
def baseEnd_366842 : Nat := 125577513504505975125287

theorem tailTrace_366842 : CollatzResearch.WordTrace tailWord_366842 prefixEnd_366842 125577513504505975125287 := by
  unfold tailWord_366842
  simp only [CollatzResearch.WordTrace]
  refine ⟨3344956734250390117689695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8919884624667706980505853 3344956734250390117689695)
  ·
    refine ⟨5017435101375585176534543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3344956734250390117689695 5017435101375585176534543)
    ·
      refine ⟨7526152652063377764801815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5017435101375585176534543 7526152652063377764801815)
      ·
        refine ⟨11289228978095066647202723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7526152652063377764801815 11289228978095066647202723)
        ·
          refine ⟨16933843467142599970804085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11289228978095066647202723 16933843467142599970804085)
          ·
            refine ⟨1587547825044618747262883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16933843467142599970804085 1587547825044618747262883)
            ·
              refine ⟨2381321737566928120894325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587547825044618747262883 2381321737566928120894325)
              ·
                refine ⟨223248912896899511333843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2381321737566928120894325 223248912896899511333843)
                ·
                  refine ⟨334873369345349267000765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223248912896899511333843 334873369345349267000765)
                  ·
                    refine ⟨125577513504505975125287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334873369345349267000765 125577513504505975125287)
                    ·
                      rfl

theorem cell22_366842_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 5, 1, 5, 1, 3].length) (baseStart_366842 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366842 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366842 prefixEnd_366842 := by exact prefixLift 366842
  have htrace : WordTrace (prefixWord ++ tailWord_366842) baseStart_366842 baseEnd_366842 := by
    simpa [prefixWord, tailWord_366842, baseEnd_366842] using wordTrace_append hprefix tailTrace_366842
  have hstable : (prefixWord ++ tailWord_366842).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366842).length < 2 ^ (prefixWord ++ tailWord_366842).sum := by decide
  have hdescent : baseEnd_366842 < baseStart_366842 := by decide
  rcases family_descends (prefixWord ++ tailWord_366842) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366883 : List Nat := [1, 1, 1, 4, 2, 2, 1, 4, 6]
def baseStart_366883 : Nat := 118140960795 + 366883 * 2 ^ 59
def prefixEnd_366883 : Nat := 4983230072969 + 3 ^ 40 * 366883 * 2
def baseEnd_366883 : Nat := 41863849547465178283387

theorem tailTrace_366883 : CollatzResearch.WordTrace tailWord_366883 prefixEnd_366883 41863849547465178283387 := by
  unfold tailWord_366883
  simp only [CollatzResearch.WordTrace]
  refine ⟨13381322329853024473001303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8920881553235349648667535 13381322329853024473001303)
  ·
    refine ⟨20071983494779536709501955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13381322329853024473001303 20071983494779536709501955)
    ·
      refine ⟨30107975242169305064252933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20071983494779536709501955 30107975242169305064252933)
      ·
        refine ⟨5645245357906744699547425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30107975242169305064252933 5645245357906744699547425)
        ·
          refine ⟨4233934018430058524660569, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5645245357906744699547425 4233934018430058524660569)
          ·
            refine ⟨3175450513822543893495427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4233934018430058524660569 3175450513822543893495427)
            ·
              refine ⟨4763175770733815840243141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3175450513822543893495427 4763175770733815840243141)
              ·
                refine ⟨893095457012590470045589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4763175770733815840243141 893095457012590470045589)
                ·
                  refine ⟨41863849547465178283387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 893095457012590470045589 41863849547465178283387)
                  ·
                    rfl

theorem cell22_366883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 1, 4, 6].length) (baseStart_366883 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366883 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366883 prefixEnd_366883 := by exact prefixLift 366883
  have htrace : WordTrace (prefixWord ++ tailWord_366883) baseStart_366883 baseEnd_366883 := by
    simpa [prefixWord, tailWord_366883, baseEnd_366883] using wordTrace_append hprefix tailTrace_366883
  have hstable : (prefixWord ++ tailWord_366883).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366883).length < 2 ^ (prefixWord ++ tailWord_366883).sum := by decide
  have hdescent : baseEnd_366883 < baseStart_366883 := by decide
  rcases family_descends (prefixWord ++ tailWord_366883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366893 : List Nat := [1, 5, 3, 1, 2, 2, 1, 3, 1, 3]
def baseStart_366893 : Nat := 118140960795 + 366893 * 2 ^ 59
def prefixEnd_366893 : Nat := 4983230072969 + 3 ^ 40 * 366893 * 2
def baseEnd_366893 : Nat := 125594971846758842100131

theorem tailTrace_366893 : CollatzResearch.WordTrace tailWord_366893 prefixEnd_366893 125594971846758842100131 := by
  unfold tailWord_366893
  simp only [CollatzResearch.WordTrace]
  refine ⟨13381687059816796180865333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8921124706544530787243555 13381687059816796180865333)
  ·
    refine ⟨1254533161857824641956125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13381687059816796180865333 1254533161857824641956125)
    ·
      refine ⟨470449935696684240733547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1254533161857824641956125 470449935696684240733547)
      ·
        refine ⟨705674903545026361100321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 470449935696684240733547 705674903545026361100321)
        ·
          refine ⟨529256177658769770825241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 705674903545026361100321 529256177658769770825241)
          ·
            refine ⟨396942133244077328118931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 529256177658769770825241 396942133244077328118931)
            ·
              refine ⟨595413199866115992178397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 396942133244077328118931 595413199866115992178397)
              ·
                refine ⟨223279949949793497066899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 595413199866115992178397 223279949949793497066899)
                ·
                  refine ⟨334919924924690245600349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223279949949793497066899 334919924924690245600349)
                  ·
                    refine ⟨125594971846758842100131, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334919924924690245600349 125594971846758842100131)
                    ·
                      rfl

theorem cell22_366893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 2, 2, 1, 3, 1, 3].length) (baseStart_366893 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366893 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366893 prefixEnd_366893 := by exact prefixLift 366893
  have htrace : WordTrace (prefixWord ++ tailWord_366893) baseStart_366893 baseEnd_366893 := by
    simpa [prefixWord, tailWord_366893, baseEnd_366893] using wordTrace_append hprefix tailTrace_366893
  have hstable : (prefixWord ++ tailWord_366893).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366893).length < 2 ^ (prefixWord ++ tailWord_366893).sum := by decide
  have hdescent : baseEnd_366893 < baseStart_366893 := by decide
  rcases family_descends (prefixWord ++ tailWord_366893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366915 : List Nat := [1, 1, 1, 3, 1, 3, 4, 1, 4, 3]
def baseStart_366915 : Nat := 118140960795 + 366915 * 2 ^ 59
def prefixEnd_366915 : Nat := 4983230072969 + 3 ^ 40 * 366915 * 2
def baseEnd_366915 : Nat := 125602502896358118050063

theorem tailTrace_366915 : CollatzResearch.WordTrace tailWord_366915 prefixEnd_366915 125602502896358118050063 := by
  unfold tailWord_366915
  simp only [CollatzResearch.WordTrace]
  refine ⟨13382489465737093938166199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8921659643824729292110799 13382489465737093938166199)
  ·
    refine ⟨20073734198605640907249299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13382489465737093938166199 20073734198605640907249299)
    ·
      refine ⟨30110601297908461360873949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20073734198605640907249299 30110601297908461360873949)
      ·
        refine ⟨11291475486715673010327731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30110601297908461360873949 11291475486715673010327731)
        ·
          refine ⟨16937213230073509515491597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11291475486715673010327731 16937213230073509515491597)
          ·
            refine ⟨6351454961277566068309349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16937213230073509515491597 6351454961277566068309349)
            ·
              refine ⟨1190897805239543637808003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6351454961277566068309349 1190897805239543637808003)
              ·
                refine ⟨1786346707859315456712005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1190897805239543637808003 1786346707859315456712005)
                ·
                  refine ⟨334940007723621648133501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1786346707859315456712005 334940007723621648133501)
                  ·
                    refine ⟨125602502896358118050063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 334940007723621648133501 125602502896358118050063)
                    ·
                      rfl

theorem cell22_366915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 3, 4, 1, 4, 3].length) (baseStart_366915 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366915 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366915 prefixEnd_366915 := by exact prefixLift 366915
  have htrace : WordTrace (prefixWord ++ tailWord_366915) baseStart_366915 baseEnd_366915 := by
    simpa [prefixWord, tailWord_366915, baseEnd_366915] using wordTrace_append hprefix tailTrace_366915
  have hstable : (prefixWord ++ tailWord_366915).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366915).length < 2 ^ (prefixWord ++ tailWord_366915).sum := by decide
  have hdescent : baseEnd_366915 < baseStart_366915 := by decide
  rcases family_descends (prefixWord ++ tailWord_366915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366928 : List Nat := [2, 1, 1, 1, 1, 6, 1, 9]
def baseStart_366928 : Nat := 118140960795 + 366928 * 2 ^ 59
def prefixEnd_366928 : Nat := 4983230072969 + 3 ^ 40 * 366928 * 2
def baseEnd_366928 : Nat := 13956328118003379719447

theorem tailTrace_366928 : CollatzResearch.WordTrace tailWord_366928 prefixEnd_366928 13956328118003379719447 := by
  unfold tailWord_366928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6691481807344998579194719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8921975743126664772259625 6691481807344998579194719)
  ·
    refine ⟨10037222711017497868792079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6691481807344998579194719 10037222711017497868792079)
    ·
      refine ⟨15055834066526246803188119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10037222711017497868792079 15055834066526246803188119)
      ·
        refine ⟨22583751099789370204782179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15055834066526246803188119 22583751099789370204782179)
        ·
          refine ⟨33875626649684055307173269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22583751099789370204782179 33875626649684055307173269)
          ·
            refine ⟨1587919999203940092523747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 33875626649684055307173269 1587919999203940092523747)
            ·
              refine ⟨2381879998805910138785621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1587919999203940092523747 2381879998805910138785621)
              ·
                refine ⟨13956328118003379719447, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2381879998805910138785621 13956328118003379719447)
                ·
                  rfl

theorem cell22_366928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 6, 1, 9].length) (baseStart_366928 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366928 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366928 prefixEnd_366928 := by exact prefixLift 366928
  have htrace : WordTrace (prefixWord ++ tailWord_366928) baseStart_366928 baseEnd_366928 := by
    simpa [prefixWord, tailWord_366928, baseEnd_366928] using wordTrace_append hprefix tailTrace_366928
  have hstable : (prefixWord ++ tailWord_366928).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366928).length < 2 ^ (prefixWord ++ tailWord_366928).sum := by decide
  have hdescent : baseEnd_366928 < baseStart_366928 := by decide
  rcases family_descends (prefixWord ++ tailWord_366928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_366943 : List Nat := [1, 1, 2, 3, 1, 2, 2, 1, 2, 7]
def baseStart_366943 : Nat := 118140960795 + 366943 * 2 ^ 59
def prefixEnd_366943 : Nat := 4983230072969 + 3 ^ 40 * 366943 * 2
def baseEnd_366943 : Nat := 125612087868575378349977

theorem tailTrace_366943 : CollatzResearch.WordTrace tailWord_366943 prefixEnd_366943 125612087868575378349977 := by
  unfold tailWord_366943
  simp only [CollatzResearch.WordTrace]
  refine ⟨13383510709635654720185483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8922340473090436480123655 13383510709635654720185483)
  ·
    refine ⟨20075266064453482080278225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13383510709635654720185483 20075266064453482080278225)
    ·
      refine ⟨15056449548340111560208669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20075266064453482080278225 15056449548340111560208669)
      ·
        refine ⟨5646168580627541835078251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15056449548340111560208669 5646168580627541835078251)
        ·
          refine ⟨8469252870941312752617377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5646168580627541835078251 8469252870941312752617377)
          ·
            refine ⟨6351939653205984564463033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8469252870941312752617377 6351939653205984564463033)
            ·
              refine ⟨4763954739904488423347275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6351939653205984564463033 4763954739904488423347275)
              ·
                refine ⟨7145932109856732635020913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4763954739904488423347275 7145932109856732635020913)
                ·
                  refine ⟨5359449082392549476265685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7145932109856732635020913 5359449082392549476265685)
                  ·
                    refine ⟨125612087868575378349977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 5359449082392549476265685 125612087868575378349977)
                    ·
                      rfl

theorem cell22_366943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 2, 1, 2, 7].length) (baseStart_366943 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_366943 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_366943 prefixEnd_366943 := by exact prefixLift 366943
  have htrace : WordTrace (prefixWord ++ tailWord_366943) baseStart_366943 baseEnd_366943 := by
    simpa [prefixWord, tailWord_366943, baseEnd_366943] using wordTrace_append hprefix tailTrace_366943
  have hstable : (prefixWord ++ tailWord_366943).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_366943).length < 2 ^ (prefixWord ++ tailWord_366943).sum := by decide
  have hdescent : baseEnd_366943 < baseStart_366943 := by decide
  rcases family_descends (prefixWord ++ tailWord_366943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367028 : List Nat := [2, 5, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_367028 : Nat := 118140960795 + 367028 * 2 ^ 59
def prefixEnd_367028 : Nat := 4983230072969 + 3 ^ 40 * 367028 * 2
def baseEnd_367028 : Nat := 125641185105663489974717

theorem tailTrace_367028 : CollatzResearch.WordTrace tailWord_367028 prefixEnd_367028 125641185105663489974717 := by
  unfold tailWord_367028
  simp only [CollatzResearch.WordTrace]
  refine ⟨6693305457163857118514869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8924407276218476158019825 6693305457163857118514869)
  ·
    refine ⟨627497386609111604860769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6693305457163857118514869 627497386609111604860769)
    ·
      refine ⟨470623039956833703645577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 627497386609111604860769 470623039956833703645577)
      ·
        refine ⟨352967279967625277734183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 470623039956833703645577 352967279967625277734183)
        ·
          refine ⟨529450919951437916601275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 352967279967625277734183 529450919951437916601275)
          ·
            refine ⟨794176379927156874901913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529450919951437916601275 794176379927156874901913)
            ·
              refine ⟨595632284945367656176435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794176379927156874901913 595632284945367656176435)
              ·
                refine ⟨893448427418051484264653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 595632284945367656176435 893448427418051484264653)
                ·
                  refine ⟨335043160281769306599245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 893448427418051484264653 335043160281769306599245)
                  ·
                    refine ⟨125641185105663489974717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335043160281769306599245 125641185105663489974717)
                    ·
                      rfl

theorem cell22_367028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_367028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367028 prefixEnd_367028 := by exact prefixLift 367028
  have htrace : WordTrace (prefixWord ++ tailWord_367028) baseStart_367028 baseEnd_367028 := by
    simpa [prefixWord, tailWord_367028, baseEnd_367028] using wordTrace_append hprefix tailTrace_367028
  have hstable : (prefixWord ++ tailWord_367028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367028).length < 2 ^ (prefixWord ++ tailWord_367028).sum := by decide
  have hdescent : baseEnd_367028 < baseStart_367028 := by decide
  rcases family_descends (prefixWord ++ tailWord_367028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367065 : List Nat := [1, 2, 1, 2, 4, 1, 1, 3, 1, 6]
def baseStart_367065 : Nat := 118140960795 + 367065 * 2 ^ 59
def prefixEnd_367065 : Nat := 4983230072969 + 3 ^ 40 * 367065 * 2
def baseEnd_367065 : Nat := 125653850961807726799603

theorem tailTrace_367065 : CollatzResearch.WordTrace tailWord_367065 prefixEnd_367065 125653850961807726799603 := by
  unfold tailWord_367065
  simp only [CollatzResearch.WordTrace]
  refine ⟨13387960415193669556126649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8925306943462446370751099 13387960415193669556126649)
  ·
    refine ⟨10040970311395252167094987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13387960415193669556126649 10040970311395252167094987)
    ·
      refine ⟨15061455467092878250642481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10040970311395252167094987 15061455467092878250642481)
      ·
        refine ⟨11296091600319658687981861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15061455467092878250642481 11296091600319658687981861)
        ·
          refine ⟨2118017175059936003996599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 11296091600319658687981861 2118017175059936003996599)
          ·
            refine ⟨3177025762589904005994899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2118017175059936003996599 3177025762589904005994899)
            ·
              refine ⟨4765538643884856008992349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3177025762589904005994899 4765538643884856008992349)
              ·
                refine ⟨1787076991456821003372131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4765538643884856008992349 1787076991456821003372131)
                ·
                  refine ⟨2680615487185231505058197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1787076991456821003372131 2680615487185231505058197)
                  ·
                    refine ⟨125653850961807726799603, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 2680615487185231505058197 125653850961807726799603)
                    ·
                      rfl

theorem cell22_367065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 1, 3, 1, 6].length) (baseStart_367065 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367065 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367065 prefixEnd_367065 := by exact prefixLift 367065
  have htrace : WordTrace (prefixWord ++ tailWord_367065) baseStart_367065 baseEnd_367065 := by
    simpa [prefixWord, tailWord_367065, baseEnd_367065] using wordTrace_append hprefix tailTrace_367065
  have hstable : (prefixWord ++ tailWord_367065).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367065).length < 2 ^ (prefixWord ++ tailWord_367065).sum := by decide
  have hdescent : baseEnd_367065 < baseStart_367065 := by decide
  rcases family_descends (prefixWord ++ tailWord_367065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367080 : List Nat := [2, 1, 4, 1, 1, 3, 10]
def baseStart_367080 : Nat := 118140960795 + 367080 * 2 ^ 59
def prefixEnd_367080 : Nat := 4983230072969 + 3 ^ 40 * 367080 * 2
def baseEnd_367080 : Nat := 4654036509938988432391

theorem tailTrace_367080 : CollatzResearch.WordTrace tailWord_367080 prefixEnd_367080 4654036509938988432391 := by
  unfold tailWord_367080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6694253755069663558961347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8925671673426218078615129 6694253755069663558961347)
  ·
    refine ⟨10041380632604495338442021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6694253755069663558961347 10041380632604495338442021)
    ·
      refine ⟨1882758868613342875957879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 10041380632604495338442021 1882758868613342875957879)
      ·
        refine ⟨2824138302920014313936819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882758868613342875957879 2824138302920014313936819)
        ·
          refine ⟨4236207454380021470905229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824138302920014313936819 4236207454380021470905229)
          ·
            refine ⟨1588577795392508051589461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4236207454380021470905229 1588577795392508051589461)
            ·
              refine ⟨4654036509938988432391, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1588577795392508051589461 4654036509938988432391)
              ·
                rfl

theorem cell22_367080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 10].length) (baseStart_367080 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367080 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367080 prefixEnd_367080 := by exact prefixLift 367080
  have htrace : WordTrace (prefixWord ++ tailWord_367080) baseStart_367080 baseEnd_367080 := by
    simpa [prefixWord, tailWord_367080, baseEnd_367080] using wordTrace_append hprefix tailTrace_367080
  have hstable : (prefixWord ++ tailWord_367080).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367080).length < 2 ^ (prefixWord ++ tailWord_367080).sum := by decide
  have hdescent : baseEnd_367080 < baseStart_367080 := by decide
  rcases family_descends (prefixWord ++ tailWord_367080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367082 : List Nat := [3, 1, 3, 1, 3, 1, 1, 1, 4, 4]
def baseStart_367082 : Nat := 118140960795 + 367082 * 2 ^ 59
def prefixEnd_367082 : Nat := 4983230072969 + 3 ^ 40 * 367082 * 2
def baseEnd_367082 : Nat := 125659670409225349124551

theorem tailTrace_367082 : CollatzResearch.WordTrace tailWord_367082 prefixEnd_367082 125659670409225349124551 := by
  unfold tailWord_367082
  simp only [CollatzResearch.WordTrace]
  refine ⟨3347145114033020364873875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8925720304088054306330333 3347145114033020364873875)
  ·
    refine ⟨5020717671049530547310813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3347145114033020364873875 5020717671049530547310813)
    ·
      refine ⟨1882769126643573955241555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5020717671049530547310813 1882769126643573955241555)
      ·
        refine ⟨2824153689965360932862333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882769126643573955241555 2824153689965360932862333)
        ·
          refine ⟨1059057633737010349823375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2824153689965360932862333 1059057633737010349823375)
          ·
            refine ⟨1588586450605515524735063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1059057633737010349823375 1588586450605515524735063)
            ·
              refine ⟨2382879675908273287102595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1588586450605515524735063 2382879675908273287102595)
              ·
                refine ⟨3574319513862409930653893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2382879675908273287102595 3574319513862409930653893)
                ·
                  refine ⟨670184908849201861997605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 3574319513862409930653893 670184908849201861997605)
                  ·
                    refine ⟨125659670409225349124551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670184908849201861997605 125659670409225349124551)
                    ·
                      rfl

theorem cell22_367082_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 1, 1, 1, 4, 4].length) (baseStart_367082 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367082 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367082 prefixEnd_367082 := by exact prefixLift 367082
  have htrace : WordTrace (prefixWord ++ tailWord_367082) baseStart_367082 baseEnd_367082 := by
    simpa [prefixWord, tailWord_367082, baseEnd_367082] using wordTrace_append hprefix tailTrace_367082
  have hstable : (prefixWord ++ tailWord_367082).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367082).length < 2 ^ (prefixWord ++ tailWord_367082).sum := by decide
  have hdescent : baseEnd_367082 < baseStart_367082 := by decide
  rcases family_descends (prefixWord ++ tailWord_367082) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367086 : List Nat := [4, 1, 2, 1, 2, 3, 3, 2, 4]
def baseStart_367086 : Nat := 118140960795 + 367086 * 2 ^ 59
def prefixEnd_367086 : Nat := 4983230072969 + 3 ^ 40 * 367086 * 2
def baseEnd_367086 : Nat := 41887013230323557341513

theorem tailTrace_367086 : CollatzResearch.WordTrace tailWord_367086 prefixEnd_367086 41887013230323557341513 := by
  unfold tailWord_367086
  simp only [CollatzResearch.WordTrace]
  refine ⟨1673590793514698767830139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8925817565411726761760741 1673590793514698767830139)
  ·
    refine ⟨2510386190272048151745209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1673590793514698767830139 2510386190272048151745209)
    ·
      refine ⟨1882789642704036113808907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2510386190272048151745209 1882789642704036113808907)
      ·
        refine ⟨2824184464056054170713361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1882789642704036113808907 2824184464056054170713361)
        ·
          refine ⟨2118138348042040628035021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2824184464056054170713361 2118138348042040628035021)
          ·
            refine ⟨794301880515765235513133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2118138348042040628035021 794301880515765235513133)
            ·
              refine ⟨297863205193411963317425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 794301880515765235513133 297863205193411963317425)
              ·
                refine ⟨223397403895058972488069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 297863205193411963317425 223397403895058972488069)
                ·
                  refine ⟨41887013230323557341513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223397403895058972488069 41887013230323557341513)
                  ·
                    rfl

theorem cell22_367086_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 2, 3, 3, 2, 4].length) (baseStart_367086 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367086 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367086 prefixEnd_367086 := by exact prefixLift 367086
  have htrace : WordTrace (prefixWord ++ tailWord_367086) baseStart_367086 baseEnd_367086 := by
    simpa [prefixWord, tailWord_367086, baseEnd_367086] using wordTrace_append hprefix tailTrace_367086
  have hstable : (prefixWord ++ tailWord_367086).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367086).length < 2 ^ (prefixWord ++ tailWord_367086).sum := by decide
  have hdescent : baseEnd_367086 < baseStart_367086 := by decide
  rcases family_descends (prefixWord ++ tailWord_367086) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367112 : List Nat := [2, 1, 3, 2, 1, 1, 1, 3, 5, 3]
def baseStart_367112 : Nat := 118140960795 + 367112 * 2 ^ 59
def prefixEnd_367112 : Nat := 4983230072969 + 3 ^ 40 * 367112 * 2
def baseEnd_367112 : Nat := 125669940022315270874459

theorem tailTrace_367112 : CollatzResearch.WordTrace tailWord_367112 prefixEnd_367112 125669940022315270874459 := by
  unfold tailWord_367112
  simp only [CollatzResearch.WordTrace]
  refine ⟨6694837323011698291543795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8926449764015597722058393 6694837323011698291543795)
  ·
    refine ⟨10042255984517547437315693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6694837323011698291543795 10042255984517547437315693)
    ·
      refine ⟨3765845994194080288993385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10042255984517547437315693 3765845994194080288993385)
      ·
        refine ⟨2824384495645560216745039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3765845994194080288993385 2824384495645560216745039)
        ·
          refine ⟨4236576743468340325117559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824384495645560216745039 4236576743468340325117559)
          ·
            refine ⟨6354865115202510487676339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4236576743468340325117559 6354865115202510487676339)
            ·
              refine ⟨9532297672803765731514509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6354865115202510487676339 9532297672803765731514509)
              ·
                refine ⟨3574611627301412149317941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9532297672803765731514509 3574611627301412149317941)
                ·
                  refine ⟨335119840059507388998557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3574611627301412149317941 335119840059507388998557)
                  ·
                    refine ⟨125669940022315270874459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335119840059507388998557 125669940022315270874459)
                    ·
                      rfl

theorem cell22_367112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 3, 5, 3].length) (baseStart_367112 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367112 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367112 prefixEnd_367112 := by exact prefixLift 367112
  have htrace : WordTrace (prefixWord ++ tailWord_367112) baseStart_367112 baseEnd_367112 := by
    simpa [prefixWord, tailWord_367112, baseEnd_367112] using wordTrace_append hprefix tailTrace_367112
  have hstable : (prefixWord ++ tailWord_367112).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367112).length < 2 ^ (prefixWord ++ tailWord_367112).sum := by decide
  have hdescent : baseEnd_367112 < baseStart_367112 := by decide
  rcases family_descends (prefixWord ++ tailWord_367112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367157 : List Nat := [1, 3, 3, 1, 1, 2, 3, 1, 2, 5]
def baseStart_367157 : Nat := 118140960795 + 367157 * 2 ^ 59
def prefixEnd_367157 : Nat := 4983230072969 + 3 ^ 40 * 367157 * 2
def baseEnd_367157 : Nat := 125685344441950153499321

theorem tailTrace_367157 : CollatzResearch.WordTrace tailWord_367157 prefixEnd_367157 125685344441950153499321 := by
  unfold tailWord_367157
  simp only [CollatzResearch.WordTrace]
  refine ⟨13391315930860369268475725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8927543953906912845650483 13391315930860369268475725)
  ·
    refine ⟨5021743474072638475678397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13391315930860369268475725 5021743474072638475678397)
    ·
      refine ⟨1883153802777239428379399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5021743474072638475678397 1883153802777239428379399)
      ·
        refine ⟨2824730704165859142569099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1883153802777239428379399 2824730704165859142569099)
        ·
          refine ⟨4237096056248788713853649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2824730704165859142569099 4237096056248788713853649)
          ·
            refine ⟨3177822042186591535390237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4237096056248788713853649 3177822042186591535390237)
            ·
              refine ⟨1191683265819971825771339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3177822042186591535390237 1191683265819971825771339)
              ·
                refine ⟨1787524898729957738657009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1191683265819971825771339 1787524898729957738657009)
                ·
                  refine ⟨1340643674047468303992757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1787524898729957738657009 1340643674047468303992757)
                  ·
                    refine ⟨125685344441950153499321, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1340643674047468303992757 125685344441950153499321)
                    ·
                      rfl

theorem cell22_367157_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 2, 3, 1, 2, 5].length) (baseStart_367157 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367157 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367157 prefixEnd_367157 := by exact prefixLift 367157
  have htrace : WordTrace (prefixWord ++ tailWord_367157) baseStart_367157 baseEnd_367157 := by
    simpa [prefixWord, tailWord_367157, baseEnd_367157] using wordTrace_append hprefix tailTrace_367157
  have hstable : (prefixWord ++ tailWord_367157).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367157).length < 2 ^ (prefixWord ++ tailWord_367157).sum := by decide
  have hdescent : baseEnd_367157 < baseStart_367157 := by decide
  rcases family_descends (prefixWord ++ tailWord_367157) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367204 : List Nat := [2, 3, 1, 1, 2, 2, 1, 6, 4]
def baseStart_367204 : Nat := 118140960795 + 367204 * 2 ^ 59
def prefixEnd_367204 : Nat := 4983230072969 + 3 ^ 40 * 367204 * 2
def baseEnd_367204 : Nat := 41900477834152565858059

theorem tailTrace_367204 : CollatzResearch.WordTrace tailWord_367204 prefixEnd_367204 41900477834152565858059 := by
  unfold tailWord_367204
  simp only [CollatzResearch.WordTrace]
  refine ⟨6696515080845048147718333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8928686774460064196957777 6696515080845048147718333)
  ·
    refine ⟨2511193155316893055394375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6696515080845048147718333 2511193155316893055394375)
    ·
      refine ⟨3766789732975339583091563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2511193155316893055394375 3766789732975339583091563)
      ·
        refine ⟨5650184599463009374637345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3766789732975339583091563 5650184599463009374637345)
        ·
          refine ⟨4237638449597257030978009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5650184599463009374637345 4237638449597257030978009)
          ·
            refine ⟨3178228837197942773233507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4237638449597257030978009 3178228837197942773233507)
            ·
              refine ⟨4767343255796914159850261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3178228837197942773233507 4767343255796914159850261)
              ·
                refine ⟨223469215115480351242981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4767343255796914159850261 223469215115480351242981)
                ·
                  refine ⟨41900477834152565858059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223469215115480351242981 41900477834152565858059)
                  ·
                    rfl

theorem cell22_367204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 2, 1, 6, 4].length) (baseStart_367204 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367204 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367204 prefixEnd_367204 := by exact prefixLift 367204
  have htrace : WordTrace (prefixWord ++ tailWord_367204) baseStart_367204 baseEnd_367204 := by
    simpa [prefixWord, tailWord_367204, baseEnd_367204] using wordTrace_append hprefix tailTrace_367204
  have hstable : (prefixWord ++ tailWord_367204).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367204).length < 2 ^ (prefixWord ++ tailWord_367204).sum := by decide
  have hdescent : baseEnd_367204 < baseStart_367204 := by decide
  rcases family_descends (prefixWord ++ tailWord_367204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367232 : List Nat := [2, 1, 1, 2, 1, 6, 1, 8]
def baseStart_367232 : Nat := 118140960795 + 367232 * 2 ^ 59
def prefixEnd_367232 : Nat := 4983230072969 + 3 ^ 40 * 367232 * 2
def baseEnd_367232 : Nat := 13967890941630550874899

theorem tailTrace_367232 : CollatzResearch.WordTrace tailWord_367232 prefixEnd_367232 13967890941630550874899 := by
  unfold tailWord_367232
  simp only [CollatzResearch.WordTrace]
  refine ⟨6697025702794328538727975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8929367603725771384970633 6697025702794328538727975)
  ·
    refine ⟨10045538554191492808091963, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6697025702794328538727975 10045538554191492808091963)
    ·
      refine ⟨15068307831287239212137945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10045538554191492808091963 15068307831287239212137945)
      ·
        refine ⟨11301230873465429409103459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15068307831287239212137945 11301230873465429409103459)
        ·
          refine ⟨16951846310198144113655189, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11301230873465429409103459 16951846310198144113655189)
          ·
            refine ⟨794617795790538005327587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16951846310198144113655189 794617795790538005327587)
            ·
              refine ⟨1191926693685807007991381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794617795790538005327587 1191926693685807007991381)
              ·
                refine ⟨13967890941630550874899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1191926693685807007991381 13967890941630550874899)
                ·
                  rfl

theorem cell22_367232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 6, 1, 8].length) (baseStart_367232 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367232 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367232 prefixEnd_367232 := by exact prefixLift 367232
  have htrace : WordTrace (prefixWord ++ tailWord_367232) baseStart_367232 baseEnd_367232 := by
    simpa [prefixWord, tailWord_367232, baseEnd_367232] using wordTrace_append hprefix tailTrace_367232
  have hstable : (prefixWord ++ tailWord_367232).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367232).length < 2 ^ (prefixWord ++ tailWord_367232).sum := by decide
  have hdescent : baseEnd_367232 < baseStart_367232 := by decide
  rcases family_descends (prefixWord ++ tailWord_367232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367341 : List Nat := [1, 5, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_367341 : Nat := 118140960795 + 367341 * 2 ^ 59
def prefixEnd_367341 : Nat := 4983230072969 + 3 ^ 40 * 367341 * 2
def baseEnd_367341 : Nat := 125748331402235006898757

theorem tailTrace_367341 : CollatzResearch.WordTrace tailWord_367341 prefixEnd_367341 125748331402235006898757 := by
  unfold tailWord_367341
  simp only [CollatzResearch.WordTrace]
  refine ⟨13398026962193768693173877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8932017974795845795449251 13398026962193768693173877)
  ·
    refine ⟨1256065027705665814985051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 13398026962193768693173877 1256065027705665814985051)
    ·
      refine ⟨1884097541558498722477577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1256065027705665814985051 1884097541558498722477577)
      ·
        refine ⟨1413073156168874041858183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1884097541558498722477577 1413073156168874041858183)
        ·
          refine ⟨2119609734253311062787275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1413073156168874041858183 2119609734253311062787275)
          ·
            refine ⟨3179414601379966594180913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2119609734253311062787275 3179414601379966594180913)
            ·
              refine ⟨2384560951034974945635685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3179414601379966594180913 2384560951034974945635685)
              ·
                refine ⟨447105178319057802306691, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2384560951034974945635685 447105178319057802306691)
                ·
                  refine ⟨670657767478586703460037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447105178319057802306691 670657767478586703460037)
                  ·
                    refine ⟨125748331402235006898757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670657767478586703460037 125748331402235006898757)
                    ·
                      rfl

theorem cell22_367341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_367341 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367341 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367341 prefixEnd_367341 := by exact prefixLift 367341
  have htrace : WordTrace (prefixWord ++ tailWord_367341) baseStart_367341 baseEnd_367341 := by
    simpa [prefixWord, tailWord_367341, baseEnd_367341] using wordTrace_append hprefix tailTrace_367341
  have hstable : (prefixWord ++ tailWord_367341).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367341).length < 2 ^ (prefixWord ++ tailWord_367341).sum := by decide
  have hdescent : baseEnd_367341 < baseStart_367341 := by decide
  rcases family_descends (prefixWord ++ tailWord_367341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367349 : List Nat := [1, 3, 6, 1, 1, 1, 2, 3, 1, 3]
def baseStart_367349 : Nat := 118140960795 + 367349 * 2 ^ 59
def prefixEnd_367349 : Nat := 4983230072969 + 3 ^ 40 * 367349 * 2
def baseEnd_367349 : Nat := 125751069965725652698733

theorem tailTrace_367349 : CollatzResearch.WordTrace tailWord_367349 prefixEnd_367349 125751069965725652698733 := by
  unfold tailWord_367349
  simp only [CollatzResearch.WordTrace]
  refine ⟨13398318746164786059465101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8932212497443190706310067 13398318746164786059465101)
  ·
    refine ⟨5024369529811794772299413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13398318746164786059465101 5024369529811794772299413)
    ·
      refine ⟨235517321709927879951535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 5024369529811794772299413 235517321709927879951535)
      ·
        refine ⟨353275982564891819927303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235517321709927879951535 353275982564891819927303)
        ·
          refine ⟨529913973847337729890955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353275982564891819927303 529913973847337729890955)
          ·
            refine ⟨794870960771006594836433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 529913973847337729890955 794870960771006594836433)
            ·
              refine ⟨596153220578254946127325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 794870960771006594836433 596153220578254946127325)
              ·
                refine ⟨223557457716845604797747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 596153220578254946127325 223557457716845604797747)
                ·
                  refine ⟨335336186575268407196621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 223557457716845604797747 335336186575268407196621)
                  ·
                    refine ⟨125751069965725652698733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335336186575268407196621 125751069965725652698733)
                    ·
                      rfl

theorem cell22_367349_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 2, 3, 1, 3].length) (baseStart_367349 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367349 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367349 prefixEnd_367349 := by exact prefixLift 367349
  have htrace : WordTrace (prefixWord ++ tailWord_367349) baseStart_367349 baseEnd_367349 := by
    simpa [prefixWord, tailWord_367349, baseEnd_367349] using wordTrace_append hprefix tailTrace_367349
  have hstable : (prefixWord ++ tailWord_367349).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367349).length < 2 ^ (prefixWord ++ tailWord_367349).sum := by decide
  have hdescent : baseEnd_367349 < baseStart_367349 := by decide
  rcases family_descends (prefixWord ++ tailWord_367349) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367354 : List Nat := [3, 1, 1, 1, 1, 3, 4, 2, 1, 5]
def baseStart_367354 : Nat := 118140960795 + 367354 * 2 ^ 59
def prefixEnd_367354 : Nat := 4983230072969 + 3 ^ 40 * 367354 * 2
def baseEnd_367354 : Nat := 125752781567907306323717

theorem tailTrace_367354 : CollatzResearch.WordTrace tailWord_367354 prefixEnd_367354 125752781567907306323717 := by
  unfold tailWord_367354
  simp only [CollatzResearch.WordTrace]
  refine ⟨3349625277786667978349279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8932334074097781275598077 3349625277786667978349279)
  ·
    refine ⟨5024437916680001967523919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3349625277786667978349279 5024437916680001967523919)
    ·
      refine ⟨7536656875020002951285879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5024437916680001967523919 7536656875020002951285879)
      ·
        refine ⟨11304985312530004426928819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7536656875020002951285879 11304985312530004426928819)
        ·
          refine ⟨16957477968795006640393229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11304985312530004426928819 16957477968795006640393229)
          ·
            refine ⟨6359054238298127490147461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16957477968795006640393229 6359054238298127490147461)
            ·
              refine ⟨1192322669680898904402649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6359054238298127490147461 1192322669680898904402649)
              ·
                refine ⟨894242002260674178301987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1192322669680898904402649 894242002260674178301987)
                ·
                  refine ⟨1341363003391011267452981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 894242002260674178301987 1341363003391011267452981)
                  ·
                    refine ⟨125752781567907306323717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1341363003391011267452981 125752781567907306323717)
                    ·
                      rfl

theorem cell22_367354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 3, 4, 2, 1, 5].length) (baseStart_367354 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367354 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367354 prefixEnd_367354 := by exact prefixLift 367354
  have htrace : WordTrace (prefixWord ++ tailWord_367354) baseStart_367354 baseEnd_367354 := by
    simpa [prefixWord, tailWord_367354, baseEnd_367354] using wordTrace_append hprefix tailTrace_367354
  have hstable : (prefixWord ++ tailWord_367354).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367354).length < 2 ^ (prefixWord ++ tailWord_367354).sum := by decide
  have hdescent : baseEnd_367354 < baseStart_367354 := by decide
  rcases family_descends (prefixWord ++ tailWord_367354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367356 : List Nat := [2, 2, 2, 1, 3, 2, 1, 5, 4]
def baseStart_367356 : Nat := 118140960795 + 367356 * 2 ^ 59
def prefixEnd_367356 : Nat := 4983230072969 + 3 ^ 40 * 367356 * 2
def baseEnd_367356 : Nat := 41917822069593322591237

theorem tailTrace_367356 : CollatzResearch.WordTrace tailWord_367356 prefixEnd_367356 41917822069593322591237 := by
  unfold tailWord_367356
  simp only [CollatzResearch.WordTrace]
  refine ⟨6699287028569713127484961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8932382704759617503313281 6699287028569713127484961)
  ·
    refine ⟨5024465271427284845613721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6699287028569713127484961 5024465271427284845613721)
    ·
      refine ⟨3768348953570463634210291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5024465271427284845613721 3768348953570463634210291)
      ·
        refine ⟨5652523430355695451315437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3768348953570463634210291 5652523430355695451315437)
        ·
          refine ⟨2119696286383385794243289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5652523430355695451315437 2119696286383385794243289)
          ·
            refine ⟨1589772214787539345682467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2119696286383385794243289 1589772214787539345682467)
            ·
              refine ⟨2384658322181309018523701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1589772214787539345682467 2384658322181309018523701)
              ·
                refine ⟨223561717704497720486597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2384658322181309018523701 223561717704497720486597)
                ·
                  refine ⟨41917822069593322591237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 223561717704497720486597 41917822069593322591237)
                  ·
                    rfl

theorem cell22_367356_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 1, 5, 4].length) (baseStart_367356 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367356 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367356 prefixEnd_367356 := by exact prefixLift 367356
  have htrace : WordTrace (prefixWord ++ tailWord_367356) baseStart_367356 baseEnd_367356 := by
    simpa [prefixWord, tailWord_367356, baseEnd_367356] using wordTrace_append hprefix tailTrace_367356
  have hstable : (prefixWord ++ tailWord_367356).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367356).length < 2 ^ (prefixWord ++ tailWord_367356).sum := by decide
  have hdescent : baseEnd_367356 < baseStart_367356 := by decide
  rcases family_descends (prefixWord ++ tailWord_367356) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367358 : List Nat := [4, 2, 2, 1, 2, 2, 1, 3, 1, 4]
def baseStart_367358 : Nat := 118140960795 + 367358 * 2 ^ 59
def prefixEnd_367358 : Nat := 4983230072969 + 3 ^ 40 * 367358 * 2
def baseEnd_367358 : Nat := 125754150849652629223705

theorem tailTrace_367358 : CollatzResearch.WordTrace tailWord_367358 prefixEnd_367358 125754150849652629223705 := by
  unfold tailWord_367358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1674830875391522574567841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8932431335421453731028485 1674830875391522574567841)
  ·
    refine ⟨1256123156543641930925881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1674830875391522574567841 1256123156543641930925881)
    ·
      refine ⟨942092367407731448194411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1256123156543641930925881 942092367407731448194411)
      ·
        refine ⟨1413138551111597172291617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942092367407731448194411 1413138551111597172291617)
        ·
          refine ⟨1059853913333697879218713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1413138551111597172291617 1059853913333697879218713)
          ·
            refine ⟨794890435000273409414035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1059853913333697879218713 794890435000273409414035)
            ·
              refine ⟨1192335652500410114121053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 794890435000273409414035 1192335652500410114121053)
              ·
                refine ⟨447125869687653792795395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1192335652500410114121053 447125869687653792795395)
                ·
                  refine ⟨670688804531480689193093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447125869687653792795395 670688804531480689193093)
                  ·
                    refine ⟨125754150849652629223705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670688804531480689193093 125754150849652629223705)
                    ·
                      rfl

theorem cell22_367358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 2, 1, 3, 1, 4].length) (baseStart_367358 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367358 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367358 prefixEnd_367358 := by exact prefixLift 367358
  have htrace : WordTrace (prefixWord ++ tailWord_367358) baseStart_367358 baseEnd_367358 := by
    simpa [prefixWord, tailWord_367358, baseEnd_367358] using wordTrace_append hprefix tailTrace_367358
  have hstable : (prefixWord ++ tailWord_367358).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367358).length < 2 ^ (prefixWord ++ tailWord_367358).sum := by decide
  have hdescent : baseEnd_367358 < baseStart_367358 := by decide
  rcases family_descends (prefixWord ++ tailWord_367358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367369 : List Nat := [1, 2, 1, 1, 3, 2, 2, 4, 2, 4]
def baseStart_367369 : Nat := 118140960795 + 367369 * 2 ^ 59
def prefixEnd_367369 : Nat := 4983230072969 + 3 ^ 40 * 367369 * 2
def baseEnd_367369 : Nat := 125757916374452267198671

theorem tailTrace_367369 : CollatzResearch.WordTrace tailWord_367369 prefixEnd_367369 125757916374452267198671 := by
  unfold tailWord_367369
  simp only [CollatzResearch.WordTrace]
  refine ⟨13399048206092329475193161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8932698804061552983462107 13399048206092329475193161)
  ·
    refine ⟨10049286154569247106394871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13399048206092329475193161 10049286154569247106394871)
    ·
      refine ⟨15073929231853870659592307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10049286154569247106394871 15073929231853870659592307)
      ·
        refine ⟨22610893847780805989388461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15073929231853870659592307 22610893847780805989388461)
        ·
          refine ⟨8479085192917802246020673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22610893847780805989388461 8479085192917802246020673)
          ·
            refine ⟨6359313894688351684515505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8479085192917802246020673 6359313894688351684515505)
            ·
              refine ⟨4769485421016263763386629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6359313894688351684515505 4769485421016263763386629)
              ·
                refine ⟨894278516440549455634993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4769485421016263763386629 894278516440549455634993)
                ·
                  refine ⟨670708887330412091726245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 894278516440549455634993 670708887330412091726245)
                  ·
                    refine ⟨125757916374452267198671, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670708887330412091726245 125757916374452267198671)
                    ·
                      rfl

theorem cell22_367369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 2, 2, 4, 2, 4].length) (baseStart_367369 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367369 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367369 prefixEnd_367369 := by exact prefixLift 367369
  have htrace : WordTrace (prefixWord ++ tailWord_367369) baseStart_367369 baseEnd_367369 := by
    simpa [prefixWord, tailWord_367369, baseEnd_367369] using wordTrace_append hprefix tailTrace_367369
  have hstable : (prefixWord ++ tailWord_367369).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367369).length < 2 ^ (prefixWord ++ tailWord_367369).sum := by decide
  have hdescent : baseEnd_367369 < baseStart_367369 := by decide
  rcases family_descends (prefixWord ++ tailWord_367369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367433 : List Nat := [1, 2, 1, 1, 2, 7, 1, 1, 3, 3]
def baseStart_367433 : Nat := 118140960795 + 367433 * 2 ^ 59
def prefixEnd_367433 : Nat := 4983230072969 + 3 ^ 40 * 367433 * 2
def baseEnd_367433 : Nat := 125779824882377433598475

theorem tailTrace_367433 : CollatzResearch.WordTrace tailWord_367433 prefixEnd_367433 125779824882377433598475 := by
  unfold tailWord_367433
  simp only [CollatzResearch.WordTrace]
  refine ⟨13401382477860468405522953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8934254985240312270348635 13401382477860468405522953)
  ·
    refine ⟨10051036858395351304142215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13401382477860468405522953 10051036858395351304142215)
    ·
      refine ⟨15076555287593026956213323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10051036858395351304142215 15076555287593026956213323)
      ·
        refine ⟨22614832931389540434319985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15076555287593026956213323 22614832931389540434319985)
        ·
          refine ⟨16961124698542155325739989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22614832931389540434319985 16961124698542155325739989)
          ·
            refine ⟨397526360122081765447031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 16961124698542155325739989 397526360122081765447031)
            ·
              refine ⟨596289540183122648170547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 397526360122081765447031 596289540183122648170547)
              ·
                refine ⟨894434310274683972255821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 596289540183122648170547 894434310274683972255821)
                ·
                  refine ⟨335412866353006489595933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 894434310274683972255821 335412866353006489595933)
                  ·
                    refine ⟨125779824882377433598475, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 335412866353006489595933 125779824882377433598475)
                    ·
                      rfl

theorem cell22_367433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 7, 1, 1, 3, 3].length) (baseStart_367433 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367433 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367433 prefixEnd_367433 := by exact prefixLift 367433
  have htrace : WordTrace (prefixWord ++ tailWord_367433) baseStart_367433 baseEnd_367433 := by
    simpa [prefixWord, tailWord_367433, baseEnd_367433] using wordTrace_append hprefix tailTrace_367433
  have hstable : (prefixWord ++ tailWord_367433).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367433).length < 2 ^ (prefixWord ++ tailWord_367433).sum := by decide
  have hdescent : baseEnd_367433 < baseStart_367433 := by decide
  rcases family_descends (prefixWord ++ tailWord_367433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367527 : List Nat := [1, 1, 6, 1, 3, 2, 2, 1, 1, 4]
def baseStart_367527 : Nat := 118140960795 + 367527 * 2 ^ 59
def prefixEnd_367527 : Nat := 4983230072969 + 3 ^ 40 * 367527 * 2
def baseEnd_367527 : Nat := 125812003003392521748187

theorem tailTrace_367527 : CollatzResearch.WordTrace tailWord_367527 prefixEnd_367527 125812003003392521748187 := by
  unfold tailWord_367527
  simp only [CollatzResearch.WordTrace]
  refine ⟨13404810939519922459444835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8936540626346614972963223 13404810939519922459444835)
  ·
    refine ⟨20107216409279883689167253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13404810939519922459444835 20107216409279883689167253)
    ·
      refine ⟨942525769184994547929715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 20107216409279883689167253 942525769184994547929715)
      ·
        refine ⟨1413788653777491821894573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 942525769184994547929715 1413788653777491821894573)
        ·
          refine ⟨530170745166559433210465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1413788653777491821894573 530170745166559433210465)
          ·
            refine ⟨397628058874919574907849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 530170745166559433210465 397628058874919574907849)
            ·
              refine ⟨298221044156189681180887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397628058874919574907849 298221044156189681180887)
              ·
                refine ⟨447331566234284521771331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 298221044156189681180887 447331566234284521771331)
                ·
                  refine ⟨670997349351426782656997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 447331566234284521771331 670997349351426782656997)
                  ·
                    refine ⟨125812003003392521748187, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 670997349351426782656997 125812003003392521748187)
                    ·
                      rfl

theorem cell22_367527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 3, 2, 2, 1, 1, 4].length) (baseStart_367527 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367527 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367527 prefixEnd_367527 := by exact prefixLift 367527
  have htrace : WordTrace (prefixWord ++ tailWord_367527) baseStart_367527 baseEnd_367527 := by
    simpa [prefixWord, tailWord_367527, baseEnd_367527] using wordTrace_append hprefix tailTrace_367527
  have hstable : (prefixWord ++ tailWord_367527).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367527).length < 2 ^ (prefixWord ++ tailWord_367527).sum := by decide
  have hdescent : baseEnd_367527 < baseStart_367527 := by decide
  rcases family_descends (prefixWord ++ tailWord_367527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367570 : List Nat := [3, 2, 2, 3, 1, 3, 2, 6]
def baseStart_367570 : Nat := 118140960795 + 367570 * 2 ^ 59
def prefixEnd_367570 : Nat := 4983230072969 + 3 ^ 40 * 367570 * 2
def baseEnd_367570 : Nat := 13980746975794971435895

theorem tailTrace_367570 : CollatzResearch.WordTrace tailWord_367570 prefixEnd_367570 13980746975794971435895 := by
  unfold tailWord_367570
  simp only [CollatzResearch.WordTrace]
  refine ⟨3351594819591035200815041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8937586185576093868840109 3351594819591035200815041)
  ·
    refine ⟨2513696114693276400611281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3351594819591035200815041 2513696114693276400611281)
    ·
      refine ⟨1885272086019957300458461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2513696114693276400611281 1885272086019957300458461)
      ·
        refine ⟨706977032257483987671923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1885272086019957300458461 706977032257483987671923)
        ·
          refine ⟨1060465548386225981507885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 706977032257483987671923 1060465548386225981507885)
          ·
            refine ⟨397674580644834743065457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1060465548386225981507885 397674580644834743065457)
            ·
              refine ⟨298255935483626057299093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 397674580644834743065457 298255935483626057299093)
              ·
                refine ⟨13980746975794971435895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 298255935483626057299093 13980746975794971435895)
                ·
                  rfl

theorem cell22_367570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 3, 2, 6].length) (baseStart_367570 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367570 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367570 prefixEnd_367570 := by exact prefixLift 367570
  have htrace : WordTrace (prefixWord ++ tailWord_367570) baseStart_367570 baseEnd_367570 := by
    simpa [prefixWord, tailWord_367570, baseEnd_367570] using wordTrace_append hprefix tailTrace_367570
  have hstable : (prefixWord ++ tailWord_367570).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367570).length < 2 ^ (prefixWord ++ tailWord_367570).sum := by decide
  have hdescent : baseEnd_367570 < baseStart_367570 := by decide
  rcases family_descends (prefixWord ++ tailWord_367570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367604 : List Nat := [2, 6, 2, 1, 1, 1, 2, 7]
def baseStart_367604 : Nat := 118140960795 + 367604 * 2 ^ 59
def prefixEnd_367604 : Nat := 4983230072969 + 3 ^ 40 * 367604 * 2
def baseEnd_367604 : Nat := 13982040186332220841439

theorem tailTrace_367604 : CollatzResearch.WordTrace tailWord_367604 prefixEnd_367604 13982040186332220841439 := by
  unfold tailWord_367604
  simp only [CollatzResearch.WordTrace]
  refine ⟨6703809680120482304998933, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8938412906827309739998577 6703809680120482304998933)
  ·
    refine ⟨314241078755647608046825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6703809680120482304998933 314241078755647608046825)
    ·
      refine ⟨235680809066735706035119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 314241078755647608046825 235680809066735706035119)
      ·
        refine ⟨353521213600103559052679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 235680809066735706035119 353521213600103559052679)
        ·
          refine ⟨530281820400155338579019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 353521213600103559052679 530281820400155338579019)
          ·
            refine ⟨795422730600233007868529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 530281820400155338579019 795422730600233007868529)
            ·
              refine ⟨596567047950174755901397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 795422730600233007868529 596567047950174755901397)
              ·
                refine ⟨13982040186332220841439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 596567047950174755901397 13982040186332220841439)
                ·
                  rfl

theorem cell22_367604_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 2, 7].length) (baseStart_367604 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367604 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367604 prefixEnd_367604 := by exact prefixLift 367604
  have htrace : WordTrace (prefixWord ++ tailWord_367604) baseStart_367604 baseEnd_367604 := by
    simpa [prefixWord, tailWord_367604, baseEnd_367604] using wordTrace_append hprefix tailTrace_367604
  have hstable : (prefixWord ++ tailWord_367604).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367604).length < 2 ^ (prefixWord ++ tailWord_367604).sum := by decide
  have hdescent : baseEnd_367604 < baseStart_367604 := by decide
  rcases family_descends (prefixWord ++ tailWord_367604) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367611 : List Nat := [1, 1, 1, 1, 1, 3, 3, 4, 3, 4]
def baseStart_367611 : Nat := 118140960795 + 367611 * 2 ^ 59
def prefixEnd_367611 : Nat := 4983230072969 + 3 ^ 40 * 367611 * 2
def baseEnd_367611 : Nat := 125840757920044302647929

theorem tailTrace_367611 : CollatzResearch.WordTrace tailWord_367611 prefixEnd_367611 125840757920044302647929 := by
  unfold tailWord_367611
  simp only [CollatzResearch.WordTrace]
  refine ⟨13407874671215604805502687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8938583114143736537001791 13407874671215604805502687)
  ·
    refine ⟨20111812006823407208254031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13407874671215604805502687 20111812006823407208254031)
    ·
      refine ⟨30167718010235110812381047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20111812006823407208254031 30167718010235110812381047)
      ·
        refine ⟨45251577015352666218571571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30167718010235110812381047 45251577015352666218571571)
        ·
          refine ⟨67877365523028999327857357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45251577015352666218571571 67877365523028999327857357)
          ·
            refine ⟨25454012071135874747946509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67877365523028999327857357 25454012071135874747946509)
            ·
              refine ⟨9545254526675953030479941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25454012071135874747946509 9545254526675953030479941)
              ·
                refine ⟨1789735223751741193214989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 9545254526675953030479941 1789735223751741193214989)
                ·
                  refine ⟨671150708906902947455621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1789735223751741193214989 671150708906902947455621)
                  ·
                    refine ⟨125840757920044302647929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 671150708906902947455621 125840757920044302647929)
                    ·
                      rfl

theorem cell22_367611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 3, 4, 3, 4].length) (baseStart_367611 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367611 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367611 prefixEnd_367611 := by exact prefixLift 367611
  have htrace : WordTrace (prefixWord ++ tailWord_367611) baseStart_367611 baseEnd_367611 := by
    simpa [prefixWord, tailWord_367611, baseEnd_367611] using wordTrace_append hprefix tailTrace_367611
  have hstable : (prefixWord ++ tailWord_367611).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367611).length < 2 ^ (prefixWord ++ tailWord_367611).sum := by decide
  have hdescent : baseEnd_367611 < baseStart_367611 := by decide
  rcases family_descends (prefixWord ++ tailWord_367611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_367628 : List Nat := [2, 2, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_367628 : Nat := 118140960795 + 367628 * 2 ^ 59
def prefixEnd_367628 : Nat := 4983230072969 + 3 ^ 40 * 367628 * 2
def baseEnd_367628 : Nat := 125846577367461924972877

theorem tailTrace_367628 : CollatzResearch.WordTrace tailWord_367628 prefixEnd_367628 125846577367461924972877 := by
  unfold tailWord_367628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6704247356077008354435769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8938996474769344472581025 6704247356077008354435769)
  ·
    refine ⟨5028185517057756265826827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6704247356077008354435769 5028185517057756265826827)
    ·
      refine ⟨7542278275586634398740241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5028185517057756265826827 7542278275586634398740241)
      ·
        refine ⟨5656708706689975799055181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7542278275586634398740241 5656708706689975799055181)
        ·
          refine ⟨2121265765008740924645693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5656708706689975799055181 2121265765008740924645693)
          ·
            refine ⟨795474661878277846742135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2121265765008740924645693 795474661878277846742135)
            ·
              refine ⟨1193211992817416770113203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 795474661878277846742135 1193211992817416770113203)
              ·
                refine ⟨1789817989226125155169805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1193211992817416770113203 1789817989226125155169805)
                ·
                  refine ⟨671181745959796933188677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1789817989226125155169805 671181745959796933188677)
                  ·
                    refine ⟨125846577367461924972877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 671181745959796933188677 125846577367461924972877)
                    ·
                      rfl

theorem cell22_367628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_367628 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_367628 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_367628 prefixEnd_367628 := by exact prefixLift 367628
  have htrace : WordTrace (prefixWord ++ tailWord_367628) baseStart_367628 baseEnd_367628 := by
    simpa [prefixWord, tailWord_367628, baseEnd_367628] using wordTrace_append hprefix tailTrace_367628
  have hstable : (prefixWord ++ tailWord_367628).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_367628).length < 2 ^ (prefixWord ++ tailWord_367628).sum := by decide
  have hdescent : baseEnd_367628 < baseStart_367628 := by decide
  rcases family_descends (prefixWord ++ tailWord_367628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
