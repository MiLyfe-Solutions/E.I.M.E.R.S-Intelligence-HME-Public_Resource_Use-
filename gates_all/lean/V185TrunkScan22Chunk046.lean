import V185TrunkScan22Chunk045

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental

namespace V185TrunkScan22Incremental

def tailWord_412578 : List Nat := [3, 3, 1, 2, 2, 2, 1, 4, 4]
def baseStart_412578 : Nat := 118140960795 + 412578 * 2 ^ 59
def prefixEnd_412578 : Nat := 4983230072969 + 3 ^ 40 * 412578 * 2
def baseEnd_412578 : Nat := 47077960326842671195021

theorem tailTrace_412578 : CollatzResearch.WordTrace tailWord_412578 prefixEnd_412578 47077960326842671195021 := by
  unfold tailWord_412578
  simp only [CollatzResearch.WordTrace]
  refine ⟨3761988974826960889421597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10031970599538562371790925 3761988974826960889421597)
  ·
    refine ⟨1410745865560110333533099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3761988974826960889421597 1410745865560110333533099)
    ·
      refine ⟨2116118798340165500299649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410745865560110333533099 2116118798340165500299649)
      ·
        refine ⟨1587089098755124125224737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2116118798340165500299649 1587089098755124125224737)
        ·
          refine ⟨1190316824066343093918553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1587089098755124125224737 1190316824066343093918553)
          ·
            refine ⟨892737618049757320438915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1190316824066343093918553 892737618049757320438915)
            ·
              refine ⟨1339106427074635980658373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892737618049757320438915 1339106427074635980658373)
              ·
                refine ⟨251082455076494246373445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1339106427074635980658373 251082455076494246373445)
                ·
                  refine ⟨47077960326842671195021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251082455076494246373445 47077960326842671195021)
                  ·
                    rfl

theorem cell22_412578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 2, 1, 4, 4].length) (baseStart_412578 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412578 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412578 prefixEnd_412578 := by exact prefixLift 412578
  have htrace : WordTrace (prefixWord ++ tailWord_412578) baseStart_412578 baseEnd_412578 := by
    simpa [prefixWord, tailWord_412578, baseEnd_412578] using wordTrace_append hprefix tailTrace_412578
  have hstable : (prefixWord ++ tailWord_412578).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412578).length < 2 ^ (prefixWord ++ tailWord_412578).sum := by decide
  have hdescent : baseEnd_412578 < baseStart_412578 := by decide
  rcases family_descends (prefixWord ++ tailWord_412578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412606 : List Nat := [4, 2, 1, 1, 1, 2, 5, 6]
def baseStart_412606 : Nat := 118140960795 + 412606 * 2 ^ 59
def prefixEnd_412606 : Nat := 4983230072969 + 3 ^ 40 * 412606 * 2
def baseEnd_412606 : Nat := 15693718439193919320553

theorem tailTrace_412606 : CollatzResearch.WordTrace tailWord_412606 prefixEnd_412606 15693718439193919320553 := by
  unfold tailWord_412606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1881122142900800542463209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10032651428804269559803781 1881122142900800542463209)
  ·
    refine ⟨1410841607175600406847407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1881122142900800542463209 1410841607175600406847407)
    ·
      refine ⟨2116262410763400610271111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1410841607175600406847407 2116262410763400610271111)
      ·
        refine ⟨3174393616145100915406667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2116262410763400610271111 3174393616145100915406667)
        ·
          refine ⟨4761590424217651373110001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3174393616145100915406667 4761590424217651373110001)
          ·
            refine ⟨3571192818163238529832501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4761590424217651373110001 3571192818163238529832501)
            ·
              refine ⟨334799326702803612171797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3571192818163238529832501 334799326702803612171797)
              ·
                refine ⟨15693718439193919320553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 334799326702803612171797 15693718439193919320553)
                ·
                  rfl

theorem cell22_412606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 5, 6].length) (baseStart_412606 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412606 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412606 prefixEnd_412606 := by exact prefixLift 412606
  have htrace : WordTrace (prefixWord ++ tailWord_412606) baseStart_412606 baseEnd_412606 := by
    simpa [prefixWord, tailWord_412606, baseEnd_412606] using wordTrace_append hprefix tailTrace_412606
  have hstable : (prefixWord ++ tailWord_412606).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412606).length < 2 ^ (prefixWord ++ tailWord_412606).sum := by decide
  have hdescent : baseEnd_412606 < baseStart_412606 := by decide
  rcases family_descends (prefixWord ++ tailWord_412606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412614 : List Nat := [6, 1, 3, 1, 1, 1, 1, 3, 1, 4]
def baseStart_412614 : Nat := 118140960795 + 412614 * 2 ^ 59
def prefixEnd_412614 : Nat := 4983230072969 + 3 ^ 40 * 412614 * 2
def baseEnd_412614 : Nat := 141246204516235919684953

theorem tailTrace_412614 : CollatzResearch.WordTrace tailWord_412614 prefixEnd_412614 141246204516235919684953 := by
  unfold tailWord_412614
  simp only [CollatzResearch.WordTrace]
  refine ⟨470289653974294428312403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 10032845951451614470664597 470289653974294428312403)
  ·
    refine ⟨705434480961441642468605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 470289653974294428312403 705434480961441642468605)
    ·
      refine ⟨264537930360540615925727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 705434480961441642468605 264537930360540615925727)
      ·
        refine ⟨396806895540810923888591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 264537930360540615925727 396806895540810923888591)
        ·
          refine ⟨595210343311216385832887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 396806895540810923888591 595210343311216385832887)
          ·
            refine ⟨892815514966824578749331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595210343311216385832887 892815514966824578749331)
            ·
              refine ⟨1339223272450236868123997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 892815514966824578749331 1339223272450236868123997)
              ·
                refine ⟨502208727168838825546499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1339223272450236868123997 502208727168838825546499)
                ·
                  refine ⟨753313090753258238319749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502208727168838825546499 753313090753258238319749)
                  ·
                    refine ⟨141246204516235919684953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753313090753258238319749 141246204516235919684953)
                    ·
                      rfl

theorem cell22_412614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 1, 1, 1, 3, 1, 4].length) (baseStart_412614 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412614 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412614 prefixEnd_412614 := by exact prefixLift 412614
  have htrace : WordTrace (prefixWord ++ tailWord_412614) baseStart_412614 baseEnd_412614 := by
    simpa [prefixWord, tailWord_412614, baseEnd_412614] using wordTrace_append hprefix tailTrace_412614
  have hstable : (prefixWord ++ tailWord_412614).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412614).length < 2 ^ (prefixWord ++ tailWord_412614).sum := by decide
  have hdescent : baseEnd_412614 < baseStart_412614 := by decide
  rcases family_descends (prefixWord ++ tailWord_412614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412696 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 6]
def baseStart_412696 : Nat := 118140960795 + 412696 * 2 ^ 59
def prefixEnd_412696 : Nat := 4983230072969 + 3 ^ 40 * 412696 * 2
def baseEnd_412696 : Nat := 47091424930671679711567

theorem tailTrace_412696 : CollatzResearch.WordTrace tailWord_412696 prefixEnd_412696 47091424930671679711567 := by
  unfold tailWord_412696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7526129856440174855240971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10034839808586899806987961 7526129856440174855240971)
  ·
    refine ⟨11289194784660262282861457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7526129856440174855240971 11289194784660262282861457)
    ·
      refine ⟨8466896088495196712146093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11289194784660262282861457 8466896088495196712146093)
      ·
        refine ⟨3175086033185698767054785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8466896088495196712146093 3175086033185698767054785)
        ·
          refine ⟨2381314524889274075291089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175086033185698767054785 2381314524889274075291089)
          ·
            refine ⟨1785985893666955556468317, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2381314524889274075291089 1785985893666955556468317)
            ·
              refine ⟨669744710125108333675619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1785985893666955556468317 669744710125108333675619)
              ·
                refine ⟨1004617065187662500513429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 669744710125108333675619 1004617065187662500513429)
                ·
                  refine ⟨47091424930671679711567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1004617065187662500513429 47091424930671679711567)
                  ·
                    rfl

theorem cell22_412696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 6].length) (baseStart_412696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412696 prefixEnd_412696 := by exact prefixLift 412696
  have htrace : WordTrace (prefixWord ++ tailWord_412696) baseStart_412696 baseEnd_412696 := by
    simpa [prefixWord, tailWord_412696, baseEnd_412696] using wordTrace_append hprefix tailTrace_412696
  have hstable : (prefixWord ++ tailWord_412696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412696).length < 2 ^ (prefixWord ++ tailWord_412696).sum := by decide
  have hdescent : baseEnd_412696 < baseStart_412696 := by decide
  rcases family_descends (prefixWord ++ tailWord_412696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412773 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 3, 3]
def baseStart_412773 : Nat := 118140960795 + 412773 * 2 ^ 59
def prefixEnd_412773 : Nat := 4983230072969 + 3 ^ 40 * 412773 * 2
def baseEnd_412773 : Nat := 141300633465612504959465

theorem tailTrace_412773 : CollatzResearch.WordTrace tailWord_412773 prefixEnd_412773 141300633465612504959465 := by
  unfold tailWord_412773
  simp only [CollatzResearch.WordTrace]
  refine ⟨15055068133601391861034973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10036712089067594574023315 15055068133601391861034973)
  ·
    refine ⟨5645650550100521947888115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15055068133601391861034973 5645650550100521947888115)
    ·
      refine ⟨8468475825150782921832173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5645650550100521947888115 8468475825150782921832173)
      ·
        refine ⟨3175678434431543595687065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8468475825150782921832173 3175678434431543595687065)
        ·
          refine ⟨2381758825823657696765299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175678434431543595687065 2381758825823657696765299)
          ·
            refine ⟨3572638238735486545147949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381758825823657696765299 3572638238735486545147949)
            ·
              refine ⟨1339739339525807454430481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3572638238735486545147949 1339739339525807454430481)
              ·
                refine ⟨1004804504644355590822861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1339739339525807454430481 1004804504644355590822861)
                ·
                  refine ⟨376801689241633346558573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1004804504644355590822861 376801689241633346558573)
                  ·
                    refine ⟨141300633465612504959465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376801689241633346558573 141300633465612504959465)
                    ·
                      rfl

theorem cell22_412773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 3, 3].length) (baseStart_412773 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412773 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412773 prefixEnd_412773 := by exact prefixLift 412773
  have htrace : WordTrace (prefixWord ++ tailWord_412773) baseStart_412773 baseEnd_412773 := by
    simpa [prefixWord, tailWord_412773, baseEnd_412773] using wordTrace_append hprefix tailTrace_412773
  have hstable : (prefixWord ++ tailWord_412773).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412773).length < 2 ^ (prefixWord ++ tailWord_412773).sum := by decide
  have hdescent : baseEnd_412773 < baseStart_412773 := by decide
  rcases family_descends (prefixWord ++ tailWord_412773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412786 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 7]
def baseStart_412786 : Nat := 118140960795 + 412786 * 2 ^ 59
def prefixEnd_412786 : Nat := 4983230072969 + 3 ^ 40 * 412786 * 2
def baseEnd_412786 : Nat := 47101694543761601461475

theorem tailTrace_412786 : CollatzResearch.WordTrace tailWord_412786 prefixEnd_412786 47101694543761601461475 := by
  unfold tailWord_412786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3763885570638573770314553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10037028188369530054172141 3763885570638573770314553)
  ·
    refine ⟨2822914177978930327735915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3763885570638573770314553 2822914177978930327735915)
    ·
      refine ⟨4234371266968395491603873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2822914177978930327735915 4234371266968395491603873)
      ·
        refine ⟨3175778450226296618702905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4234371266968395491603873 3175778450226296618702905)
        ·
          refine ⟨2381833837669722464027179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3175778450226296618702905 2381833837669722464027179)
          ·
            refine ⟨3572750756504583696040769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2381833837669722464027179 3572750756504583696040769)
            ·
              refine ⟨2679563067378437772030577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3572750756504583696040769 2679563067378437772030577)
              ·
                refine ⟨2009672300533828329022933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2679563067378437772030577 2009672300533828329022933)
                ·
                  refine ⟨47101694543761601461475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2009672300533828329022933 47101694543761601461475)
                  ·
                    rfl

theorem cell22_412786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 7].length) (baseStart_412786 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412786 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412786 prefixEnd_412786 := by exact prefixLift 412786
  have htrace : WordTrace (prefixWord ++ tailWord_412786) baseStart_412786 baseEnd_412786 := by
    simpa [prefixWord, tailWord_412786, baseEnd_412786] using wordTrace_append hprefix tailTrace_412786
  have hstable : (prefixWord ++ tailWord_412786).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412786).length < 2 ^ (prefixWord ++ tailWord_412786).sum := by decide
  have hdescent : baseEnd_412786 < baseStart_412786 := by decide
  rcases family_descends (prefixWord ++ tailWord_412786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412816 : List Nat := [2, 1, 1, 1, 1, 1, 4, 4, 3, 4]
def baseStart_412816 : Nat := 118140960795 + 412816 * 2 ^ 59
def prefixEnd_412816 : Nat := 4983230072969 + 3 ^ 40 * 412816 * 2
def baseEnd_412816 : Nat := 141315353244374726134333

theorem tailTrace_412816 : CollatzResearch.WordTrace tailWord_412816 prefixEnd_412816 141315353244374726134333 := by
  unfold tailWord_412816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7528318236222805102425151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10037757648297073469900201 7528318236222805102425151)
  ·
    refine ⟨11292477354334207653637727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7528318236222805102425151 11292477354334207653637727)
    ·
      refine ⟨16938716031501311480456591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11292477354334207653637727 16938716031501311480456591)
      ·
        refine ⟨25408074047251967220684887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16938716031501311480456591 25408074047251967220684887)
        ·
          refine ⟨38112111070877950831027331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25408074047251967220684887 38112111070877950831027331)
          ·
            refine ⟨57168166606316926246540997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38112111070877950831027331 57168166606316926246540997)
            ·
              refine ⟨10719031238684423671226437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57168166606316926246540997 10719031238684423671226437)
              ·
                refine ⟨2009818357253329438354957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10719031238684423671226437 2009818357253329438354957)
                ·
                  refine ⟨753681883969998539383109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2009818357253329438354957 753681883969998539383109)
                  ·
                    refine ⟨141315353244374726134333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753681883969998539383109 141315353244374726134333)
                    ·
                      rfl

theorem cell22_412816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 4, 4, 3, 4].length) (baseStart_412816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412816 prefixEnd_412816 := by exact prefixLift 412816
  have htrace : WordTrace (prefixWord ++ tailWord_412816) baseStart_412816 baseEnd_412816 := by
    simpa [prefixWord, tailWord_412816, baseEnd_412816] using wordTrace_append hprefix tailTrace_412816
  have hstable : (prefixWord ++ tailWord_412816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412816).length < 2 ^ (prefixWord ++ tailWord_412816).sum := by decide
  have hdescent : baseEnd_412816 < baseStart_412816 := by decide
  rcases family_descends (prefixWord ++ tailWord_412816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412818 : List Nat := [3, 2, 3, 1, 1, 2, 2, 1, 2, 5]
def baseStart_412818 : Nat := 118140960795 + 412818 * 2 ^ 59
def prefixEnd_412818 : Nat := 4983230072969 + 3 ^ 40 * 412818 * 2
def baseEnd_412818 : Nat := 141316037885247387584327

theorem tailTrace_412818 : CollatzResearch.WordTrace tailWord_412818 prefixEnd_412818 141316037885247387584327 := by
  unfold tailWord_412818
  simp only [CollatzResearch.WordTrace]
  refine ⟨3764177354609591136605777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10037806278958909697615405 3764177354609591136605777)
  ·
    refine ⟨2823133015957193352454333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3764177354609591136605777 2823133015957193352454333)
    ·
      refine ⟨1058674880983947507170375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2823133015957193352454333 1058674880983947507170375)
      ·
        refine ⟨1588012321475921260755563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1058674880983947507170375 1588012321475921260755563)
        ·
          refine ⟨2382018482213881891133345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1588012321475921260755563 2382018482213881891133345)
          ·
            refine ⟨1786513861660411418350009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2382018482213881891133345 1786513861660411418350009)
            ·
              refine ⟨1339885396245308563762507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1786513861660411418350009 1339885396245308563762507)
              ·
                refine ⟨2009828094367962845643761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1339885396245308563762507 2009828094367962845643761)
                ·
                  refine ⟨1507371070775972134232821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2009828094367962845643761 1507371070775972134232821)
                  ·
                    refine ⟨141316037885247387584327, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1507371070775972134232821 141316037885247387584327)
                    ·
                      rfl

theorem cell22_412818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 2, 1, 2, 5].length) (baseStart_412818 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412818 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412818 prefixEnd_412818 := by exact prefixLift 412818
  have htrace : WordTrace (prefixWord ++ tailWord_412818) baseStart_412818 baseEnd_412818 := by
    simpa [prefixWord, tailWord_412818, baseEnd_412818] using wordTrace_append hprefix tailTrace_412818
  have hstable : (prefixWord ++ tailWord_412818).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412818).length < 2 ^ (prefixWord ++ tailWord_412818).sum := by decide
  have hdescent : baseEnd_412818 < baseStart_412818 := by decide
  rcases family_descends (prefixWord ++ tailWord_412818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412863 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 4, 3]
def baseStart_412863 : Nat := 118140960795 + 412863 * 2 ^ 59
def prefixEnd_412863 : Nat := 4983230072969 + 3 ^ 40 * 412863 * 2
def baseEnd_412863 : Nat := 141331442304882270209189

theorem tailTrace_412863 : CollatzResearch.WordTrace tailWord_412863 prefixEnd_412863 141331442304882270209189 := by
  unfold tailWord_412863
  simp only [CollatzResearch.WordTrace]
  refine ⟨15058350703275337231811243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10038900468850224821207495 15058350703275337231811243)
  ·
    refine ⟨22587526054913005847716865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15058350703275337231811243 22587526054913005847716865)
    ·
      refine ⟨16940644541184754385787649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22587526054913005847716865 16940644541184754385787649)
      ·
        refine ⟨12705483405888565789340737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16940644541184754385787649 12705483405888565789340737)
        ·
          refine ⟨9529112554416424342005553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12705483405888565789340737 9529112554416424342005553)
          ·
            refine ⟨7146834415812318256504165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9529112554416424342005553 7146834415812318256504165)
            ·
              refine ⟨1340031452964809673094531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7146834415812318256504165 1340031452964809673094531)
              ·
                refine ⟨2010047179447214509641797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340031452964809673094531 2010047179447214509641797)
                ·
                  refine ⟨376883846146352720557837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010047179447214509641797 376883846146352720557837)
                  ·
                    refine ⟨141331442304882270209189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376883846146352720557837 141331442304882270209189)
                    ·
                      rfl

theorem cell22_412863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 4, 3].length) (baseStart_412863 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412863 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412863 prefixEnd_412863 := by exact prefixLift 412863
  have htrace : WordTrace (prefixWord ++ tailWord_412863) baseStart_412863 baseEnd_412863 := by
    simpa [prefixWord, tailWord_412863, baseEnd_412863] using wordTrace_append hprefix tailTrace_412863
  have hstable : (prefixWord ++ tailWord_412863).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412863).length < 2 ^ (prefixWord ++ tailWord_412863).sum := by decide
  have hdescent : baseEnd_412863 < baseStart_412863 := by decide
  rcases family_descends (prefixWord ++ tailWord_412863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412865 : List Nat := [1, 2, 6, 1, 1, 1, 3, 1, 6]
def baseStart_412865 : Nat := 118140960795 + 412865 * 2 ^ 59
def prefixEnd_412865 : Nat := 4983230072969 + 3 ^ 40 * 412865 * 2
def baseEnd_412865 : Nat := 47110708981918310553061

theorem tailTrace_412865 : CollatzResearch.WordTrace tailWord_412865 prefixEnd_412865 47110708981918310553061 := by
  unfold tailWord_412865
  simp only [CollatzResearch.WordTrace]
  refine ⟨15058423649268091573384049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10038949099512061048922699 15058423649268091573384049)
  ·
    refine ⟨11293817736951068680038037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15058423649268091573384049 11293817736951068680038037)
    ·
      refine ⟨529397706419581344376783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 11293817736951068680038037 529397706419581344376783)
      ·
        refine ⟨794096559629372016565175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 529397706419581344376783 794096559629372016565175)
        ·
          refine ⟨1191144839444058024847763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794096559629372016565175 1191144839444058024847763)
          ·
            refine ⟨1786717259166087037271645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191144839444058024847763 1786717259166087037271645)
            ·
              refine ⟨670018972187282638976867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1786717259166087037271645 670018972187282638976867)
              ·
                refine ⟨1005028458280923958465301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670018972187282638976867 1005028458280923958465301)
                ·
                  refine ⟨47110708981918310553061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1005028458280923958465301 47110708981918310553061)
                  ·
                    rfl

theorem cell22_412865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 3, 1, 6].length) (baseStart_412865 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412865 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412865 prefixEnd_412865 := by exact prefixLift 412865
  have htrace : WordTrace (prefixWord ++ tailWord_412865) baseStart_412865 baseEnd_412865 := by
    simpa [prefixWord, tailWord_412865, baseEnd_412865] using wordTrace_append hprefix tailTrace_412865
  have hstable : (prefixWord ++ tailWord_412865).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412865).length < 2 ^ (prefixWord ++ tailWord_412865).sum := by decide
  have hdescent : baseEnd_412865 < baseStart_412865 := by decide
  rcases family_descends (prefixWord ++ tailWord_412865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412884 : List Nat := [2, 4, 1, 4, 1, 2, 1, 2, 1, 4]
def baseStart_412884 : Nat := 118140960795 + 412884 * 2 ^ 59
def prefixEnd_412884 : Nat := 4983230072969 + 3 ^ 40 * 412884 * 2
def baseEnd_412884 : Nat := 141338631034045215434125

theorem tailTrace_412884 : CollatzResearch.WordTrace tailWord_412884 prefixEnd_412884 141338631034045215434125 := by
  unfold tailWord_412884
  simp only [CollatzResearch.WordTrace]
  refine ⟨7529558318099628909162853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10039411090799505212217137 7529558318099628909162853)
  ·
    refine ⟨1411792184643680420468035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7529558318099628909162853 1411792184643680420468035)
    ·
      refine ⟨2117688276965520630702053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1411792184643680420468035 2117688276965520630702053)
      ·
        refine ⟨397066551931035118256635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2117688276965520630702053 397066551931035118256635)
        ·
          refine ⟨595599827896552677384953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397066551931035118256635 595599827896552677384953)
          ·
            refine ⟨446699870922414508038715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 595599827896552677384953 446699870922414508038715)
            ·
              refine ⟨670049806383621762058073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446699870922414508038715 670049806383621762058073)
              ·
                refine ⟨502537354787716321543555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 670049806383621762058073 502537354787716321543555)
                ·
                  refine ⟨753806032181574482315333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 502537354787716321543555 753806032181574482315333)
                  ·
                    refine ⟨141338631034045215434125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753806032181574482315333 141338631034045215434125)
                    ·
                      rfl

theorem cell22_412884_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 4, 1, 2, 1, 2, 1, 4].length) (baseStart_412884 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412884 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412884 prefixEnd_412884 := by exact prefixLift 412884
  have htrace : WordTrace (prefixWord ++ tailWord_412884) baseStart_412884 baseEnd_412884 := by
    simpa [prefixWord, tailWord_412884, baseEnd_412884] using wordTrace_append hprefix tailTrace_412884
  have hstable : (prefixWord ++ tailWord_412884).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412884).length < 2 ^ (prefixWord ++ tailWord_412884).sum := by decide
  have hdescent : baseEnd_412884 < baseStart_412884 := by decide
  rcases family_descends (prefixWord ++ tailWord_412884) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412916 : List Nat := [2, 6, 1, 2, 1, 1, 1, 4, 4]
def baseStart_412916 : Nat := 118140960795 + 412916 * 2 ^ 59
def prefixEnd_412916 : Nat := 4983230072969 + 3 ^ 40 * 412916 * 2
def baseEnd_412916 : Nat := 47116528429335932878009

theorem tailTrace_412916 : CollatzResearch.WordTrace tailWord_412916 prefixEnd_412916 47116528429335932878009 := by
  unfold tailWord_412916
  simp only [CollatzResearch.WordTrace]
  refine ⟨7530141886041663641745301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10040189181388884855660401 7530141886041663641745301)
  ·
    refine ⟨352975400908202983206811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7530141886041663641745301 352975400908202983206811)
    ·
      refine ⟨529463101362304474810217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 352975400908202983206811 529463101362304474810217)
      ·
        refine ⟨397097326021728356107663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529463101362304474810217 397097326021728356107663)
        ·
          refine ⟨595645989032592534161495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397097326021728356107663 595645989032592534161495)
          ·
            refine ⟨893468983548888801242243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595645989032592534161495 893468983548888801242243)
            ·
              refine ⟨1340203475323333201863365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 893468983548888801242243 1340203475323333201863365)
              ·
                refine ⟨251288151623124975349381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1340203475323333201863365 251288151623124975349381)
                ·
                  refine ⟨47116528429335932878009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251288151623124975349381 47116528429335932878009)
                  ·
                    rfl

theorem cell22_412916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 1, 1, 4, 4].length) (baseStart_412916 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412916 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412916 prefixEnd_412916 := by exact prefixLift 412916
  have htrace : WordTrace (prefixWord ++ tailWord_412916) baseStart_412916 baseEnd_412916 := by
    simpa [prefixWord, tailWord_412916, baseEnd_412916] using wordTrace_append hprefix tailTrace_412916
  have hstable : (prefixWord ++ tailWord_412916).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412916).length < 2 ^ (prefixWord ++ tailWord_412916).sum := by decide
  have hdescent : baseEnd_412916 < baseStart_412916 := by decide
  rcases family_descends (prefixWord ++ tailWord_412916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412946 : List Nat := [3, 2, 4, 2, 2, 1, 1, 1, 2, 4]
def baseStart_412946 : Nat := 118140960795 + 412946 * 2 ^ 59
def prefixEnd_412946 : Nat := 4983230072969 + 3 ^ 40 * 412946 * 2
def baseEnd_412946 : Nat := 141359854901097720383935

theorem tailTrace_412946 : CollatzResearch.WordTrace tailWord_412946 prefixEnd_412946 141359854901097720383935 := by
  unfold tailWord_412946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765344490493660601770673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10040918641316428271388461 3765344490493660601770673)
  ·
    refine ⟨2824008367870245451328005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3765344490493660601770673 2824008367870245451328005)
    ·
      refine ⟨529501568975671022124001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2824008367870245451328005 529501568975671022124001)
      ·
        refine ⟨397126176731753266593001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 529501568975671022124001 397126176731753266593001)
        ·
          refine ⟨297844632548814949944751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 397126176731753266593001 297844632548814949944751)
          ·
            refine ⟨446766948823222424917127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297844632548814949944751 446766948823222424917127)
            ·
              refine ⟨670150423234833637375691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446766948823222424917127 670150423234833637375691)
              ·
                refine ⟨1005225634852250456063537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670150423234833637375691 1005225634852250456063537)
                ·
                  refine ⟨753919226139187842047653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1005225634852250456063537 753919226139187842047653)
                  ·
                    refine ⟨141359854901097720383935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 753919226139187842047653 141359854901097720383935)
                    ·
                      rfl

theorem cell22_412946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 2, 1, 1, 1, 2, 4].length) (baseStart_412946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412946 prefixEnd_412946 := by exact prefixLift 412946
  have htrace : WordTrace (prefixWord ++ tailWord_412946) baseStart_412946 baseEnd_412946 := by
    simpa [prefixWord, tailWord_412946, baseEnd_412946] using wordTrace_append hprefix tailTrace_412946
  have hstable : (prefixWord ++ tailWord_412946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412946).length < 2 ^ (prefixWord ++ tailWord_412946).sum := by decide
  have hdescent : baseEnd_412946 < baseStart_412946 := by decide
  rcases family_descends (prefixWord ++ tailWord_412946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412959 : List Nat := [1, 1, 2, 4, 4, 1, 2, 3, 1, 3]
def baseStart_412959 : Nat := 118140960795 + 412959 * 2 ^ 59
def prefixEnd_412959 : Nat := 4983230072969 + 3 ^ 40 * 412959 * 2
def baseEnd_412959 : Nat := 141364305066770019808895

theorem tailTrace_412959 : CollatzResearch.WordTrace tailWord_412959 prefixEnd_412959 141364305066770019808895 := by
  unfold tailWord_412959
  simp only [CollatzResearch.WordTrace]
  refine ⟨15061852110927545627305931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10041234740618363751537287 15061852110927545627305931)
  ·
    refine ⟨22592778166391318440958897, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15061852110927545627305931 22592778166391318440958897)
    ·
      refine ⟨16944583624793488830719173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22592778166391318440958897 16944583624793488830719173)
      ·
        refine ⟨3177109429648779155759845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16944583624793488830719173 3177109429648779155759845)
        ·
          refine ⟨595708018059146091704971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3177109429648779155759845 595708018059146091704971)
          ·
            refine ⟨893562027088719137557457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595708018059146091704971 893562027088719137557457)
            ·
              refine ⟨670171520316539353168093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 893562027088719137557457 670171520316539353168093)
              ·
                refine ⟨251314320118702257438035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670171520316539353168093 251314320118702257438035)
                ·
                  refine ⟨376971480178053386157053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251314320118702257438035 376971480178053386157053)
                  ·
                    refine ⟨141364305066770019808895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 376971480178053386157053 141364305066770019808895)
                    ·
                      rfl

theorem cell22_412959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 3, 1, 3].length) (baseStart_412959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412959 prefixEnd_412959 := by exact prefixLift 412959
  have htrace : WordTrace (prefixWord ++ tailWord_412959) baseStart_412959 baseEnd_412959 := by
    simpa [prefixWord, tailWord_412959, baseEnd_412959] using wordTrace_append hprefix tailTrace_412959
  have hstable : (prefixWord ++ tailWord_412959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412959).length < 2 ^ (prefixWord ++ tailWord_412959).sum := by decide
  have hdescent : baseEnd_412959 < baseStart_412959 := by decide
  rcases family_descends (prefixWord ++ tailWord_412959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412970 : List Nat := [3, 1, 4, 2, 1, 1, 1, 2, 2, 5]
def baseStart_412970 : Nat := 118140960795 + 412970 * 2 ^ 59
def prefixEnd_412970 : Nat := 4983230072969 + 3 ^ 40 * 412970 * 2
def baseEnd_412970 : Nat := 141368070591569657783861

theorem tailTrace_412970 : CollatzResearch.WordTrace tailWord_412970 prefixEnd_412970 141368070591569657783861 := by
  unfold tailWord_412970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3765563328471923626489091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10041502209258463003970909 3765563328471923626489091)
  ·
    refine ⟨5648344992707885439733637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3765563328471923626489091 5648344992707885439733637)
    ·
      refine ⟨1059064686132728519950057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5648344992707885439733637 1059064686132728519950057)
      ·
        refine ⟨794298514599546389962543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059064686132728519950057 794298514599546389962543)
        ·
          refine ⟨1191447771899319584943815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794298514599546389962543 1191447771899319584943815)
          ·
            refine ⟨1787171657848979377415723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1191447771899319584943815 1787171657848979377415723)
            ·
              refine ⟨2680757486773469066123585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787171657848979377415723 2680757486773469066123585)
              ·
                refine ⟨2010568115080101799592689, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2680757486773469066123585 2010568115080101799592689)
                ·
                  refine ⟨1507926086310076349694517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2010568115080101799592689 1507926086310076349694517)
                  ·
                    refine ⟨141368070591569657783861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1507926086310076349694517 141368070591569657783861)
                    ·
                      rfl

theorem cell22_412970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 2, 2, 5].length) (baseStart_412970 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412970 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412970 prefixEnd_412970 := by exact prefixLift 412970
  have htrace : WordTrace (prefixWord ++ tailWord_412970) baseStart_412970 baseEnd_412970 := by
    simpa [prefixWord, tailWord_412970, baseEnd_412970] using wordTrace_append hprefix tailTrace_412970
  have hstable : (prefixWord ++ tailWord_412970).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412970).length < 2 ^ (prefixWord ++ tailWord_412970).sum := by decide
  have hdescent : baseEnd_412970 < baseStart_412970 := by decide
  rcases family_descends (prefixWord ++ tailWord_412970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_412989 : List Nat := [1, 4, 1, 5, 1, 1, 3, 1, 5]
def baseStart_412989 : Nat := 118140960795 + 412989 * 2 ^ 59
def prefixEnd_412989 : Nat := 4983230072969 + 3 ^ 40 * 412989 * 2
def baseEnd_412989 : Nat := 47124858226619980519601

theorem tailTrace_412989 : CollatzResearch.WordTrace tailWord_412989 prefixEnd_412989 47124858226619980519601 := by
  unfold tailWord_412989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15062946300818860750898021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10041964200545907167265347 15062946300818860750898021)
  ·
    refine ⟨2824302431403536390793379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15062946300818860750898021 2824302431403536390793379)
    ·
      refine ⟨4236453647105304586190069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824302431403536390793379 4236453647105304586190069)
      ·
        refine ⟨397167529416122304955319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4236453647105304586190069 397167529416122304955319)
        ·
          refine ⟨595751294124183457432979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 397167529416122304955319 595751294124183457432979)
          ·
            refine ⟨893626941186275186149469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 595751294124183457432979 893626941186275186149469)
            ·
              refine ⟨335110102944853194806051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 893626941186275186149469 335110102944853194806051)
              ·
                refine ⟨502665154417279792209077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335110102944853194806051 502665154417279792209077)
                ·
                  refine ⟨47124858226619980519601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 502665154417279792209077 47124858226619980519601)
                  ·
                    rfl

theorem cell22_412989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 1, 3, 1, 5].length) (baseStart_412989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_412989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_412989 prefixEnd_412989 := by exact prefixLift 412989
  have htrace : WordTrace (prefixWord ++ tailWord_412989) baseStart_412989 baseEnd_412989 := by
    simpa [prefixWord, tailWord_412989, baseEnd_412989] using wordTrace_append hprefix tailTrace_412989
  have hstable : (prefixWord ++ tailWord_412989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_412989).length < 2 ^ (prefixWord ++ tailWord_412989).sum := by decide
  have hdescent : baseEnd_412989 < baseStart_412989 := by decide
  rcases family_descends (prefixWord ++ tailWord_412989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413015 : List Nat := [1, 1, 3, 2, 3, 2, 1, 2, 4, 3]
def baseStart_413015 : Nat := 118140960795 + 413015 * 2 ^ 59
def prefixEnd_413015 : Nat := 4983230072969 + 3 ^ 40 * 413015 * 2
def baseEnd_413015 : Nat := 141383475011204540408723

theorem tailTrace_413015 : CollatzResearch.WordTrace tailWord_413015 prefixEnd_413015 141383475011204540408723 := by
  unfold tailWord_413015
  simp only [CollatzResearch.WordTrace]
  refine ⟨15063894598724667191344499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10042596399149778127562999 15063894598724667191344499)
  ·
    refine ⟨22595841898087000787016749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15063894598724667191344499 22595841898087000787016749)
    ·
      refine ⟨8473440711782625295131281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22595841898087000787016749 8473440711782625295131281)
      ·
        refine ⟨6355080533836968971348461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8473440711782625295131281 6355080533836968971348461)
        ·
          refine ⟨2383155200188863364255673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6355080533836968971348461 2383155200188863364255673)
          ·
            refine ⟨1787366400141647523191755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383155200188863364255673 1787366400141647523191755)
            ·
              refine ⟨2681049600212471284787633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1787366400141647523191755 2681049600212471284787633)
              ·
                refine ⟨2010787200159353463590725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2681049600212471284787633 2010787200159353463590725)
                ·
                  refine ⟨377022600029878774423261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2010787200159353463590725 377022600029878774423261)
                  ·
                    refine ⟨141383475011204540408723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377022600029878774423261 141383475011204540408723)
                    ·
                      rfl

theorem cell22_413015_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 1, 2, 4, 3].length) (baseStart_413015 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413015 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413015 prefixEnd_413015 := by exact prefixLift 413015
  have htrace : WordTrace (prefixWord ++ tailWord_413015) baseStart_413015 baseEnd_413015 := by
    simpa [prefixWord, tailWord_413015, baseEnd_413015] using wordTrace_append hprefix tailTrace_413015
  have hstable : (prefixWord ++ tailWord_413015).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413015).length < 2 ^ (prefixWord ++ tailWord_413015).sum := by decide
  have hdescent : baseEnd_413015 < baseStart_413015 := by decide
  rcases family_descends (prefixWord ++ tailWord_413015) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413028 : List Nat := [2, 3, 1, 1, 3, 2, 10]
def baseStart_413028 : Nat := 118140960795 + 413028 * 2 ^ 59
def prefixEnd_413028 : Nat := 4983230072969 + 3 ^ 40 * 413028 * 2
def baseEnd_413028 : Nat := 5236589821365808882729

theorem tailTrace_413028 : CollatzResearch.WordTrace tailWord_413028 prefixEnd_413028 5236589821365808882729 := by
  unfold tailWord_413028
  simp only [CollatzResearch.WordTrace]
  refine ⟨7532184373838785205783869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10042912498451713607711825 7532184373838785205783869)
  ·
    refine ⟨2824569140189544452168951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7532184373838785205783869 2824569140189544452168951)
    ·
      refine ⟨4236853710284316678253427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2824569140189544452168951 4236853710284316678253427)
      ·
        refine ⟨6355280565426475017380141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4236853710284316678253427 6355280565426475017380141)
        ·
          refine ⟨2383230212034928131517553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6355280565426475017380141 2383230212034928131517553)
          ·
            refine ⟨1787422659026196098638165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2383230212034928131517553 1787422659026196098638165)
            ·
              refine ⟨5236589821365808882729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1787422659026196098638165 5236589821365808882729)
              ·
                rfl

theorem cell22_413028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 2, 10].length) (baseStart_413028 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413028 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413028 prefixEnd_413028 := by exact prefixLift 413028
  have htrace : WordTrace (prefixWord ++ tailWord_413028) baseStart_413028 baseEnd_413028 := by
    simpa [prefixWord, tailWord_413028, baseEnd_413028] using wordTrace_append hprefix tailTrace_413028
  have hstable : (prefixWord ++ tailWord_413028).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413028).length < 2 ^ (prefixWord ++ tailWord_413028).sum := by decide
  have hdescent : baseEnd_413028 < baseStart_413028 := by decide
  rcases family_descends (prefixWord ++ tailWord_413028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413034 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 6]
def baseStart_413034 : Nat := 118140960795 + 413034 * 2 ^ 59
def prefixEnd_413034 : Nat := 4983230072969 + 3 ^ 40 * 413034 * 2
def baseEnd_413034 : Nat := 47129993033164941394555

theorem tailTrace_413034 : CollatzResearch.WordTrace tailWord_413034 prefixEnd_413034 47129993033164941394555 := by
  unfold tailWord_413034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3766146896413958359071539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10043058390437222290857437 3766146896413958359071539)
  ·
    refine ⟨5649220344620937538607309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3766146896413958359071539 5649220344620937538607309)
    ·
      refine ⟨2118457629232851576977741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5649220344620937538607309 2118457629232851576977741)
      ·
        refine ⟨794421610962319341366653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2118457629232851576977741 794421610962319341366653)
        ·
          refine ⟨297908104110869753012495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 794421610962319341366653 297908104110869753012495)
          ·
            refine ⟨446862156166304629518743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 297908104110869753012495 446862156166304629518743)
            ·
              refine ⟨670293234249456944278115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 446862156166304629518743 670293234249456944278115)
              ·
                refine ⟨1005439851374185416417173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 670293234249456944278115 1005439851374185416417173)
                ·
                  refine ⟨47129993033164941394555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1005439851374185416417173 47129993033164941394555)
                  ·
                    rfl

theorem cell22_413034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 6].length) (baseStart_413034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413034 prefixEnd_413034 := by exact prefixLift 413034
  have htrace : WordTrace (prefixWord ++ tailWord_413034) baseStart_413034 baseEnd_413034 := by
    simpa [prefixWord, tailWord_413034, baseEnd_413034] using wordTrace_append hprefix tailTrace_413034
  have hstable : (prefixWord ++ tailWord_413034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413034).length < 2 ^ (prefixWord ++ tailWord_413034).sum := by decide
  have hdescent : baseEnd_413034 < baseStart_413034 := by decide
  rcases family_descends (prefixWord ++ tailWord_413034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413105 : List Nat := [1, 2, 2, 4, 1, 1, 3, 1, 2, 5]
def baseStart_413105 : Nat := 118140960795 + 413105 * 2 ^ 59
def prefixEnd_413105 : Nat := 4983230072969 + 3 ^ 40 * 413105 * 2
def baseEnd_413105 : Nat := 141414283850474305658447

theorem tailTrace_413105 : CollatzResearch.WordTrace tailWord_413105 prefixEnd_413105 141414283850474305658447 := by
  unfold tailWord_413105
  simp only [CollatzResearch.WordTrace]
  refine ⟨15067177168398612562120769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10044784778932408374747179 15067177168398612562120769)
  ·
    refine ⟨11300382876298959421590577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15067177168398612562120769 11300382876298959421590577)
    ·
      refine ⟨8475287157224219566192933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11300382876298959421590577 8475287157224219566192933)
      ·
        refine ⟨1589116341979541168661175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8475287157224219566192933 1589116341979541168661175)
        ·
          refine ⟨2383674512969311752991763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1589116341979541168661175 2383674512969311752991763)
          ·
            refine ⟨3575511769453967629487645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2383674512969311752991763 3575511769453967629487645)
            ·
              refine ⟨1340816913545237861057867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3575511769453967629487645 1340816913545237861057867)
              ·
                refine ⟨2011225370317856791586801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340816913545237861057867 2011225370317856791586801)
                ·
                  refine ⟨1508419027738392593690101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2011225370317856791586801 1508419027738392593690101)
                  ·
                    refine ⟨141414283850474305658447, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1508419027738392593690101 141414283850474305658447)
                    ·
                      rfl

theorem cell22_413105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 3, 1, 2, 5].length) (baseStart_413105 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413105 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413105 prefixEnd_413105 := by exact prefixLift 413105
  have htrace : WordTrace (prefixWord ++ tailWord_413105) baseStart_413105 baseEnd_413105 := by
    simpa [prefixWord, tailWord_413105, baseEnd_413105] using wordTrace_append hprefix tailTrace_413105
  have hstable : (prefixWord ++ tailWord_413105).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413105).length < 2 ^ (prefixWord ++ tailWord_413105).sum := by decide
  have hdescent : baseEnd_413105 < baseStart_413105 := by decide
  rcases family_descends (prefixWord ++ tailWord_413105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413120 : List Nat := [2, 1, 1, 2, 3, 1, 4, 1, 3, 4]
def baseStart_413120 : Nat := 118140960795 + 413120 * 2 ^ 59
def prefixEnd_413120 : Nat := 4983230072969 + 3 ^ 40 * 413120 * 2
def baseEnd_413120 : Nat := 141419418657019266533401

theorem tailTrace_413120 : CollatzResearch.WordTrace tailWord_413120 prefixEnd_413120 141419418657019266533401 := by
  unfold tailWord_413120
  simp only [CollatzResearch.WordTrace]
  refine ⟨7533862131672135061958407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10045149508896180082611209 7533862131672135061958407)
  ·
    refine ⟨11300793197508202592937611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7533862131672135061958407 11300793197508202592937611)
    ·
      refine ⟨16951189796262303889406417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11300793197508202592937611 16951189796262303889406417)
      ·
        refine ⟨12713392347196727917054813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16951189796262303889406417 12713392347196727917054813)
        ·
          refine ⟨4767522130198772968895555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12713392347196727917054813 4767522130198772968895555)
          ·
            refine ⟨7151283195298159453343333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4767522130198772968895555 7151283195298159453343333)
            ·
              refine ⟨1340865599118404897501875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7151283195298159453343333 1340865599118404897501875)
              ·
                refine ⟨2011298398677607346252813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1340865599118404897501875 2011298398677607346252813)
                ·
                  refine ⟨754236899504102754844805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2011298398677607346252813 754236899504102754844805)
                  ·
                    refine ⟨141419418657019266533401, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 754236899504102754844805 141419418657019266533401)
                    ·
                      rfl

theorem cell22_413120_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 1, 4, 1, 3, 4].length) (baseStart_413120 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413120 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413120 prefixEnd_413120 := by exact prefixLift 413120
  have htrace : WordTrace (prefixWord ++ tailWord_413120) baseStart_413120 baseEnd_413120 := by
    simpa [prefixWord, tailWord_413120, baseEnd_413120] using wordTrace_append hprefix tailTrace_413120
  have hstable : (prefixWord ++ tailWord_413120).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413120).length < 2 ^ (prefixWord ++ tailWord_413120).sum := by decide
  have hdescent : baseEnd_413120 < baseStart_413120 := by decide
  rcases family_descends (prefixWord ++ tailWord_413120) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413167 : List Nat := [1, 1, 2, 1, 4, 1, 2, 5, 2, 3]
def baseStart_413167 : Nat := 118140960795 + 413167 * 2 ^ 59
def prefixEnd_413167 : Nat := 4983230072969 + 3 ^ 40 * 413167 * 2
def baseEnd_413167 : Nat := 141435507717526810608257

theorem tailTrace_413167 : CollatzResearch.WordTrace tailWord_413167 prefixEnd_413167 141435507717526810608257 := by
  unfold tailWord_413167
  simp only [CollatzResearch.WordTrace]
  refine ⟨15069438494173997150877755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10046292329449331433918503 15069438494173997150877755)
  ·
    refine ⟨22604157741260995726316633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15069438494173997150877755 22604157741260995726316633)
    ·
      refine ⟨16953118305945746794737475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22604157741260995726316633 16953118305945746794737475)
      ·
        refine ⟨25429677458918620192106213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16953118305945746794737475 25429677458918620192106213)
        ·
          refine ⟨4768064523547241286019915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25429677458918620192106213 4768064523547241286019915)
          ·
            refine ⟨7152096785320861929029873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768064523547241286019915 7152096785320861929029873)
            ·
              refine ⟨5364072588990646446772405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7152096785320861929029873 5364072588990646446772405)
              ·
                refine ⟨502881805217873104384913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5364072588990646446772405 502881805217873104384913)
                ·
                  refine ⟨377161353913404828288685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 502881805217873104384913 377161353913404828288685)
                  ·
                    refine ⟨141435507717526810608257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377161353913404828288685 141435507717526810608257)
                    ·
                      rfl

theorem cell22_413167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 5, 2, 3].length) (baseStart_413167 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413167 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413167 prefixEnd_413167 := by exact prefixLift 413167
  have htrace : WordTrace (prefixWord ++ tailWord_413167) baseStart_413167 baseEnd_413167 := by
    simpa [prefixWord, tailWord_413167, baseEnd_413167] using wordTrace_append hprefix tailTrace_413167
  have hstable : (prefixWord ++ tailWord_413167).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413167).length < 2 ^ (prefixWord ++ tailWord_413167).sum := by decide
  have hdescent : baseEnd_413167 < baseStart_413167 := by decide
  rcases family_descends (prefixWord ++ tailWord_413167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413186 : List Nat := [3, 4, 1, 2, 1, 1, 3, 3, 4]
def baseStart_413186 : Nat := 118140960795 + 413186 * 2 ^ 59
def prefixEnd_413186 : Nat := 4983230072969 + 3 ^ 40 * 413186 * 2
def baseEnd_413186 : Nat := 47147337268605698127733

theorem tailTrace_413186 : CollatzResearch.WordTrace tailWord_413186 prefixEnd_413186 47147337268605698127733 := by
  unfold tailWord_413186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767532870276290848954853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10046754320736775597212941 3767532870276290848954853)
  ·
    refine ⟨706412413176804534179035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3767532870276290848954853 706412413176804534179035)
    ·
      refine ⟨1059618619765206801268553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 706412413176804534179035 1059618619765206801268553)
      ·
        refine ⟨794713964823905100951415, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1059618619765206801268553 794713964823905100951415)
        ·
          refine ⟨1192070947235857651427123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 794713964823905100951415 1192070947235857651427123)
          ·
            refine ⟨1788106420853786477140685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192070947235857651427123 1788106420853786477140685)
            ·
              refine ⟨670539907820169928927757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1788106420853786477140685 670539907820169928927757)
              ·
                refine ⟨251452465432563723347909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 670539907820169928927757 251452465432563723347909)
                ·
                  refine ⟨47147337268605698127733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251452465432563723347909 47147337268605698127733)
                  ·
                    rfl

theorem cell22_413186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_413186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413186 prefixEnd_413186 := by exact prefixLift 413186
  have htrace : WordTrace (prefixWord ++ tailWord_413186) baseStart_413186 baseEnd_413186 := by
    simpa [prefixWord, tailWord_413186, baseEnd_413186] using wordTrace_append hprefix tailTrace_413186
  have hstable : (prefixWord ++ tailWord_413186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413186).length < 2 ^ (prefixWord ++ tailWord_413186).sum := by decide
  have hdescent : baseEnd_413186 < baseStart_413186 := by decide
  rcases family_descends (prefixWord ++ tailWord_413186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413210 : List Nat := [3, 1, 1, 3, 1, 1, 1, 3, 2, 6]
def baseStart_413210 : Nat := 118140960795 + 413210 * 2 ^ 59
def prefixEnd_413210 : Nat := 4983230072969 + 3 ^ 40 * 413210 * 2
def baseEnd_413210 : Nat := 141450227496289031783125

theorem tailTrace_413210 : CollatzResearch.WordTrace tailWord_413210 prefixEnd_413210 141450227496289031783125 := by
  unfold tailWord_413210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3767751708254553873673271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10047337888678810329795389 3767751708254553873673271)
  ·
    refine ⟨5651627562381830810509907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3767751708254553873673271 5651627562381830810509907)
    ·
      refine ⟨8477441343572746215764861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5651627562381830810509907 8477441343572746215764861)
      ·
        refine ⟨3179040503839779830911823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8477441343572746215764861 3179040503839779830911823)
        ·
          refine ⟨4768560755759669746367735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179040503839779830911823 4768560755759669746367735)
          ·
            refine ⟨7152841133639504619551603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4768560755759669746367735 7152841133639504619551603)
            ·
              refine ⟨10729261700459256929327405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7152841133639504619551603 10729261700459256929327405)
              ·
                refine ⟨4023473137672221348497777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10729261700459256929327405 4023473137672221348497777)
                ·
                  refine ⟨3017604853254166011373333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4023473137672221348497777 3017604853254166011373333)
                  ·
                    refine ⟨141450227496289031783125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3017604853254166011373333 141450227496289031783125)
                    ·
                      rfl

theorem cell22_413210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 1, 3, 2, 6].length) (baseStart_413210 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413210 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413210 prefixEnd_413210 := by exact prefixLift 413210
  have htrace : WordTrace (prefixWord ++ tailWord_413210) baseStart_413210 baseEnd_413210 := by
    simpa [prefixWord, tailWord_413210, baseEnd_413210] using wordTrace_append hprefix tailTrace_413210
  have hstable : (prefixWord ++ tailWord_413210).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413210).length < 2 ^ (prefixWord ++ tailWord_413210).sum := by decide
  have hdescent : baseEnd_413210 < baseStart_413210 := by decide
  rcases family_descends (prefixWord ++ tailWord_413210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413317 : List Nat := [1, 3, 1, 1, 4, 1, 2, 1, 4, 4]
def baseStart_413317 : Nat := 118140960795 + 413317 * 2 ^ 59
def prefixEnd_413317 : Nat := 4983230072969 + 3 ^ 40 * 413317 * 2
def baseEnd_413317 : Nat := 141486855782976419357797

theorem tailTrace_413317 : CollatzResearch.WordTrace tailWord_413317 prefixEnd_413317 141486855782976419357797 := by
  unfold tailWord_413317
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074909443630572768838205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10049939629087048512558803 15074909443630572768838205)
  ·
    refine ⟨5653091041361464788314327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15074909443630572768838205 5653091041361464788314327)
    ·
      refine ⟨8479636562042197182471491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5653091041361464788314327 8479636562042197182471491)
      ·
        refine ⟨12719454843063295773707237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8479636562042197182471491 12719454843063295773707237)
        ·
          refine ⟨2384897783074367957570107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12719454843063295773707237 2384897783074367957570107)
          ·
            refine ⟨3577346674611551936355161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2384897783074367957570107 3577346674611551936355161)
            ·
              refine ⟨2683010005958663952266371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3577346674611551936355161 2683010005958663952266371)
              ·
                refine ⟨4024515008937995928399557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2683010005958663952266371 4024515008937995928399557)
                ·
                  refine ⟨754596564175874236574917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4024515008937995928399557 754596564175874236574917)
                  ·
                    refine ⟨141486855782976419357797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 754596564175874236574917 141486855782976419357797)
                    ·
                      rfl

theorem cell22_413317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 2, 1, 4, 4].length) (baseStart_413317 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413317 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413317 prefixEnd_413317 := by exact prefixLift 413317
  have htrace : WordTrace (prefixWord ++ tailWord_413317) baseStart_413317 baseEnd_413317 := by
    simpa [prefixWord, tailWord_413317, baseEnd_413317] using wordTrace_append hprefix tailTrace_413317
  have hstable : (prefixWord ++ tailWord_413317).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413317).length < 2 ^ (prefixWord ++ tailWord_413317).sum := by decide
  have hdescent : baseEnd_413317 < baseStart_413317 := by decide
  rcases family_descends (prefixWord ++ tailWord_413317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413319 : List Nat := [1, 1, 4, 2, 1, 4, 1, 1, 4, 3]
def baseStart_413319 : Nat := 118140960795 + 413319 * 2 ^ 59
def prefixEnd_413319 : Nat := 4983230072969 + 3 ^ 40 * 413319 * 2
def baseEnd_413319 : Nat := 141487540423849080807791

theorem tailTrace_413319 : CollatzResearch.WordTrace tailWord_413319 prefixEnd_413319 141487540423849080807791 := by
  unfold tailWord_413319
  simp only [CollatzResearch.WordTrace]
  refine ⟨15074982389623327110411011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10049988259748884740274007 15074982389623327110411011)
  ·
    refine ⟨22612473584434990665616517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15074982389623327110411011 22612473584434990665616517)
    ·
      refine ⟨4239838797081560749803097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22612473584434990665616517 4239838797081560749803097)
      ·
        refine ⟨3179879097811170562352323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4239838797081560749803097 3179879097811170562352323)
        ·
          refine ⟨4769818646716755843528485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3179879097811170562352323 4769818646716755843528485)
          ·
            refine ⟨894340996259391720661591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4769818646716755843528485 894340996259391720661591)
            ·
              refine ⟨1341511494389087580992387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 894340996259391720661591 1341511494389087580992387)
              ·
                refine ⟨2012267241583631371488581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1341511494389087580992387 2012267241583631371488581)
                ·
                  refine ⟨377300107796930882154109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2012267241583631371488581 377300107796930882154109)
                  ·
                    refine ⟨141487540423849080807791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377300107796930882154109 141487540423849080807791)
                    ·
                      rfl

theorem cell22_413319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 4, 1, 1, 4, 3].length) (baseStart_413319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413319 prefixEnd_413319 := by exact prefixLift 413319
  have htrace : WordTrace (prefixWord ++ tailWord_413319) baseStart_413319 baseEnd_413319 := by
    simpa [prefixWord, tailWord_413319, baseEnd_413319] using wordTrace_append hprefix tailTrace_413319
  have hstable : (prefixWord ++ tailWord_413319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413319).length < 2 ^ (prefixWord ++ tailWord_413319).sum := by decide
  have hdescent : baseEnd_413319 < baseStart_413319 := by decide
  rcases family_descends (prefixWord ++ tailWord_413319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413366 : List Nat := [5, 1, 3, 1, 1, 3, 8]
def baseStart_413366 : Nat := 118140960795 + 413366 * 2 ^ 59
def prefixEnd_413366 : Nat := 4983230072969 + 3 ^ 40 * 413366 * 2
def baseEnd_413366 : Nat := 5240875166087282403061

theorem tailTrace_413366 : CollatzResearch.WordTrace tailWord_413366 prefixEnd_413366 5240875166087282403061 := by
  unfold tailWord_413366
  simp only [CollatzResearch.WordTrace]
  refine ⟨942293538778315883585747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10051131080302036091581301 942293538778315883585747)
  ·
    refine ⟨1413440308167473825378621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 942293538778315883585747 1413440308167473825378621)
    ·
      refine ⟨530040115562802684516983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1413440308167473825378621 530040115562802684516983)
      ·
        refine ⟨795060173344204026775475, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530040115562802684516983 795060173344204026775475)
        ·
          refine ⟨1192590260016306040163213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795060173344204026775475 1192590260016306040163213)
          ·
            refine ⟨447221347506114765061205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1192590260016306040163213 447221347506114765061205)
            ·
              refine ⟨5240875166087282403061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 447221347506114765061205 5240875166087282403061)
              ·
                rfl

theorem cell22_413366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 3, 8].length) (baseStart_413366 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413366 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413366 prefixEnd_413366 := by exact prefixLift 413366
  have htrace : WordTrace (prefixWord ++ tailWord_413366) baseStart_413366 baseEnd_413366 := by
    simpa [prefixWord, tailWord_413366, baseEnd_413366] using wordTrace_append hprefix tailTrace_413366
  have hstable : (prefixWord ++ tailWord_413366).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413366).length < 2 ^ (prefixWord ++ tailWord_413366).sum := by decide
  have hdescent : baseEnd_413366 < baseStart_413366 := by decide
  rcases family_descends (prefixWord ++ tailWord_413366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413428 : List Nat := [2, 6, 1, 1, 1, 1, 1, 4, 5]
def baseStart_413428 : Nat := 118140960795 + 413428 * 2 ^ 59
def prefixEnd_413428 : Nat := 4983230072969 + 3 ^ 40 * 413428 * 2
def baseEnd_413428 : Nat := 47174951117136376610819

theorem tailTrace_413428 : CollatzResearch.WordTrace tailWord_413428 prefixEnd_413428 47174951117136376610819 := by
  unfold tailWord_413428
  simp only [CollatzResearch.WordTrace]
  refine ⟨7539478973114219363064469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10052638630818959150752625 7539478973114219363064469)
  ·
    refine ⟨353413076864729032643647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7539478973114219363064469 353413076864729032643647)
    ·
      refine ⟨530119615297093548965471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353413076864729032643647 530119615297093548965471)
      ·
        refine ⟨795179422945640323448207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 530119615297093548965471 795179422945640323448207)
        ·
          refine ⟨1192769134418460485172311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795179422945640323448207 1192769134418460485172311)
          ·
            refine ⟨1789153701627690727758467, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1192769134418460485172311 1789153701627690727758467)
            ·
              refine ⟨2683730552441536091637701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1789153701627690727758467 2683730552441536091637701)
              ·
                refine ⟨503199478582788017182069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2683730552441536091637701 503199478582788017182069)
                ·
                  refine ⟨47174951117136376610819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 503199478582788017182069 47174951117136376610819)
                  ·
                    rfl

theorem cell22_413428_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 1, 1, 1, 1, 4, 5].length) (baseStart_413428 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413428 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413428 prefixEnd_413428 := by exact prefixLift 413428
  have htrace : WordTrace (prefixWord ++ tailWord_413428) baseStart_413428 baseEnd_413428 := by
    simpa [prefixWord, tailWord_413428, baseEnd_413428] using wordTrace_append hprefix tailTrace_413428
  have hstable : (prefixWord ++ tailWord_413428).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413428).length < 2 ^ (prefixWord ++ tailWord_413428).sum := by decide
  have hdescent : baseEnd_413428 < baseStart_413428 := by decide
  rcases family_descends (prefixWord ++ tailWord_413428) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413454 : List Nat := [4, 1, 1, 2, 1, 1, 3, 3, 1, 5]
def baseStart_413454 : Nat := 118140960795 + 413454 * 2 ^ 59
def prefixEnd_413454 : Nat := 4983230072969 + 3 ^ 40 * 413454 * 2
def baseEnd_413454 : Nat := 141533753682753728682377

theorem tailTrace_413454 : CollatzResearch.WordTrace tailWord_413454 prefixEnd_413454 141533753682753728682377 := by
  unfold tailWord_413454
  simp only [CollatzResearch.WordTrace]
  refine ⟨1884988280516780645821927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10053270829422830111050277 1884988280516780645821927)
  ·
    refine ⟨2827482420775170968732891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1884988280516780645821927 2827482420775170968732891)
    ·
      refine ⟨4241223631162756453099337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2827482420775170968732891 4241223631162756453099337)
      ·
        refine ⟨3180917723372067339824503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4241223631162756453099337 3180917723372067339824503)
        ·
          refine ⟨4771376585058101009736755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3180917723372067339824503 4771376585058101009736755)
          ·
            refine ⟨7157064877587151514605133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4771376585058101009736755 7157064877587151514605133)
            ·
              refine ⟨2683899329095181817976925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7157064877587151514605133 2683899329095181817976925)
              ·
                refine ⟨1006462248410693181741347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2683899329095181817976925 1006462248410693181741347)
                ·
                  refine ⟨1509693372616039772612021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1006462248410693181741347 1509693372616039772612021)
                  ·
                    refine ⟨141533753682753728682377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1509693372616039772612021 141533753682753728682377)
                    ·
                      rfl

theorem cell22_413454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_413454 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413454 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413454 prefixEnd_413454 := by exact prefixLift 413454
  have htrace : WordTrace (prefixWord ++ tailWord_413454) baseStart_413454 baseEnd_413454 := by
    simpa [prefixWord, tailWord_413454, baseEnd_413454] using wordTrace_append hprefix tailTrace_413454
  have hstable : (prefixWord ++ tailWord_413454).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413454).length < 2 ^ (prefixWord ++ tailWord_413454).sum := by decide
  have hdescent : baseEnd_413454 < baseStart_413454 := by decide
  rcases family_descends (prefixWord ++ tailWord_413454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413550 : List Nat := [4, 1, 2, 3, 1, 3, 1, 1, 3, 3]
def baseStart_413550 : Nat := 118140960795 + 413550 * 2 ^ 59
def prefixEnd_413550 : Nat := 4983230072969 + 3 ^ 40 * 413550 * 2
def baseEnd_413550 : Nat := 141566616444641478282083

theorem tailTrace_413550 : CollatzResearch.WordTrace tailWord_413550 prefixEnd_413550 141566616444641478282083 := by
  unfold tailWord_413550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1885425956473306695258763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10055605101190969041380069 1885425956473306695258763)
  ·
    refine ⟨2828138934709960042888145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1885425956473306695258763 2828138934709960042888145)
    ·
      refine ⟨2121104201032470032166109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2828138934709960042888145 2121104201032470032166109)
      ·
        refine ⟨795414075387176262062291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2121104201032470032166109 795414075387176262062291)
        ·
          refine ⟨1193121113080764393093437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 795414075387176262062291 1193121113080764393093437)
          ·
            refine ⟨447420417405286647410039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1193121113080764393093437 447420417405286647410039)
            ·
              refine ⟨671130626107929971115059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447420417405286647410039 671130626107929971115059)
              ·
                refine ⟨1006695939161894956672589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671130626107929971115059 1006695939161894956672589)
                ·
                  refine ⟨377510977185710608752221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006695939161894956672589 377510977185710608752221)
                  ·
                    refine ⟨141566616444641478282083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377510977185710608752221 141566616444641478282083)
                    ·
                      rfl

theorem cell22_413550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 3, 1, 1, 3, 3].length) (baseStart_413550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413550 prefixEnd_413550 := by exact prefixLift 413550
  have htrace : WordTrace (prefixWord ++ tailWord_413550) baseStart_413550 baseEnd_413550 := by
    simpa [prefixWord, tailWord_413550, baseEnd_413550] using wordTrace_append hprefix tailTrace_413550
  have hstable : (prefixWord ++ tailWord_413550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413550).length < 2 ^ (prefixWord ++ tailWord_413550).sum := by decide
  have hdescent : baseEnd_413550 < baseStart_413550 := by decide
  rcases family_descends (prefixWord ++ tailWord_413550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413649 : List Nat := [1, 2, 2, 1, 2, 1, 2, 2, 1, 8]
def baseStart_413649 : Nat := 118140960795 + 413649 * 2 ^ 59
def prefixEnd_413649 : Nat := 4983230072969 + 3 ^ 40 * 413649 * 2
def baseEnd_413649 : Nat := 141600506167838220056779

theorem tailTrace_413649 : CollatzResearch.WordTrace tailWord_413649 prefixEnd_413649 141600506167838220056779 := by
  unfold tailWord_413649
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087018478427793469924001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10058012318951862313282667 15087018478427793469924001)
  ·
    refine ⟨11315263858820845102443001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15087018478427793469924001 11315263858820845102443001)
    ·
      refine ⟨8486447894115633826832251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11315263858820845102443001 8486447894115633826832251)
      ·
        refine ⟨12729671841173450740248377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8486447894115633826832251 12729671841173450740248377)
        ·
          refine ⟨9547253880880088055186283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12729671841173450740248377 9547253880880088055186283)
          ·
            refine ⟨14320880821320132082779425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9547253880880088055186283 14320880821320132082779425)
            ·
              refine ⟨10740660615990099062084569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14320880821320132082779425 10740660615990099062084569)
              ·
                refine ⟨8055495461992574296563427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10740660615990099062084569 8055495461992574296563427)
                ·
                  refine ⟨12083243192988861444845141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8055495461992574296563427 12083243192988861444845141)
                  ·
                    refine ⟨141600506167838220056779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12083243192988861444845141 141600506167838220056779)
                    ·
                      rfl

theorem cell22_413649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, 8].length) (baseStart_413649 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413649 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413649 prefixEnd_413649 := by exact prefixLift 413649
  have htrace : WordTrace (prefixWord ++ tailWord_413649) baseStart_413649 baseEnd_413649 := by
    simpa [prefixWord, tailWord_413649, baseEnd_413649] using wordTrace_append hprefix tailTrace_413649
  have hstable : (prefixWord ++ tailWord_413649).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413649).length < 2 ^ (prefixWord ++ tailWord_413649).sum := by decide
  have hdescent : baseEnd_413649 < baseStart_413649 := by decide
  rcases family_descends (prefixWord ++ tailWord_413649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413657 : List Nat := [1, 2, 1, 2, 7, 1, 1, 2, 2, 3]
def baseStart_413657 : Nat := 118140960795 + 413657 * 2 ^ 59
def prefixEnd_413657 : Nat := 4983230072969 + 3 ^ 40 * 413657 * 2
def baseEnd_413657 : Nat := 141603244731328865856755

theorem tailTrace_413657 : CollatzResearch.WordTrace tailWord_413657 prefixEnd_413657 141603244731328865856755 := by
  unfold tailWord_413657
  simp only [CollatzResearch.WordTrace]
  refine ⟨15087310262398810836215225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10058206841599207224143483 15087310262398810836215225)
  ·
    refine ⟨11315482696799108127161419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15087310262398810836215225 11315482696799108127161419)
    ·
      refine ⟨16973224045198662190742129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11315482696799108127161419 16973224045198662190742129)
      ·
        refine ⟨12729918033898996643056597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 16973224045198662190742129 12729918033898996643056597)
        ·
          refine ⟨298357453919507733821639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 12729918033898996643056597 298357453919507733821639)
          ·
            refine ⟨447536180879261600732459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298357453919507733821639 447536180879261600732459)
            ·
              refine ⟨671304271318892401098689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447536180879261600732459 671304271318892401098689)
              ·
                refine ⟨503478203489169300824017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671304271318892401098689 503478203489169300824017)
                ·
                  refine ⟨377608652616876975618013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 503478203489169300824017 377608652616876975618013)
                  ·
                    refine ⟨141603244731328865856755, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377608652616876975618013 141603244731328865856755)
                    ·
                      rfl

theorem cell22_413657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 2, 2, 3].length) (baseStart_413657 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413657 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413657 prefixEnd_413657 := by exact prefixLift 413657
  have htrace : WordTrace (prefixWord ++ tailWord_413657) baseStart_413657 baseEnd_413657 := by
    simpa [prefixWord, tailWord_413657, baseEnd_413657] using wordTrace_append hprefix tailTrace_413657
  have hstable : (prefixWord ++ tailWord_413657).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413657).length < 2 ^ (prefixWord ++ tailWord_413657).sum := by decide
  have hdescent : baseEnd_413657 < baseStart_413657 := by decide
  rcases family_descends (prefixWord ++ tailWord_413657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413668 : List Nat := [2, 3, 1, 1, 1, 1, 6, 1, 3, 3]
def baseStart_413668 : Nat := 118140960795 + 413668 * 2 ^ 59
def prefixEnd_413668 : Nat := 4983230072969 + 3 ^ 40 * 413668 * 2
def baseEnd_413668 : Nat := 141607010256128503831721

theorem tailTrace_413668 : CollatzResearch.WordTrace tailWord_413668 prefixEnd_413668 141607010256128503831721 := by
  unfold tailWord_413668
  simp only [CollatzResearch.WordTrace]
  refine ⟨7543855732679479857432829, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10058474310239306476577105 7543855732679479857432829)
  ·
    refine ⟨2828945899754804946537311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7543855732679479857432829 2828945899754804946537311)
    ·
      refine ⟨4243418849632207419805967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2828945899754804946537311 4243418849632207419805967)
      ·
        refine ⟨6365128274448311129708951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4243418849632207419805967 6365128274448311129708951)
        ·
          refine ⟨9547692411672466694563427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6365128274448311129708951 9547692411672466694563427)
          ·
            refine ⟨14321538617508700041845141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9547692411672466694563427 14321538617508700041845141)
            ·
              refine ⟨671322122695720314461491, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14321538617508700041845141 671322122695720314461491)
              ·
                refine ⟨1006983184043580471692237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 671322122695720314461491 1006983184043580471692237)
                ·
                  refine ⟨377618694016342676884589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1006983184043580471692237 377618694016342676884589)
                  ·
                    refine ⟨141607010256128503831721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377618694016342676884589 141607010256128503831721)
                    ·
                      rfl

theorem cell22_413668_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 6, 1, 3, 3].length) (baseStart_413668 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413668 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413668 prefixEnd_413668 := by exact prefixLift 413668
  have htrace : WordTrace (prefixWord ++ tailWord_413668) baseStart_413668 baseEnd_413668 := by
    simpa [prefixWord, tailWord_413668, baseEnd_413668] using wordTrace_append hprefix tailTrace_413668
  have hstable : (prefixWord ++ tailWord_413668).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413668).length < 2 ^ (prefixWord ++ tailWord_413668).sum := by decide
  have hdescent : baseEnd_413668 < baseStart_413668 := by decide
  rcases family_descends (prefixWord ++ tailWord_413668) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413719 : List Nat := [1, 1, 3, 5, 2, 1, 3, 2, 1, 3]
def baseStart_413719 : Nat := 118140960795 + 413719 * 2 ^ 59
def prefixEnd_413719 : Nat := 4983230072969 + 3 ^ 40 * 413719 * 2
def baseEnd_413719 : Nat := 141624468598381370806565

theorem tailTrace_413719 : CollatzResearch.WordTrace tailWord_413719 prefixEnd_413719 141624468598381370806565 := by
  unfold tailWord_413719
  simp only [CollatzResearch.WordTrace]
  refine ⟨15089571588174195424972211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10059714392116130283314807 15089571588174195424972211)
  ·
    refine ⟨22634357382261293137458317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15089571588174195424972211 22634357382261293137458317)
    ·
      refine ⟨8487884018347984926546869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22634357382261293137458317 8487884018347984926546869)
      ·
        refine ⟨795739126720123586863769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8487884018347984926546869 795739126720123586863769)
        ·
          refine ⟨596804345040092690147827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795739126720123586863769 596804345040092690147827)
          ·
            refine ⟨895206517560139035221741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 596804345040092690147827 895206517560139035221741)
            ·
              refine ⟨335702444085052138208153, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895206517560139035221741 335702444085052138208153)
              ·
                refine ⟨251776833063789103656115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335702444085052138208153 251776833063789103656115)
                ·
                  refine ⟨377665249595683655484173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 251776833063789103656115 377665249595683655484173)
                  ·
                    refine ⟨141624468598381370806565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377665249595683655484173 141624468598381370806565)
                    ·
                      rfl

theorem cell22_413719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 2, 1, 3].length) (baseStart_413719 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413719 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413719 prefixEnd_413719 := by exact prefixLift 413719
  have htrace : WordTrace (prefixWord ++ tailWord_413719) baseStart_413719 baseEnd_413719 := by
    simpa [prefixWord, tailWord_413719, baseEnd_413719] using wordTrace_append hprefix tailTrace_413719
  have hstable : (prefixWord ++ tailWord_413719).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413719).length < 2 ^ (prefixWord ++ tailWord_413719).sum := by decide
  have hdescent : baseEnd_413719 < baseStart_413719 := by decide
  rcases family_descends (prefixWord ++ tailWord_413719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413732 : List Nat := [2, 3, 1, 4, 2, 2, 2, 1, 5]
def baseStart_413732 : Nat := 118140960795 + 413732 * 2 ^ 59
def prefixEnd_413732 : Nat := 4983230072969 + 3 ^ 40 * 413732 * 2
def baseEnd_413732 : Nat := 47209639588017890077175

theorem tailTrace_413732 : CollatzResearch.WordTrace tailWord_413732 prefixEnd_413732 47209639588017890077175 := by
  unfold tailWord_413732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7545022868563549322597725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10060030491418065763463633 7545022868563549322597725)
  ·
    refine ⟨2829383575711330995974147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7545022868563549322597725 2829383575711330995974147)
    ·
      refine ⟨4244075363566996493961221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2829383575711330995974147 4244075363566996493961221)
      ·
        refine ⟨795764130668811842617729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4244075363566996493961221 795764130668811842617729)
        ·
          refine ⟨596823098001608881963297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 795764130668811842617729 596823098001608881963297)
          ·
            refine ⟨447617323501206661472473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 596823098001608881963297 447617323501206661472473)
            ·
              refine ⟨335712992625904996104355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 447617323501206661472473 335712992625904996104355)
              ·
                refine ⟨503569488938857494156533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 335712992625904996104355 503569488938857494156533)
                ·
                  refine ⟨47209639588017890077175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 503569488938857494156533 47209639588017890077175)
                  ·
                    rfl

theorem cell22_413732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 2, 2, 2, 1, 5].length) (baseStart_413732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413732 prefixEnd_413732 := by exact prefixLift 413732
  have htrace : WordTrace (prefixWord ++ tailWord_413732) baseStart_413732 baseEnd_413732 := by
    simpa [prefixWord, tailWord_413732, baseEnd_413732] using wordTrace_append hprefix tailTrace_413732
  have hstable : (prefixWord ++ tailWord_413732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413732).length < 2 ^ (prefixWord ++ tailWord_413732).sum := by decide
  have hdescent : baseEnd_413732 < baseStart_413732 := by decide
  rcases family_descends (prefixWord ++ tailWord_413732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413745 : List Nat := [1, 2, 2, 3, 1, 5, 1, 2, 1, 4]
def baseStart_413745 : Nat := 118140960795 + 413745 * 2 ^ 59
def prefixEnd_413745 : Nat := 4983230072969 + 3 ^ 40 * 413745 * 2
def baseEnd_413745 : Nat := 141633368929725969656485

theorem tailTrace_413745 : CollatzResearch.WordTrace tailWord_413745 prefixEnd_413745 141633368929725969656485 := by
  unfold tailWord_413745
  simp only [CollatzResearch.WordTrace]
  refine ⟨15090519886080001865418689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10060346590720001243612459 15090519886080001865418689)
  ·
    refine ⟨11317889914560001399064017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15090519886080001865418689 11317889914560001399064017)
    ·
      refine ⟨8488417435920001049298013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11317889914560001399064017 8488417435920001049298013)
      ·
        refine ⟨3183156538470000393486755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8488417435920001049298013 3183156538470000393486755)
        ·
          refine ⟨4774734807705000590230133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3183156538470000393486755 4774734807705000590230133)
          ·
            refine ⟨447631388222343805334075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4774734807705000590230133 447631388222343805334075)
            ·
              refine ⟨671447082333515708001113, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 447631388222343805334075 671447082333515708001113)
              ·
                refine ⟨503585311750136781000835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671447082333515708001113 503585311750136781000835)
                ·
                  refine ⟨755377967625205171501253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503585311750136781000835 755377967625205171501253)
                  ·
                    refine ⟨141633368929725969656485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 755377967625205171501253 141633368929725969656485)
                    ·
                      rfl

theorem cell22_413745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 5, 1, 2, 1, 4].length) (baseStart_413745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413745 prefixEnd_413745 := by exact prefixLift 413745
  have htrace : WordTrace (prefixWord ++ tailWord_413745) baseStart_413745 baseEnd_413745 := by
    simpa [prefixWord, tailWord_413745, baseEnd_413745] using wordTrace_append hprefix tailTrace_413745
  have hstable : (prefixWord ++ tailWord_413745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413745).length < 2 ^ (prefixWord ++ tailWord_413745).sum := by decide
  have hdescent : baseEnd_413745 < baseStart_413745 := by decide
  rcases family_descends (prefixWord ++ tailWord_413745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413788 : List Nat := [2, 2, 4, 1, 1, 2, 3, 7]
def baseStart_413788 : Nat := 118140960795 + 413788 * 2 ^ 59
def prefixEnd_413788 : Nat := 4983230072969 + 3 ^ 40 * 413788 * 2
def baseEnd_413788 : Nat := 15738676523165354536817

theorem tailTrace_413788 : CollatzResearch.WordTrace tailWord_413788 prefixEnd_413788 15738676523165354536817 := by
  unfold tailWord_413788
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546044112462110104617009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10061392149949480139489345 7546044112462110104617009)
  ·
    refine ⟨5659533084346582578462757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7546044112462110104617009 5659533084346582578462757)
    ·
      refine ⟨1061162453314984233461767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5659533084346582578462757 1061162453314984233461767)
      ·
        refine ⟨1591743679972476350192651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1061162453314984233461767 1591743679972476350192651)
        ·
          refine ⟨2387615519958714525288977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1591743679972476350192651 2387615519958714525288977)
          ·
            refine ⟨1790711639969035893966733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2387615519958714525288977 1790711639969035893966733)
            ·
              refine ⟨671516864988388460237525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1790711639969035893966733 671516864988388460237525)
              ·
                refine ⟨15738676523165354536817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 671516864988388460237525 15738676523165354536817)
                ·
                  rfl

theorem cell22_413788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 3, 7].length) (baseStart_413788 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413788 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413788 prefixEnd_413788 := by exact prefixLift 413788
  have htrace : WordTrace (prefixWord ++ tailWord_413788) baseStart_413788 baseEnd_413788 := by
    simpa [prefixWord, tailWord_413788, baseEnd_413788] using wordTrace_append hprefix tailTrace_413788
  have hstable : (prefixWord ++ tailWord_413788).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413788).length < 2 ^ (prefixWord ++ tailWord_413788).sum := by decide
  have hdescent : baseEnd_413788 < baseStart_413788 := by decide
  rcases family_descends (prefixWord ++ tailWord_413788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413801 : List Nat := [1, 2, 1, 1, 1, 5, 1, 2, 2, 6]
def baseStart_413801 : Nat := 118140960795 + 413801 * 2 ^ 59
def prefixEnd_413801 : Nat := 4983230072969 + 3 ^ 40 * 413801 * 2
def baseEnd_413801 : Nat := 141652538874160490256313

theorem tailTrace_413801 : CollatzResearch.WordTrace tailWord_413801 prefixEnd_413801 141652538874160490256313 := by
  unfold tailWord_413801
  simp only [CollatzResearch.WordTrace]
  refine ⟨15092562373877123429457257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10061708249251415619638171 15092562373877123429457257)
  ·
    refine ⟨11319421780407842572092943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15092562373877123429457257 11319421780407842572092943)
    ·
      refine ⟨16979132670611763858139415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11319421780407842572092943 16979132670611763858139415)
      ·
        refine ⟨25468699005917645787209123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16979132670611763858139415 25468699005917645787209123)
        ·
          refine ⟨38203048508876468680813685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25468699005917645787209123 38203048508876468680813685)
          ·
            refine ⟨3581535797707168938826283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38203048508876468680813685 3581535797707168938826283)
            ·
              refine ⟨5372303696560753408239425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3581535797707168938826283 5372303696560753408239425)
              ·
                refine ⟨4029227772420565056179569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5372303696560753408239425 4029227772420565056179569)
                ·
                  refine ⟨3021920829315423792134677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4029227772420565056179569 3021920829315423792134677)
                  ·
                    refine ⟨141652538874160490256313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3021920829315423792134677 141652538874160490256313)
                    ·
                      rfl

theorem cell22_413801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 6].length) (baseStart_413801 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413801 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413801 prefixEnd_413801 := by exact prefixLift 413801
  have htrace : WordTrace (prefixWord ++ tailWord_413801) baseStart_413801 baseEnd_413801 := by
    simpa [prefixWord, tailWord_413801, baseEnd_413801] using wordTrace_append hprefix tailTrace_413801
  have hstable : (prefixWord ++ tailWord_413801).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413801).length < 2 ^ (prefixWord ++ tailWord_413801).sum := by decide
  have hdescent : baseEnd_413801 < baseStart_413801 := by decide
  rcases family_descends (prefixWord ++ tailWord_413801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413816 : List Nat := [2, 1, 2, 1, 1, 1, 3, 4, 7]
def baseStart_413816 : Nat := 118140960795 + 413816 * 2 ^ 59
def prefixEnd_413816 : Nat := 4983230072969 + 3 ^ 40 * 413816 * 2
def baseEnd_413816 : Nat := 47219224560235150377089

theorem tailTrace_413816 : CollatzResearch.WordTrace tailWord_413816 prefixEnd_413816 47219224560235150377089 := by
  unfold tailWord_413816
  simp only [CollatzResearch.WordTrace]
  refine ⟨7546554734411390495626651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10062072979215187327502201 7546554734411390495626651)
  ·
    refine ⟨11319832101617085743439977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7546554734411390495626651 11319832101617085743439977)
    ·
      refine ⟨8489874076212814307579983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11319832101617085743439977 8489874076212814307579983)
      ·
        refine ⟨12734811114319221461369975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8489874076212814307579983 12734811114319221461369975)
        ·
          refine ⟨19102216671478832192054963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12734811114319221461369975 19102216671478832192054963)
          ·
            refine ⟨28653325007218248288082445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19102216671478832192054963 28653325007218248288082445)
            ·
              refine ⟨10744996877706843108030917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28653325007218248288082445 10744996877706843108030917)
              ·
                refine ⟨2014686914570033082755797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10744996877706843108030917 2014686914570033082755797)
                ·
                  refine ⟨47219224560235150377089, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2014686914570033082755797 47219224560235150377089)
                  ·
                    rfl

theorem cell22_413816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 4, 7].length) (baseStart_413816 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413816 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413816 prefixEnd_413816 := by exact prefixLift 413816
  have htrace : WordTrace (prefixWord ++ tailWord_413816) baseStart_413816 baseEnd_413816 := by
    simpa [prefixWord, tailWord_413816, baseEnd_413816] using wordTrace_append hprefix tailTrace_413816
  have hstable : (prefixWord ++ tailWord_413816).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413816).length < 2 ^ (prefixWord ++ tailWord_413816).sum := by decide
  have hdescent : baseEnd_413816 < baseStart_413816 := by decide
  rcases family_descends (prefixWord ++ tailWord_413816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413925 : List Nat := [1, 3, 1, 4, 2, 1, 1, 3, 2, 4]
def baseStart_413925 : Nat := 118140960795 + 413925 * 2 ^ 59
def prefixEnd_413925 : Nat := 4983230072969 + 3 ^ 40 * 413925 * 2
def baseEnd_413925 : Nat := 141694986608265500155933

theorem tailTrace_413925 : CollatzResearch.WordTrace tailWord_413925 prefixEnd_413925 141694986608265500155933 := by
  unfold tailWord_413925
  simp only [CollatzResearch.WordTrace]
  refine ⟨15097085025427892606971229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10064723350285261737980819 15097085025427892606971229)
  ·
    refine ⟨5661406884535459727614211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15097085025427892606971229 5661406884535459727614211)
    ·
      refine ⟨8492110326803189591421317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5661406884535459727614211 8492110326803189591421317)
      ·
        refine ⟨1592270686275598048391497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8492110326803189591421317 1592270686275598048391497)
        ·
          refine ⟨1194203014706698536293623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1592270686275598048391497 1194203014706698536293623)
          ·
            refine ⟨1791304522060047804440435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194203014706698536293623 1791304522060047804440435)
            ·
              refine ⟨2686956783090071706660653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1791304522060047804440435 2686956783090071706660653)
              ·
                refine ⟨1007608793658776889997745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2686956783090071706660653 1007608793658776889997745)
                ·
                  refine ⟨755706595244082667498309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1007608793658776889997745 755706595244082667498309)
                  ·
                    refine ⟨141694986608265500155933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 755706595244082667498309 141694986608265500155933)
                    ·
                      rfl

theorem cell22_413925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 1, 3, 2, 4].length) (baseStart_413925 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413925 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413925 prefixEnd_413925 := by exact prefixLift 413925
  have htrace : WordTrace (prefixWord ++ tailWord_413925) baseStart_413925 baseEnd_413925 := by
    simpa [prefixWord, tailWord_413925, baseEnd_413925] using wordTrace_append hprefix tailTrace_413925
  have hstable : (prefixWord ++ tailWord_413925).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413925).length < 2 ^ (prefixWord ++ tailWord_413925).sum := by decide
  have hdescent : baseEnd_413925 < baseStart_413925 := by decide
  rcases family_descends (prefixWord ++ tailWord_413925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413940 : List Nat := [2, 6, 1, 13]
def baseStart_413940 : Nat := 118140960795 + 413940 * 2 ^ 59
def prefixEnd_413940 : Nat := 4983230072969 + 3 ^ 40 * 413940 * 2
def baseEnd_413940 : Nat := 194376023888628890303

theorem tailTrace_413940 : CollatzResearch.WordTrace tailWord_413940 prefixEnd_413940 194376023888628890303 := by
  unfold tailWord_413940
  simp only [CollatzResearch.WordTrace]
  refine ⟨7548816060186775084383637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10065088080249033445844849 7548816060186775084383637)
  ·
    refine ⟨353850752821255082080483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 7548816060186775084383637 353850752821255082080483)
    ·
      refine ⟨530776129231882623120725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 353850752821255082080483 530776129231882623120725)
      ·
        refine ⟨194376023888628890303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 13 530776129231882623120725 194376023888628890303)
        ·
          rfl

theorem cell22_413940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 13].length) (baseStart_413940 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413940 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413940 prefixEnd_413940 := by exact prefixLift 413940
  have htrace : WordTrace (prefixWord ++ tailWord_413940) baseStart_413940 baseEnd_413940 := by
    simpa [prefixWord, tailWord_413940, baseEnd_413940] using wordTrace_append hprefix tailTrace_413940
  have hstable : (prefixWord ++ tailWord_413940).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413940).length < 2 ^ (prefixWord ++ tailWord_413940).sum := by decide
  have hdescent : baseEnd_413940 < baseStart_413940 := by decide
  rcases family_descends (prefixWord ++ tailWord_413940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413953 : List Nat := [1, 2, 4, 1, 1, 2, 1, 1, 1, 8]
def baseStart_413953 : Nat := 118140960795 + 413953 * 2 ^ 59
def prefixEnd_413953 : Nat := 4983230072969 + 3 ^ 40 * 413953 * 2
def baseEnd_413953 : Nat := 141704571580482760455847

theorem tailTrace_413953 : CollatzResearch.WordTrace tailWord_413953 prefixEnd_413953 141704571580482760455847 := by
  unfold tailWord_413953
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098106269326453388990513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10065404179550968925993675 15098106269326453388990513)
  ·
    refine ⟨11323579701994840041742885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15098106269326453388990513 11323579701994840041742885)
    ·
      refine ⟨2123171194124032507826791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11323579701994840041742885 2123171194124032507826791)
      ·
        refine ⟨3184756791186048761740187, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2123171194124032507826791 3184756791186048761740187)
        ·
          refine ⟨4777135186779073142610281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3184756791186048761740187 4777135186779073142610281)
          ·
            refine ⟨3582851390084304856957711, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4777135186779073142610281 3582851390084304856957711)
            ·
              refine ⟨5374277085126457285436567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3582851390084304856957711 5374277085126457285436567)
              ·
                refine ⟨8061415627689685928154851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5374277085126457285436567 8061415627689685928154851)
                ·
                  refine ⟨12092123441534528892232277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8061415627689685928154851 12092123441534528892232277)
                  ·
                    refine ⟨141704571580482760455847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12092123441534528892232277 141704571580482760455847)
                    ·
                      rfl

theorem cell22_413953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 1, 1, 1, 8].length) (baseStart_413953 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413953 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413953 prefixEnd_413953 := by exact prefixLift 413953
  have htrace : WordTrace (prefixWord ++ tailWord_413953) baseStart_413953 baseEnd_413953 := by
    simpa [prefixWord, tailWord_413953, baseEnd_413953] using wordTrace_append hprefix tailTrace_413953
  have hstable : (prefixWord ++ tailWord_413953).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413953).length < 2 ^ (prefixWord ++ tailWord_413953).sum := by decide
  have hdescent : baseEnd_413953 < baseStart_413953 := by decide
  rcases family_descends (prefixWord ++ tailWord_413953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_413955 : List Nat := [1, 1, 1, 3, 2, 3, 2, 3, 3, 3]
def baseStart_413955 : Nat := 118140960795 + 413955 * 2 ^ 59
def prefixEnd_413955 : Nat := 4983230072969 + 3 ^ 40 * 413955 * 2
def baseEnd_413955 : Nat := 141705256221355421905841

theorem tailTrace_413955 : CollatzResearch.WordTrace tailWord_413955 prefixEnd_413955 141705256221355421905841 := by
  unfold tailWord_413955
  simp only [CollatzResearch.WordTrace]
  refine ⟨15098179215319207730563319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10065452810212805153708879 15098179215319207730563319)
  ·
    refine ⟨22647268822978811595844979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15098179215319207730563319 22647268822978811595844979)
    ·
      refine ⟨33970903234468217393767469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22647268822978811595844979 33970903234468217393767469)
      ·
        refine ⟨12739088712925581522662801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 33970903234468217393767469 12739088712925581522662801)
        ·
          refine ⟨9554316534694186141997101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12739088712925581522662801 9554316534694186141997101)
          ·
            refine ⟨3582868700510319803248913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9554316534694186141997101 3582868700510319803248913)
            ·
              refine ⟨2687151525382739852436685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3582868700510319803248913 2687151525382739852436685)
              ·
                refine ⟨1007681822018527444663757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2687151525382739852436685 1007681822018527444663757)
                ·
                  refine ⟨377880683256947791748909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1007681822018527444663757 377880683256947791748909)
                  ·
                    refine ⟨141705256221355421905841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 377880683256947791748909 141705256221355421905841)
                    ·
                      rfl

theorem cell22_413955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 3, 3, 3].length) (baseStart_413955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_413955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_413955 prefixEnd_413955 := by exact prefixLift 413955
  have htrace : WordTrace (prefixWord ++ tailWord_413955) baseStart_413955 baseEnd_413955 := by
    simpa [prefixWord, tailWord_413955, baseEnd_413955] using wordTrace_append hprefix tailTrace_413955
  have hstable : (prefixWord ++ tailWord_413955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_413955).length < 2 ^ (prefixWord ++ tailWord_413955).sum := by decide
  have hdescent : baseEnd_413955 < baseStart_413955 := by decide
  rcases family_descends (prefixWord ++ tailWord_413955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414032 : List Nat := [2, 1, 1, 1, 1, 7, 2, 2, 1, 4]
def baseStart_414032 : Nat := 118140960795 + 414032 * 2 ^ 59
def prefixEnd_414032 : Nat := 4983230072969 + 3 ^ 40 * 414032 * 2
def baseEnd_414032 : Nat := 141731614894952887730605

theorem tailTrace_414032 : CollatzResearch.WordTrace tailWord_414032 prefixEnd_414032 141731614894952887730605 := by
  unfold tailWord_414032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7550493818020124940558175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10067325090693499920744233 7550493818020124940558175)
  ·
    refine ⟨11325740727030187410837263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7550493818020124940558175 11325740727030187410837263)
    ·
      refine ⟨16988611090545281116255895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11325740727030187410837263 16988611090545281116255895)
      ·
        refine ⟨25482916635817921674383843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16988611090545281116255895 25482916635817921674383843)
        ·
          refine ⟨38224374953726882511575765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25482916635817921674383843 38224374953726882511575765)
          ·
            refine ⟨895883787977973808865057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 38224374953726882511575765 895883787977973808865057)
            ·
              refine ⟨671912840983480356648793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895883787977973808865057 671912840983480356648793)
              ·
                refine ⟨503934630737610267486595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 671912840983480356648793 503934630737610267486595)
                ·
                  refine ⟨755901946106415401229893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 503934630737610267486595 755901946106415401229893)
                  ·
                    refine ⟨141731614894952887730605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 755901946106415401229893 141731614894952887730605)
                    ·
                      rfl

theorem cell22_414032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 7, 2, 2, 1, 4].length) (baseStart_414032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414032 prefixEnd_414032 := by exact prefixLift 414032
  have htrace : WordTrace (prefixWord ++ tailWord_414032) baseStart_414032 baseEnd_414032 := by
    simpa [prefixWord, tailWord_414032, baseEnd_414032] using wordTrace_append hprefix tailTrace_414032
  have hstable : (prefixWord ++ tailWord_414032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414032).length < 2 ^ (prefixWord ++ tailWord_414032).sum := by decide
  have hdescent : baseEnd_414032 < baseStart_414032 := by decide
  rcases family_descends (prefixWord ++ tailWord_414032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414047 : List Nat := [1, 1, 2, 3, 1, 2, 5, 3, 4]
def baseStart_414047 : Nat := 118140960795 + 414047 * 2 ^ 59
def prefixEnd_414047 : Nat := 4983230072969 + 3 ^ 40 * 414047 * 2
def baseEnd_414047 : Nat := 47245583233832616201853

theorem tailTrace_414047 : CollatzResearch.WordTrace tailWord_414047 prefixEnd_414047 47245583233832616201853 := by
  unfold tailWord_414047
  simp only [CollatzResearch.WordTrace]
  refine ⟨15101534730985907442912395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10067689820657271628608263 15101534730985907442912395)
  ·
    refine ⟨22652302096478861164368593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15101534730985907442912395 22652302096478861164368593)
    ·
      refine ⟨16989226572359145873276445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22652302096478861164368593 16989226572359145873276445)
      ·
        refine ⟨6370959964634679702478667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 16989226572359145873276445 6370959964634679702478667)
        ·
          refine ⟨9556439946952019553718001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6370959964634679702478667 9556439946952019553718001)
          ·
            refine ⟨7167329960214014665288501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9556439946952019553718001 7167329960214014665288501)
            ·
              refine ⟨671937183770063874870797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 7167329960214014665288501 671937183770063874870797)
              ·
                refine ⟨251976443913773953076549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 671937183770063874870797 251976443913773953076549)
                ·
                  refine ⟨47245583233832616201853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251976443913773953076549 47245583233832616201853)
                  ·
                    rfl

theorem cell22_414047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 5, 3, 4].length) (baseStart_414047 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414047 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414047 prefixEnd_414047 := by exact prefixLift 414047
  have htrace : WordTrace (prefixWord ++ tailWord_414047) baseStart_414047 baseEnd_414047 := by
    simpa [prefixWord, tailWord_414047, baseEnd_414047] using wordTrace_append hprefix tailTrace_414047
  have hstable : (prefixWord ++ tailWord_414047).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414047).length < 2 ^ (prefixWord ++ tailWord_414047).sum := by decide
  have hdescent : baseEnd_414047 < baseStart_414047 := by decide
  rcases family_descends (prefixWord ++ tailWord_414047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414064 : List Nat := [2, 1, 1, 1, 4, 4, 3, 2, 4]
def baseStart_414064 : Nat := 118140960795 + 414064 * 2 ^ 59
def prefixEnd_414064 : Nat := 4983230072969 + 3 ^ 40 * 414064 * 2
def baseEnd_414064 : Nat := 47247523049638490310169

theorem tailTrace_414064 : CollatzResearch.WordTrace tailWord_414064 prefixEnd_414064 47247523049638490310169 := by
  unfold tailWord_414064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7551077385962159673140623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10068103181282879564187497 7551077385962159673140623)
  ·
    refine ⟨11326616078943239509710935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7551077385962159673140623 11326616078943239509710935)
    ·
      refine ⟨16989924118414859264566403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11326616078943239509710935 16989924118414859264566403)
      ·
        refine ⟨25484886177622288896849605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 16989924118414859264566403 25484886177622288896849605)
        ·
          refine ⟨4778416158304179168159301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25484886177622288896849605 4778416158304179168159301)
          ·
            refine ⟨895953029682033594029869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4778416158304179168159301 895953029682033594029869)
            ·
              refine ⟨335982386130762597761201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 895953029682033594029869 335982386130762597761201)
              ·
                refine ⟨251986789598071948320901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 335982386130762597761201 251986789598071948320901)
                ·
                  refine ⟨47247523049638490310169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 251986789598071948320901 47247523049638490310169)
                  ·
                    rfl

theorem cell22_414064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 3, 2, 4].length) (baseStart_414064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414064 prefixEnd_414064 := by exact prefixLift 414064
  have htrace : WordTrace (prefixWord ++ tailWord_414064) baseStart_414064 baseEnd_414064 := by
    simpa [prefixWord, tailWord_414064, baseEnd_414064] using wordTrace_append hprefix tailTrace_414064
  have hstable : (prefixWord ++ tailWord_414064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414064).length < 2 ^ (prefixWord ++ tailWord_414064).sum := by decide
  have hdescent : baseEnd_414064 < baseStart_414064 := by decide
  rcases family_descends (prefixWord ++ tailWord_414064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414075 : List Nat := [1, 1, 1, 1, 1, 8, 2, 7]
def baseStart_414075 : Nat := 118140960795 + 414075 * 2 ^ 59
def prefixEnd_414075 : Nat := 4983230072969 + 3 ^ 40 * 414075 * 2
def baseEnd_414075 : Nat := 15749592741523900989497

theorem tailTrace_414075 : CollatzResearch.WordTrace tailWord_414075 prefixEnd_414075 15749592741523900989497 := by
  unfold tailWord_414075
  simp only [CollatzResearch.WordTrace]
  refine ⟨15102555974884468224931679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10068370649922978816621119 15102555974884468224931679)
  ·
    refine ⟨22653833962326702337397519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15102555974884468224931679 22653833962326702337397519)
    ·
      refine ⟨33980750943490053506096279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22653833962326702337397519 33980750943490053506096279)
      ·
        refine ⟨50971126415235080259144419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 33980750943490053506096279 50971126415235080259144419)
        ·
          refine ⟨76456689622852620388716629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 50971126415235080259144419 76456689622852620388716629)
          ·
            refine ⟨895976831517804145180273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 76456689622852620388716629 895976831517804145180273)
            ·
              refine ⟨671982623638353108885205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 895976831517804145180273 671982623638353108885205)
              ·
                refine ⟨15749592741523900989497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 671982623638353108885205 15749592741523900989497)
                ·
                  rfl

theorem cell22_414075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 8, 2, 7].length) (baseStart_414075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414075 prefixEnd_414075 := by exact prefixLift 414075
  have htrace : WordTrace (prefixWord ++ tailWord_414075) baseStart_414075 baseEnd_414075 := by
    simpa [prefixWord, tailWord_414075, baseEnd_414075] using wordTrace_append hprefix tailTrace_414075
  have hstable : (prefixWord ++ tailWord_414075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414075).length < 2 ^ (prefixWord ++ tailWord_414075).sum := by decide
  have hdescent : baseEnd_414075 < baseStart_414075 := by decide
  rcases family_descends (prefixWord ++ tailWord_414075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414094 : List Nat := [4, 1, 1, 4, 1, 2, 2, 1, 2, 4]
def baseStart_414094 : Nat := 118140960795 + 414094 * 2 ^ 59
def prefixEnd_414094 : Nat := 4983230072969 + 3 ^ 40 * 414094 * 2
def baseEnd_414094 : Nat := 141752838762005392680415

theorem tailTrace_414094 : CollatzResearch.WordTrace tailWord_414094 prefixEnd_414094 141752838762005392680415 := by
  unfold tailWord_414094
  simp only [CollatzResearch.WordTrace]
  refine ⟨1887906120226954308734167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10068832641210422979915557 1887906120226954308734167)
  ·
    refine ⟨2831859180340431463101251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1887906120226954308734167 2831859180340431463101251)
    ·
      refine ⟨4247788770510647194651877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2831859180340431463101251 4247788770510647194651877)
      ·
        refine ⟨796460394470746348997227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4247788770510647194651877 796460394470746348997227)
        ·
          refine ⟨1194690591706119523495841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796460394470746348997227 1194690591706119523495841)
          ·
            refine ⟨896017943779589642621881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1194690591706119523495841 896017943779589642621881)
            ·
              refine ⟨672013457834692231966411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896017943779589642621881 672013457834692231966411)
              ·
                refine ⟨1008020186752038347949617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672013457834692231966411 1008020186752038347949617)
                ·
                  refine ⟨756015140064028760962213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1008020186752038347949617 756015140064028760962213)
                  ·
                    refine ⟨141752838762005392680415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756015140064028760962213 141752838762005392680415)
                    ·
                      rfl

theorem cell22_414094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 2, 2, 1, 2, 4].length) (baseStart_414094 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414094 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414094 prefixEnd_414094 := by exact prefixLift 414094
  have htrace : WordTrace (prefixWord ++ tailWord_414094) baseStart_414094 baseEnd_414094 := by
    simpa [prefixWord, tailWord_414094, baseEnd_414094] using wordTrace_append hprefix tailTrace_414094
  have hstable : (prefixWord ++ tailWord_414094).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414094).length < 2 ^ (prefixWord ++ tailWord_414094).sum := by decide
  have hdescent : baseEnd_414094 < baseStart_414094 := by decide
  rcases family_descends (prefixWord ++ tailWord_414094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414135 : List Nat := [1, 1, 3, 1, 3, 3, 1, 1, 1, 7]
def baseStart_414135 : Nat := 118140960795 + 414135 * 2 ^ 59
def prefixEnd_414135 : Nat := 4983230072969 + 3 ^ 40 * 414135 * 2
def baseEnd_414135 : Nat := 141766873899894952405289

theorem tailTrace_414135 : CollatzResearch.WordTrace tailWord_414135 prefixEnd_414135 141766873899894952405289 := by
  unfold tailWord_414135
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104744354667098472115859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10069829569778065648077239 15104744354667098472115859)
  ·
    refine ⟨22657116532000647708173789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15104744354667098472115859 22657116532000647708173789)
    ·
      refine ⟨8496418699500242890565171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22657116532000647708173789 8496418699500242890565171)
      ·
        refine ⟨12744628049250364335847757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8496418699500242890565171 12744628049250364335847757)
        ·
          refine ⟨4779235518468886625942909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12744628049250364335847757 4779235518468886625942909)
          ·
            refine ⟨1792213319425832484728591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4779235518468886625942909 1792213319425832484728591)
            ·
              refine ⟨2688319979138748727092887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1792213319425832484728591 2688319979138748727092887)
              ·
                refine ⟨4032479968708123090639331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2688319979138748727092887 4032479968708123090639331)
                ·
                  refine ⟨6048719953062184635958997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4032479968708123090639331 6048719953062184635958997)
                  ·
                    refine ⟨141766873899894952405289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6048719953062184635958997 141766873899894952405289)
                    ·
                      rfl

theorem cell22_414135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 7].length) (baseStart_414135 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414135 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414135 prefixEnd_414135 := by exact prefixLift 414135
  have htrace : WordTrace (prefixWord ++ tailWord_414135) baseStart_414135 baseEnd_414135 := by
    simpa [prefixWord, tailWord_414135, baseEnd_414135] using wordTrace_append hprefix tailTrace_414135
  have hstable : (prefixWord ++ tailWord_414135).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414135).length < 2 ^ (prefixWord ++ tailWord_414135).sum := by decide
  have hdescent : baseEnd_414135 < baseStart_414135 := by decide
  rcases family_descends (prefixWord ++ tailWord_414135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414137 : List Nat := [1, 2, 1, 4, 3, 1, 2, 3, 5]
def baseStart_414137 : Nat := 118140960795 + 414137 * 2 ^ 59
def prefixEnd_414137 : Nat := 4983230072969 + 3 ^ 40 * 414137 * 2
def baseEnd_414137 : Nat := 47255852846922537951761

theorem tailTrace_414137 : CollatzResearch.WordTrace tailWord_414137 prefixEnd_414137 47255852846922537951761 := by
  unfold tailWord_414137
  simp only [CollatzResearch.WordTrace]
  refine ⟨15104817300659852813688665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10069878200439901875792443 15104817300659852813688665)
  ·
    refine ⟨11328612975494889610266499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15104817300659852813688665 11328612975494889610266499)
    ·
      refine ⟨16992919463242334415399749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11328612975494889610266499 16992919463242334415399749)
      ·
        refine ⟨3186172399357937702887453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 16992919463242334415399749 3186172399357937702887453)
        ·
          refine ⟨1194814649759226638582795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3186172399357937702887453 1194814649759226638582795)
          ·
            refine ⟨1792221974638839957874193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1194814649759226638582795 1792221974638839957874193)
            ·
              refine ⟨1344166480979129968405645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1792221974638839957874193 1344166480979129968405645)
              ·
                refine ⟨504062430367173738152117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1344166480979129968405645 504062430367173738152117)
                ·
                  refine ⟨47255852846922537951761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 504062430367173738152117 47255852846922537951761)
                  ·
                    rfl

theorem cell22_414137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 2, 3, 5].length) (baseStart_414137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414137 prefixEnd_414137 := by exact prefixLift 414137
  have htrace : WordTrace (prefixWord ++ tailWord_414137) baseStart_414137 baseEnd_414137 := by
    simpa [prefixWord, tailWord_414137, baseEnd_414137] using wordTrace_append hprefix tailTrace_414137
  have hstable : (prefixWord ++ tailWord_414137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414137).length < 2 ^ (prefixWord ++ tailWord_414137).sum := by decide
  have hdescent : baseEnd_414137 < baseStart_414137 := by decide
  rcases family_descends (prefixWord ++ tailWord_414137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414145 : List Nat := [1, 2, 7, 1, 2, 1, 1, 1, 2, 4]
def baseStart_414145 : Nat := 118140960795 + 414145 * 2 ^ 59
def prefixEnd_414145 : Nat := 4983230072969 + 3 ^ 40 * 414145 * 2
def baseEnd_414145 : Nat := 141770297104258259655259

theorem tailTrace_414145 : CollatzResearch.WordTrace tailWord_414145 prefixEnd_414145 141770297104258259655259 := by
  unfold tailWord_414145
  simp only [CollatzResearch.WordTrace]
  refine ⟨15105109084630870179979889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10070072723087246786653259 15105109084630870179979889)
  ·
    refine ⟨11328831813473152634984917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15105109084630870179979889 11328831813473152634984917)
    ·
      refine ⟨265519495628277014882459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 11328831813473152634984917 265519495628277014882459)
      ·
        refine ⟨398279243442415522323689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 265519495628277014882459 398279243442415522323689)
        ·
          refine ⟨298709432581811641742767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 398279243442415522323689 298709432581811641742767)
          ·
            refine ⟨448064148872717462614151, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 298709432581811641742767 448064148872717462614151)
            ·
              refine ⟨672096223309076193921227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448064148872717462614151 672096223309076193921227)
              ·
                refine ⟨1008144334963614290881841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 672096223309076193921227 1008144334963614290881841)
                ·
                  refine ⟨756108251222710718161381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1008144334963614290881841 756108251222710718161381)
                  ·
                    refine ⟨141770297104258259655259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756108251222710718161381 141770297104258259655259)
                    ·
                      rfl

theorem cell22_414145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 2, 1, 1, 1, 2, 4].length) (baseStart_414145 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414145 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414145 prefixEnd_414145 := by exact prefixLift 414145
  have htrace : WordTrace (prefixWord ++ tailWord_414145) baseStart_414145 baseEnd_414145 := by
    simpa [prefixWord, tailWord_414145, baseEnd_414145] using wordTrace_append hprefix tailTrace_414145
  have hstable : (prefixWord ++ tailWord_414145).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414145).length < 2 ^ (prefixWord ++ tailWord_414145).sum := by decide
  have hdescent : baseEnd_414145 < baseStart_414145 := by decide
  rcases family_descends (prefixWord ++ tailWord_414145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414180 : List Nat := [2, 3, 1, 1, 1, 1, 1, 1, 2, 9]
def baseStart_414180 : Nat := 118140960795 + 414180 * 2 ^ 59
def prefixEnd_414180 : Nat := 4983230072969 + 3 ^ 40 * 414180 * 2
def baseEnd_414180 : Nat := 141782278319529835030151

theorem tailTrace_414180 : CollatzResearch.WordTrace tailWord_414180 prefixEnd_414180 141782278319529835030151 := by
  unfold tailWord_414180
  simp only [CollatzResearch.WordTrace]
  refine ⟨7553192819752035578751997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10070923759669380771669329 7553192819752035578751997)
  ·
    refine ⟨2832447307407013342031999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7553192819752035578751997 2832447307407013342031999)
    ·
      refine ⟨4248670961110520013047999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2832447307407013342031999 4248670961110520013047999)
      ·
        refine ⟨6373006441665780019571999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4248670961110520013047999 6373006441665780019571999)
        ·
          refine ⟨9559509662498670029357999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6373006441665780019571999 9559509662498670029357999)
          ·
            refine ⟨14339264493748005044036999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9559509662498670029357999 14339264493748005044036999)
            ·
              refine ⟨21508896740622007566055499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14339264493748005044036999 21508896740622007566055499)
              ·
                refine ⟨32263345110933011349083249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21508896740622007566055499 32263345110933011349083249)
                ·
                  refine ⟨24197508833199758511812437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32263345110933011349083249 24197508833199758511812437)
                  ·
                    refine ⟨141782278319529835030151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24197508833199758511812437 141782278319529835030151)
                    ·
                      rfl

theorem cell22_414180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 1, 1, 2, 9].length) (baseStart_414180 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414180 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414180 prefixEnd_414180 := by exact prefixLift 414180
  have htrace : WordTrace (prefixWord ++ tailWord_414180) baseStart_414180 baseEnd_414180 := by
    simpa [prefixWord, tailWord_414180, baseEnd_414180] using wordTrace_append hprefix tailTrace_414180
  have hstable : (prefixWord ++ tailWord_414180).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414180).length < 2 ^ (prefixWord ++ tailWord_414180).sum := by decide
  have hdescent : baseEnd_414180 < baseStart_414180 := by decide
  rcases family_descends (prefixWord ++ tailWord_414180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414195 : List Nat := [1, 1, 1, 2, 2, 2, 3, 1, 3, 6]
def baseStart_414195 : Nat := 118140960795 + 414195 * 2 ^ 59
def prefixEnd_414195 : Nat := 4983230072969 + 3 ^ 40 * 414195 * 2
def baseEnd_414195 : Nat := 141787413126074795905105

theorem tailTrace_414195 : CollatzResearch.WordTrace tailWord_414195 prefixEnd_414195 141787413126074795905105 := by
  unfold tailWord_414195
  simp only [CollatzResearch.WordTrace]
  refine ⟨15106932734449728719300039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10071288489633152479533359 15106932734449728719300039)
  ·
    refine ⟨22660399101674593078950059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15106932734449728719300039 22660399101674593078950059)
    ·
      refine ⟨33990598652511889618425089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22660399101674593078950059 33990598652511889618425089)
      ·
        refine ⟨25492948989383917213818817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 33990598652511889618425089 25492948989383917213818817)
        ·
          refine ⟨19119711742037937910364113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25492948989383917213818817 19119711742037937910364113)
          ·
            refine ⟨14339783806528453432773085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19119711742037937910364113 14339783806528453432773085)
            ·
              refine ⟨5377418927448170037289907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14339783806528453432773085 5377418927448170037289907)
              ·
                refine ⟨8066128391172255055934861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5377418927448170037289907 8066128391172255055934861)
                ·
                  refine ⟨3024798146689595645975573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8066128391172255055934861 3024798146689595645975573)
                  ·
                    refine ⟨141787413126074795905105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3024798146689595645975573 141787413126074795905105)
                    ·
                      rfl

theorem cell22_414195_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 6].length) (baseStart_414195 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414195 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414195 prefixEnd_414195 := by exact prefixLift 414195
  have htrace : WordTrace (prefixWord ++ tailWord_414195) baseStart_414195 baseEnd_414195 := by
    simpa [prefixWord, tailWord_414195, baseEnd_414195] using wordTrace_append hprefix tailTrace_414195
  have hstable : (prefixWord ++ tailWord_414195).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414195).length < 2 ^ (prefixWord ++ tailWord_414195).sum := by decide
  have hdescent : baseEnd_414195 < baseStart_414195 := by decide
  rcases family_descends (prefixWord ++ tailWord_414195) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414248 : List Nat := [2, 1, 5, 2, 1, 1, 4, 1, 2, 3]
def baseStart_414248 : Nat := 118140960795 + 414248 * 2 ^ 59
def prefixEnd_414248 : Nat := 4983230072969 + 3 ^ 40 * 414248 * 2
def baseEnd_414248 : Nat := 141805556109200324329943

theorem tailTrace_414248 : CollatzResearch.WordTrace tailWord_414248 prefixEnd_414248 141805556109200324329943 := by
  unfold tailWord_414248
  simp only [CollatzResearch.WordTrace]
  refine ⟨7554432901628859385489699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10072577202171812513986265 7554432901628859385489699)
  ·
    refine ⟨11331649352443289078234549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7554432901628859385489699 11331649352443289078234549)
    ·
      refine ⟨1062342126791558351084489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11331649352443289078234549 1062342126791558351084489)
      ·
        refine ⟨796756595093668763313367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1062342126791558351084489 796756595093668763313367)
        ·
          refine ⟨1195134892640503144970051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 796756595093668763313367 1195134892640503144970051)
          ·
            refine ⟨1792702338960754717455077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195134892640503144970051 1792702338960754717455077)
            ·
              refine ⟨336131688555141509522827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1792702338960754717455077 336131688555141509522827)
              ·
                refine ⟨504197532832712264284241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336131688555141509522827 504197532832712264284241)
                ·
                  refine ⟨378148149624534198213181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504197532832712264284241 378148149624534198213181)
                  ·
                    refine ⟨141805556109200324329943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378148149624534198213181 141805556109200324329943)
                    ·
                      rfl

theorem cell22_414248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 1, 2, 3].length) (baseStart_414248 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414248 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414248 prefixEnd_414248 := by exact prefixLift 414248
  have htrace : WordTrace (prefixWord ++ tailWord_414248) baseStart_414248 baseEnd_414248 := by
    simpa [prefixWord, tailWord_414248, baseEnd_414248] using wordTrace_append hprefix tailTrace_414248
  have hstable : (prefixWord ++ tailWord_414248).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414248).length < 2 ^ (prefixWord ++ tailWord_414248).sum := by decide
  have hdescent : baseEnd_414248 < baseStart_414248 := by decide
  rcases family_descends (prefixWord ++ tailWord_414248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414289 : List Nat := [1, 2, 2, 1, 3, 4, 2, 2, 5]
def baseStart_414289 : Nat := 118140960795 + 414289 * 2 ^ 59
def prefixEnd_414289 : Nat := 4983230072969 + 3 ^ 40 * 414289 * 2
def baseEnd_414289 : Nat := 47273197082363294684939

theorem tailTrace_414289 : CollatzResearch.WordTrace tailWord_414289 prefixEnd_414289 47273197082363294684939 := by
  unfold tailWord_414289
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110361196109182773221921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10073574130739455182147947 15110361196109182773221921)
  ·
    refine ⟨11332770897081887079916441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15110361196109182773221921 11332770897081887079916441)
    ·
      refine ⟨8499578172811415309937331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11332770897081887079916441 8499578172811415309937331)
      ·
        refine ⟨12749367259217122964905997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8499578172811415309937331 12749367259217122964905997)
        ·
          refine ⟨4781012722206421111839749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12749367259217122964905997 4781012722206421111839749)
          ·
            refine ⟨896439885413703958469953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4781012722206421111839749 896439885413703958469953)
            ·
              refine ⟨672329914060277968852465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896439885413703958469953 672329914060277968852465)
              ·
                refine ⟨504247435545208476639349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672329914060277968852465 504247435545208476639349)
                ·
                  refine ⟨47273197082363294684939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 504247435545208476639349 47273197082363294684939)
                  ·
                    rfl

theorem cell22_414289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 2, 2, 5].length) (baseStart_414289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414289 prefixEnd_414289 := by exact prefixLift 414289
  have htrace : WordTrace (prefixWord ++ tailWord_414289) baseStart_414289 baseEnd_414289 := by
    simpa [prefixWord, tailWord_414289, baseEnd_414289] using wordTrace_append hprefix tailTrace_414289
  have hstable : (prefixWord ++ tailWord_414289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414289).length < 2 ^ (prefixWord ++ tailWord_414289).sum := by decide
  have hdescent : baseEnd_414289 < baseStart_414289 := by decide
  rcases family_descends (prefixWord ++ tailWord_414289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414293 : List Nat := [1, 3, 2, 2, 1, 1, 6, 2, 1, 3]
def baseStart_414293 : Nat := 118140960795 + 414293 * 2 ^ 59
def prefixEnd_414293 : Nat := 4983230072969 + 3 ^ 40 * 414293 * 2
def baseEnd_414293 : Nat := 141820960528835206954805

theorem tailTrace_414293 : CollatzResearch.WordTrace tailWord_414293 prefixEnd_414293 141820960528835206954805 := by
  unfold tailWord_414293
  simp only [CollatzResearch.WordTrace]
  refine ⟨15110507088094691456367533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10073671392063127637578355 15110507088094691456367533)
  ·
    refine ⟨5666440158035509296137825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15110507088094691456367533 5666440158035509296137825)
    ·
      refine ⟨4249830118526631972103369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5666440158035509296137825 4249830118526631972103369)
      ·
        refine ⟨3187372588894973979077527, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4249830118526631972103369 3187372588894973979077527)
        ·
          refine ⟨4781058883342460968616291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3187372588894973979077527 4781058883342460968616291)
          ·
            refine ⟨7171588325013691452924437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4781058883342460968616291 7171588325013691452924437)
            ·
              refine ⟨336168202735016786855833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 7171588325013691452924437 336168202735016786855833)
              ·
                refine ⟨252126152051262590141875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336168202735016786855833 252126152051262590141875)
                ·
                  refine ⟨378189228076893885212813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252126152051262590141875 378189228076893885212813)
                  ·
                    refine ⟨141820960528835206954805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378189228076893885212813 141820960528835206954805)
                    ·
                      rfl

theorem cell22_414293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_414293 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414293 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414293 prefixEnd_414293 := by exact prefixLift 414293
  have htrace : WordTrace (prefixWord ++ tailWord_414293) baseStart_414293 baseEnd_414293 := by
    simpa [prefixWord, tailWord_414293, baseEnd_414293] using wordTrace_append hprefix tailTrace_414293
  have hstable : (prefixWord ++ tailWord_414293).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414293).length < 2 ^ (prefixWord ++ tailWord_414293).sum := by decide
  have hdescent : baseEnd_414293 < baseStart_414293 := by decide
  rcases family_descends (prefixWord ++ tailWord_414293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414336 : List Nat := [2, 1, 1, 2, 1, 5, 4, 1, 1, 4]
def baseStart_414336 : Nat := 118140960795 + 414336 * 2 ^ 59
def prefixEnd_414336 : Nat := 4983230072969 + 3 ^ 40 * 414336 * 2
def baseEnd_414336 : Nat := 141835680307597428129673

theorem tailTrace_414336 : CollatzResearch.WordTrace tailWord_414336 prefixEnd_414336 141835680307597428129673 := by
  unfold tailWord_414336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7556037713469454900091431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10074716951292606533455241 7556037713469454900091431)
  ·
    refine ⟨11334056570204182350137147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7556037713469454900091431 11334056570204182350137147)
    ·
      refine ⟨17001084855306273525205721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11334056570204182350137147 17001084855306273525205721)
      ·
        refine ⟨12750813641479705143904291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17001084855306273525205721 12750813641479705143904291)
        ·
          refine ⟨19126220462219557715856437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12750813641479705143904291 19126220462219557715856437)
          ·
            refine ⟨1793083168333083535861541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19126220462219557715856437 1793083168333083535861541)
            ·
              refine ⟨336203094062453162974039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1793083168333083535861541 336203094062453162974039)
              ·
                refine ⟨504304641093679744461059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 336203094062453162974039 504304641093679744461059)
                ·
                  refine ⟨756456961640519616691589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 504304641093679744461059 756456961640519616691589)
                  ·
                    refine ⟨141835680307597428129673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756456961640519616691589 141835680307597428129673)
                    ·
                      rfl

theorem cell22_414336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 5, 4, 1, 1, 4].length) (baseStart_414336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414336 prefixEnd_414336 := by exact prefixLift 414336
  have htrace : WordTrace (prefixWord ++ tailWord_414336) baseStart_414336 baseEnd_414336 := by
    simpa [prefixWord, tailWord_414336, baseEnd_414336] using wordTrace_append hprefix tailTrace_414336
  have hstable : (prefixWord ++ tailWord_414336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414336).length < 2 ^ (prefixWord ++ tailWord_414336).sum := by decide
  have hdescent : baseEnd_414336 < baseStart_414336 := by decide
  rcases family_descends (prefixWord ++ tailWord_414336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414364 : List Nat := [2, 2, 3, 2, 2, 1, 1, 2, 1, 6]
def baseStart_414364 : Nat := 118140960795 + 414364 * 2 ^ 59
def prefixEnd_414364 : Nat := 4983230072969 + 3 ^ 40 * 414364 * 2
def baseEnd_414364 : Nat := 141845265279814688429587

theorem tailTrace_414364 : CollatzResearch.WordTrace tailWord_414364 prefixEnd_414364 141845265279814688429587 := by
  unfold tailWord_414364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7556548335418735291101073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10075397780558313721468097 7556548335418735291101073)
  ·
    refine ⟨5667411251564051468325805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7556548335418735291101073 5667411251564051468325805)
    ·
      refine ⟨2125279219336519300622177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5667411251564051468325805 2125279219336519300622177)
      ·
        refine ⟨1593959414502389475466633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2125279219336519300622177 1593959414502389475466633)
        ·
          refine ⟨1195469560876792106599975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1593959414502389475466633 1195469560876792106599975)
          ·
            refine ⟨1793204341315188159899963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195469560876792106599975 1793204341315188159899963)
            ·
              refine ⟨2689806511972782239849945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793204341315188159899963 2689806511972782239849945)
              ·
                refine ⟨2017354883979586679887459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2689806511972782239849945 2017354883979586679887459)
                ·
                  refine ⟨3026032325969380019831189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2017354883979586679887459 3026032325969380019831189)
                  ·
                    refine ⟨141845265279814688429587, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3026032325969380019831189 141845265279814688429587)
                    ·
                      rfl

theorem cell22_414364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 1, 2, 1, 6].length) (baseStart_414364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414364 prefixEnd_414364 := by exact prefixLift 414364
  have htrace : WordTrace (prefixWord ++ tailWord_414364) baseStart_414364 baseEnd_414364 := by
    simpa [prefixWord, tailWord_414364, baseEnd_414364] using wordTrace_append hprefix tailTrace_414364
  have hstable : (prefixWord ++ tailWord_414364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414364).length < 2 ^ (prefixWord ++ tailWord_414364).sum := by decide
  have hdescent : baseEnd_414364 < baseStart_414364 := by decide
  rcases family_descends (prefixWord ++ tailWord_414364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414385 : List Nat := [1, 2, 2, 6, 1, 2, 1, 3, 4]
def baseStart_414385 : Nat := 118140960795 + 414385 * 2 ^ 59
def prefixEnd_414385 : Nat := 4983230072969 + 3 ^ 40 * 414385 * 2
def baseEnd_414385 : Nat := 47284151336325877884841

theorem tailTrace_414385 : CollatzResearch.WordTrace tailWord_414385 prefixEnd_414385 47284151336325877884841 := by
  unfold tailWord_414385
  simp only [CollatzResearch.WordTrace]
  refine ⟨15113862603761391168716609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10075908402507594112477739 15113862603761391168716609)
  ·
    refine ⟨11335396952821043376537457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15113862603761391168716609 11335396952821043376537457)
    ·
      refine ⟨8501547714615782532403093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11335396952821043376537457 8501547714615782532403093)
      ·
        refine ⟨398510049122614806206395, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8501547714615782532403093 398510049122614806206395)
        ·
          refine ⟨597765073683922209309593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398510049122614806206395 597765073683922209309593)
          ·
            refine ⟨448323805262941656982195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 597765073683922209309593 448323805262941656982195)
            ·
              refine ⟨672485707894412485473293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448323805262941656982195 672485707894412485473293)
              ·
                refine ⟨252182140460404682052485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 672485707894412485473293 252182140460404682052485)
                ·
                  refine ⟨47284151336325877884841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252182140460404682052485 47284151336325877884841)
                  ·
                    rfl

theorem cell22_414385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 2, 1, 3, 4].length) (baseStart_414385 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414385 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414385 prefixEnd_414385 := by exact prefixLift 414385
  have htrace : WordTrace (prefixWord ++ tailWord_414385) baseStart_414385 baseEnd_414385 := by
    simpa [prefixWord, tailWord_414385, baseEnd_414385] using wordTrace_append hprefix tailTrace_414385
  have hstable : (prefixWord ++ tailWord_414385).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414385).length < 2 ^ (prefixWord ++ tailWord_414385).sum := by decide
  have hdescent : baseEnd_414385 < baseStart_414385 := by decide
  rcases family_descends (prefixWord ++ tailWord_414385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414392 : List Nat := [2, 1, 2, 1, 2, 1, 1, 1, 3, 8]
def baseStart_414392 : Nat := 118140960795 + 414392 * 2 ^ 59
def prefixEnd_414392 : Nat := 4983230072969 + 3 ^ 40 * 414392 * 2
def baseEnd_414392 : Nat := 141854850252031948729501

theorem tailTrace_414392 : CollatzResearch.WordTrace tailWord_414392 prefixEnd_414392 141854850252031948729501 := by
  unfold tailWord_414392
  simp only [CollatzResearch.WordTrace]
  refine ⟨7557058957368015682110715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10076078609824020909480953 7557058957368015682110715)
  ·
    refine ⟨11335588436052023523166073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7557058957368015682110715 11335588436052023523166073)
    ·
      refine ⟨8501691327039017642374555, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11335588436052023523166073 8501691327039017642374555)
      ·
        refine ⟨12752536990558526463561833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8501691327039017642374555 12752536990558526463561833)
        ·
          refine ⟨9564402742918894847671375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12752536990558526463561833 9564402742918894847671375)
          ·
            refine ⟨14346604114378342271507063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9564402742918894847671375 14346604114378342271507063)
            ·
              refine ⟨21519906171567513407260595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14346604114378342271507063 21519906171567513407260595)
              ·
                refine ⟨32279859257351270110890893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21519906171567513407260595 32279859257351270110890893)
                ·
                  refine ⟨12104947221506726291584085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32279859257351270110890893 12104947221506726291584085)
                  ·
                    refine ⟨141854850252031948729501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12104947221506726291584085 141854850252031948729501)
                    ·
                      rfl

theorem cell22_414392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 1, 1, 3, 8].length) (baseStart_414392 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414392 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414392 prefixEnd_414392 := by exact prefixLift 414392
  have htrace : WordTrace (prefixWord ++ tailWord_414392) baseStart_414392 baseEnd_414392 := by
    simpa [prefixWord, tailWord_414392, baseEnd_414392] using wordTrace_append hprefix tailTrace_414392
  have hstable : (prefixWord ++ tailWord_414392).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414392).length < 2 ^ (prefixWord ++ tailWord_414392).sum := by decide
  have hdescent : baseEnd_414392 < baseStart_414392 := by decide
  rcases family_descends (prefixWord ++ tailWord_414392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414413 : List Nat := [1, 6, 2, 1, 2, 1, 2, 7]
def baseStart_414413 : Nat := 118140960795 + 414413 * 2 ^ 59
def prefixEnd_414413 : Nat := 4983230072969 + 3 ^ 40 * 414413 * 2
def baseEnd_414413 : Nat := 15762448775688321550493

theorem tailTrace_414413 : CollatzResearch.WordTrace tailWord_414413 prefixEnd_414413 15762448775688321550493 := by
  unfold tailWord_414413
  simp only [CollatzResearch.WordTrace]
  refine ⟨15114883847659951950735893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10076589231773301300490595 15114883847659951950735893)
  ·
    refine ⟨708510180359060247690745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15114883847659951950735893 708510180359060247690745)
    ·
      refine ⟨531382635269295185768059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 708510180359060247690745 531382635269295185768059)
      ·
        refine ⟨797073952903942778652089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 531382635269295185768059 797073952903942778652089)
        ·
          refine ⟨597805464677957083989067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 797073952903942778652089 597805464677957083989067)
          ·
            refine ⟨896708197016935625983601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 597805464677957083989067 896708197016935625983601)
            ·
              refine ⟨672531147762701719487701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 896708197016935625983601 672531147762701719487701)
              ·
                refine ⟨15762448775688321550493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 672531147762701719487701 15762448775688321550493)
                ·
                  rfl

theorem cell22_414413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 2, 1, 2, 7].length) (baseStart_414413 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414413 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414413 prefixEnd_414413 := by exact prefixLift 414413
  have htrace : WordTrace (prefixWord ++ tailWord_414413) baseStart_414413 baseEnd_414413 := by
    simpa [prefixWord, tailWord_414413, baseEnd_414413] using wordTrace_append hprefix tailTrace_414413
  have hstable : (prefixWord ++ tailWord_414413).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414413).length < 2 ^ (prefixWord ++ tailWord_414413).sum := by decide
  have hdescent : baseEnd_414413 < baseStart_414413 := by decide
  rcases family_descends (prefixWord ++ tailWord_414413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414462 : List Nat := [4, 2, 2, 1, 2, 1, 4, 2, 1, 3]
def baseStart_414462 : Nat := 118140960795 + 414462 * 2 ^ 59
def prefixEnd_414462 : Nat := 4983230072969 + 3 ^ 40 * 414462 * 2
def baseEnd_414462 : Nat := 141878812682575099479287

theorem tailTrace_414462 : CollatzResearch.WordTrace tailWord_414462 prefixEnd_414462 141878812682575099479287 := by
  unfold tailWord_414462
  simp only [CollatzResearch.WordTrace]
  refine ⟨1889583878060304164908705, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10077780682988288879513093 1889583878060304164908705)
  ·
    refine ⟨1417187908545228123681529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1889583878060304164908705 1417187908545228123681529)
    ·
      refine ⟨1062890931408921092761147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1417187908545228123681529 1062890931408921092761147)
      ·
        refine ⟨1594336397113381639141721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1062890931408921092761147 1594336397113381639141721)
        ·
          refine ⟨1195752297835036229356291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1594336397113381639141721 1195752297835036229356291)
          ·
            refine ⟨1793628446752554344034437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195752297835036229356291 1793628446752554344034437)
            ·
              refine ⟨336305333766103939506457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1793628446752554344034437 336305333766103939506457)
              ·
                refine ⟨252229000324577954629843, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336305333766103939506457 252229000324577954629843)
                ·
                  refine ⟨378343500486866931944765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252229000324577954629843 378343500486866931944765)
                  ·
                    refine ⟨141878812682575099479287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378343500486866931944765 141878812682575099479287)
                    ·
                      rfl

theorem cell22_414462_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 2, 1, 3].length) (baseStart_414462 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414462 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414462 prefixEnd_414462 := by exact prefixLift 414462
  have htrace : WordTrace (prefixWord ++ tailWord_414462) baseStart_414462 baseEnd_414462 := by
    simpa [prefixWord, tailWord_414462, baseEnd_414462] using wordTrace_append hprefix tailTrace_414462
  have hstable : (prefixWord ++ tailWord_414462).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414462).length < 2 ^ (prefixWord ++ tailWord_414462).sum := by decide
  have hdescent : baseEnd_414462 < baseStart_414462 := by decide
  rcases family_descends (prefixWord ++ tailWord_414462) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414471 : List Nat := [1, 1, 4, 4, 1, 1, 1, 2, 3, 4]
def baseStart_414471 : Nat := 118140960795 + 414471 * 2 ^ 59
def prefixEnd_414471 : Nat := 4983230072969 + 3 ^ 40 * 414471 * 2
def baseEnd_414471 : Nat := 141881893566502076004259

theorem tailTrace_414471 : CollatzResearch.WordTrace tailWord_414471 prefixEnd_414471 141881893566502076004259 := by
  unfold tailWord_414471
  simp only [CollatzResearch.WordTrace]
  refine ⟨15116999281449827856347267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10077999520966551904231511 15116999281449827856347267)
  ·
    refine ⟨22675498922174741784520901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15116999281449827856347267 22675498922174741784520901)
    ·
      refine ⟨4251656047907764084597669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22675498922174741784520901 4251656047907764084597669)
      ·
        refine ⟨797185508982705765862063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4251656047907764084597669 797185508982705765862063)
        ·
          refine ⟨1195778263474058648793095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 797185508982705765862063 1195778263474058648793095)
          ·
            refine ⟨1793667395211087973189643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1195778263474058648793095 1793667395211087973189643)
            ·
              refine ⟨2690501092816631959784465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1793667395211087973189643 2690501092816631959784465)
              ·
                refine ⟨2017875819612473969838349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690501092816631959784465 2017875819612473969838349)
                ·
                  refine ⟨756703432354677738689381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2017875819612473969838349 756703432354677738689381)
                  ·
                    refine ⟨141881893566502076004259, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 756703432354677738689381 141881893566502076004259)
                    ·
                      rfl

theorem cell22_414471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 2, 3, 4].length) (baseStart_414471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414471 prefixEnd_414471 := by exact prefixLift 414471
  have htrace : WordTrace (prefixWord ++ tailWord_414471) baseStart_414471 baseEnd_414471 := by
    simpa [prefixWord, tailWord_414471, baseEnd_414471] using wordTrace_append hprefix tailTrace_414471
  have hstable : (prefixWord ++ tailWord_414471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414471).length < 2 ^ (prefixWord ++ tailWord_414471).sum := by decide
  have hdescent : baseEnd_414471 < baseStart_414471 := by decide
  rcases family_descends (prefixWord ++ tailWord_414471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414501 : List Nat := [1, 3, 1, 2, 3, 1, 2, 2, 4, 3]
def baseStart_414501 : Nat := 118140960795 + 414501 * 2 ^ 59
def prefixEnd_414501 : Nat := 4983230072969 + 3 ^ 40 * 414501 * 2
def baseEnd_414501 : Nat := 141892163179591997754167

theorem tailTrace_414501 : CollatzResearch.WordTrace tailWord_414501 prefixEnd_414501 141892163179591997754167 := by
  unfold tailWord_414501
  simp only [CollatzResearch.WordTrace]
  refine ⟨15118093471341142979939357, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10078728980894095319959571 15118093471341142979939357)
  ·
    refine ⟨5669285051752928617477259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15118093471341142979939357 5669285051752928617477259)
    ·
      refine ⟨8503927577629392926215889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5669285051752928617477259 8503927577629392926215889)
      ·
        refine ⟨6377945683222044694661917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8503927577629392926215889 6377945683222044694661917)
        ·
          refine ⟨2391729631208266760498219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6377945683222044694661917 2391729631208266760498219)
          ·
            refine ⟨3587594446812400140747329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391729631208266760498219 3587594446812400140747329)
            ·
              refine ⟨2690695835109300105560497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3587594446812400140747329 2690695835109300105560497)
              ·
                refine ⟨2018021876331975079170373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2690695835109300105560497 2018021876331975079170373)
                ·
                  refine ⟨378379101812245327344445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2018021876331975079170373 378379101812245327344445)
                  ·
                    refine ⟨141892163179591997754167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378379101812245327344445 141892163179591997754167)
                    ·
                      rfl

theorem cell22_414501_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 2, 2, 4, 3].length) (baseStart_414501 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414501 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414501 prefixEnd_414501 := by exact prefixLift 414501
  have htrace : WordTrace (prefixWord ++ tailWord_414501) baseStart_414501 baseEnd_414501 := by
    simpa [prefixWord, tailWord_414501, baseEnd_414501] using wordTrace_append hprefix tailTrace_414501
  have hstable : (prefixWord ++ tailWord_414501).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414501).length < 2 ^ (prefixWord ++ tailWord_414501).sum := by decide
  have hdescent : baseEnd_414501 < baseStart_414501 := by decide
  rcases family_descends (prefixWord ++ tailWord_414501) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414514 : List Nat := [3, 2, 1, 1, 3, 1, 11]
def baseStart_414514 : Nat := 118140960795 + 414514 * 2 ^ 59
def prefixEnd_414514 : Nat := 4983230072969 + 3 ^ 40 * 414514 * 2
def baseEnd_414514 : Nat := 5255430123898677673301

theorem tailTrace_414514 : CollatzResearch.WordTrace tailWord_414514 prefixEnd_414514 5255430123898677673301 := by
  unfold tailWord_414514
  simp only [CollatzResearch.WordTrace]
  refine ⟨3779641905073511550040649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10079045080196030800108397 3779641905073511550040649)
  ·
    refine ⟨2834731428805133662530487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3779641905073511550040649 2834731428805133662530487)
    ·
      refine ⟨4252097143207700493795731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2834731428805133662530487 4252097143207700493795731)
      ·
        refine ⟨6378145714811550740693597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4252097143207700493795731 6378145714811550740693597)
        ·
          refine ⟨2391804643054331527760099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6378145714811550740693597 2391804643054331527760099)
          ·
            refine ⟨3587706964581497291640149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2391804643054331527760099 3587706964581497291640149)
            ·
              refine ⟨5255430123898677673301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 3587706964581497291640149 5255430123898677673301)
              ·
                rfl

theorem cell22_414514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 1, 11].length) (baseStart_414514 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414514 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414514 prefixEnd_414514 := by exact prefixLift 414514
  have htrace : WordTrace (prefixWord ++ tailWord_414514) baseStart_414514 baseEnd_414514 := by
    simpa [prefixWord, tailWord_414514, baseEnd_414514] using wordTrace_append hprefix tailTrace_414514
  have hstable : (prefixWord ++ tailWord_414514).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414514).length < 2 ^ (prefixWord ++ tailWord_414514).sum := by decide
  have hdescent : baseEnd_414514 < baseStart_414514 := by decide
  rcases family_descends (prefixWord ++ tailWord_414514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414544 : List Nat := [2, 1, 1, 1, 1, 4, 2, 2, 2, 6]
def baseStart_414544 : Nat := 118140960795 + 414544 * 2 ^ 59
def prefixEnd_414544 : Nat := 4983230072969 + 3 ^ 40 * 414544 * 2
def baseEnd_414544 : Nat := 141906882958354218929035

theorem tailTrace_414544 : CollatzResearch.WordTrace tailWord_414544 prefixEnd_414544 141906882958354218929035 := by
  unfold tailWord_414544
  simp only [CollatzResearch.WordTrace]
  refine ⟨7559830905092680661877343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10079774540123574215836457 7559830905092680661877343)
  ·
    refine ⟨11339746357639020992816015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7559830905092680661877343 11339746357639020992816015)
    ·
      refine ⟨17009619536458531489224023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11339746357639020992816015 17009619536458531489224023)
      ·
        refine ⟨25514429304687797233836035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17009619536458531489224023 25514429304687797233836035)
        ·
          refine ⟨38271643957031695850754053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25514429304687797233836035 38271643957031695850754053)
          ·
            refine ⟨7175933241943442972016385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38271643957031695850754053 7175933241943442972016385)
            ·
              refine ⟨5381949931457582229012289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7175933241943442972016385 5381949931457582229012289)
              ·
                refine ⟨4036462448593186671759217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5381949931457582229012289 4036462448593186671759217)
                ·
                  refine ⟨3027346836444890003819413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4036462448593186671759217 3027346836444890003819413)
                  ·
                    refine ⟨141906882958354218929035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3027346836444890003819413 141906882958354218929035)
                    ·
                      rfl

theorem cell22_414544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 2, 2, 6].length) (baseStart_414544 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414544 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414544 prefixEnd_414544 := by exact prefixLift 414544
  have htrace : WordTrace (prefixWord ++ tailWord_414544) baseStart_414544 baseEnd_414544 := by
    simpa [prefixWord, tailWord_414544, baseEnd_414544] using wordTrace_append hprefix tailTrace_414544
  have hstable : (prefixWord ++ tailWord_414544).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414544).length < 2 ^ (prefixWord ++ tailWord_414544).sum := by decide
  have hdescent : baseEnd_414544 < baseStart_414544 := by decide
  rcases family_descends (prefixWord ++ tailWord_414544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414559 : List Nat := [1, 1, 2, 3, 1, 3, 1, 1, 9]
def baseStart_414559 : Nat := 118140960795 + 414559 * 2 ^ 59
def prefixEnd_414559 : Nat := 4983230072969 + 3 ^ 40 * 414559 * 2
def baseEnd_414559 : Nat := 47304005921633059934663

theorem tailTrace_414559 : CollatzResearch.WordTrace tailWord_414559 prefixEnd_414559 47304005921633059934663 := by
  unfold tailWord_414559
  simp only [CollatzResearch.WordTrace]
  refine ⟨15120208905131018885550731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10080139270087345923700487 15120208905131018885550731)
  ·
    refine ⟨22680313357696528328326097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15120208905131018885550731 22680313357696528328326097)
    ·
      refine ⟨17010235018272396246244573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22680313357696528328326097 17010235018272396246244573)
      ·
        refine ⟨6378838131852148592341715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17010235018272396246244573 6378838131852148592341715)
        ·
          refine ⟨9568257197778222888512573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6378838131852148592341715 9568257197778222888512573)
          ·
            refine ⟨3588096449166833583192215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9568257197778222888512573 3588096449166833583192215)
            ·
              refine ⟨5382144673750250374788323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3588096449166833583192215 5382144673750250374788323)
              ·
                refine ⟨8073217010625375562182485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5382144673750250374788323 8073217010625375562182485)
                ·
                  refine ⟨47304005921633059934663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8073217010625375562182485 47304005921633059934663)
                  ·
                    rfl

theorem cell22_414559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 1, 9].length) (baseStart_414559 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414559 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414559 prefixEnd_414559 := by exact prefixLift 414559
  have htrace : WordTrace (prefixWord ++ tailWord_414559) baseStart_414559 baseEnd_414559 := by
    simpa [prefixWord, tailWord_414559, baseEnd_414559] using wordTrace_append hprefix tailTrace_414559
  have hstable : (prefixWord ++ tailWord_414559).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414559).length < 2 ^ (prefixWord ++ tailWord_414559).sum := by decide
  have hdescent : baseEnd_414559 < baseStart_414559 := by decide
  rcases family_descends (prefixWord ++ tailWord_414559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414631 : List Nat := [1, 1, 6, 1, 4, 1, 2, 2, 1, 3]
def baseStart_414631 : Nat := 118140960795 + 414631 * 2 ^ 59
def prefixEnd_414631 : Nat := 4983230072969 + 3 ^ 40 * 414631 * 2
def baseEnd_414631 : Nat := 141936664836314992003769

theorem tailTrace_414631 : CollatzResearch.WordTrace tailWord_414631 prefixEnd_414631 141936664836314992003769 := by
  unfold tailWord_414631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15122834960870175182171747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10081889973913450121447831 15122834960870175182171747)
  ·
    refine ⟨22684252441305262773257621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15122834960870175182171747 22684252441305262773257621)
    ·
      refine ⟨1063324333186184192496451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 22684252441305262773257621 1063324333186184192496451)
      ·
        refine ⟨1594986499779276288744677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1063324333186184192496451 1594986499779276288744677)
        ·
          refine ⟨299059968708614304139627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1594986499779276288744677 299059968708614304139627)
          ·
            refine ⟨448589953062921456209441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299059968708614304139627 448589953062921456209441)
            ·
              refine ⟨336442464797191092157081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 448589953062921456209441 336442464797191092157081)
              ·
                refine ⟨252331848597893319117811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 336442464797191092157081 252331848597893319117811)
                ·
                  refine ⟨378497772896839978676717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252331848597893319117811 378497772896839978676717)
                  ·
                    refine ⟨141936664836314992003769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378497772896839978676717 141936664836314992003769)
                    ·
                      rfl

theorem cell22_414631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 2, 1, 3].length) (baseStart_414631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414631 prefixEnd_414631 := by exact prefixLift 414631
  have htrace : WordTrace (prefixWord ++ tailWord_414631) baseStart_414631 baseEnd_414631 := by
    simpa [prefixWord, tailWord_414631, baseEnd_414631] using wordTrace_append hprefix tailTrace_414631
  have hstable : (prefixWord ++ tailWord_414631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414631).length < 2 ^ (prefixWord ++ tailWord_414631).sum := by decide
  have hdescent : baseEnd_414631 < baseStart_414631 := by decide
  rcases family_descends (prefixWord ++ tailWord_414631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414687 : List Nat := [1, 1, 2, 3, 5, 2, 1, 2, 2, 3]
def baseStart_414687 : Nat := 118140960795 + 414687 * 2 ^ 59
def prefixEnd_414687 : Nat := 4983230072969 + 3 ^ 40 * 414687 * 2
def baseEnd_414687 : Nat := 141955834780749512603597

theorem tailTrace_414687 : CollatzResearch.WordTrace tailWord_414687 prefixEnd_414687 141955834780749512603597 := by
  unfold tailWord_414687
  simp only [CollatzResearch.WordTrace]
  refine ⟨15124877448667296746210315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10083251632444864497473543 15124877448667296746210315)
  ·
    refine ⟨22687316173000945119315473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15124877448667296746210315 22687316173000945119315473)
    ·
      refine ⟨17015487129750708839486605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22687316173000945119315473 17015487129750708839486605)
      ·
        refine ⟨6380807673656515814807477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17015487129750708839486605 6380807673656515814807477)
        ·
          refine ⟨598200719405298357638201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6380807673656515814807477 598200719405298357638201)
          ·
            refine ⟨448650539553973768228651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 598200719405298357638201 448650539553973768228651)
            ·
              refine ⟨672975809330960652342977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448650539553973768228651 672975809330960652342977)
              ·
                refine ⟨504731856998220489257233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 672975809330960652342977 504731856998220489257233)
                ·
                  refine ⟨378548892748665366942925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504731856998220489257233 378548892748665366942925)
                  ·
                    refine ⟨141955834780749512603597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378548892748665366942925 141955834780749512603597)
                    ·
                      rfl

theorem cell22_414687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 2, 2, 3].length) (baseStart_414687 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414687 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414687 prefixEnd_414687 := by exact prefixLift 414687
  have htrace : WordTrace (prefixWord ++ tailWord_414687) baseStart_414687 baseEnd_414687 := by
    simpa [prefixWord, tailWord_414687, baseEnd_414687] using wordTrace_append hprefix tailTrace_414687
  have hstable : (prefixWord ++ tailWord_414687).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414687).length < 2 ^ (prefixWord ++ tailWord_414687).sum := by decide
  have hdescent : baseEnd_414687 < baseStart_414687 := by decide
  rcases family_descends (prefixWord ++ tailWord_414687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414696 : List Nat := [2, 1, 4, 1, 1, 1, 2, 1, 1, 8]
def baseStart_414696 : Nat := 118140960795 + 414696 * 2 ^ 59
def prefixEnd_414696 : Nat := 4983230072969 + 3 ^ 40 * 414696 * 2
def baseEnd_414696 : Nat := 141958915664676489128569

theorem tailTrace_414696 : CollatzResearch.WordTrace tailWord_414696 prefixEnd_414696 141958915664676489128569 := by
  unfold tailWord_414696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7562602852817345641643971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10083470470423127522191961 7562602852817345641643971)
  ·
    refine ⟨11343904279226018462465957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7562602852817345641643971 11343904279226018462465957)
    ·
      refine ⟨2126982052354878461712367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11343904279226018462465957 2126982052354878461712367)
      ·
        refine ⟨3190473078532317692568551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2126982052354878461712367 3190473078532317692568551)
        ·
          refine ⟨4785709617798476538852827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3190473078532317692568551 4785709617798476538852827)
          ·
            refine ⟨7178564426697714808279241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4785709617798476538852827 7178564426697714808279241)
            ·
              refine ⟨5383923320023286106209431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7178564426697714808279241 5383923320023286106209431)
              ·
                refine ⟨8075884980034929159314147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5383923320023286106209431 8075884980034929159314147)
                ·
                  refine ⟨12113827470052393738971221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8075884980034929159314147 12113827470052393738971221)
                  ·
                    refine ⟨141958915664676489128569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12113827470052393738971221 141958915664676489128569)
                    ·
                      rfl

theorem cell22_414696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 1, 2, 1, 1, 8].length) (baseStart_414696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414696 prefixEnd_414696 := by exact prefixLift 414696
  have htrace : WordTrace (prefixWord ++ tailWord_414696) baseStart_414696 baseEnd_414696 := by
    simpa [prefixWord, tailWord_414696, baseEnd_414696] using wordTrace_append hprefix tailTrace_414696
  have hstable : (prefixWord ++ tailWord_414696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414696).length < 2 ^ (prefixWord ++ tailWord_414696).sum := by decide
  have hdescent : baseEnd_414696 < baseStart_414696 := by decide
  rcases family_descends (prefixWord ++ tailWord_414696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414732 : List Nat := [2, 2, 1, 2, 3, 2, 3, 3, 1, 3]
def baseStart_414732 : Nat := 118140960795 + 414732 * 2 ^ 59
def prefixEnd_414732 : Nat := 4983230072969 + 3 ^ 40 * 414732 * 2
def baseEnd_414732 : Nat := 141971239200384395228459

theorem tailTrace_414732 : CollatzResearch.WordTrace tailWord_414732 prefixEnd_414732 141971239200384395228459 := by
  unfold tailWord_414732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7563259366752134715799225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10084345822336179621065633 7563259366752134715799225)
  ·
    refine ⟨5672444525064101036849419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7563259366752134715799225 5672444525064101036849419)
    ·
      refine ⟨8508666787596151555274129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5672444525064101036849419 8508666787596151555274129)
      ·
        refine ⟨6381500090697113666455597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8508666787596151555274129 6381500090697113666455597)
        ·
          refine ⟨2393062534011417624920849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6381500090697113666455597 2393062534011417624920849)
          ·
            refine ⟨1794796900508563218690637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2393062534011417624920849 1794796900508563218690637)
            ·
              refine ⟨673048837690711207008989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1794796900508563218690637 673048837690711207008989)
              ·
                refine ⟨252393314134016702628371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 673048837690711207008989 252393314134016702628371)
                ·
                  refine ⟨378589971201025053942557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252393314134016702628371 378589971201025053942557)
                  ·
                    refine ⟨141971239200384395228459, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378589971201025053942557 141971239200384395228459)
                    ·
                      rfl

theorem cell22_414732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 3, 1, 3].length) (baseStart_414732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414732 prefixEnd_414732 := by exact prefixLift 414732
  have htrace : WordTrace (prefixWord ++ tailWord_414732) baseStart_414732 baseEnd_414732 := by
    simpa [prefixWord, tailWord_414732, baseEnd_414732] using wordTrace_append hprefix tailTrace_414732
  have hstable : (prefixWord ++ tailWord_414732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414732).length < 2 ^ (prefixWord ++ tailWord_414732).sum := by decide
  have hdescent : baseEnd_414732 < baseStart_414732 := by decide
  rcases family_descends (prefixWord ++ tailWord_414732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414749 : List Nat := [1, 4, 2, 2, 4, 1, 1, 1, 3, 3]
def baseStart_414749 : Nat := 118140960795 + 414749 * 2 ^ 59
def prefixEnd_414749 : Nat := 4983230072969 + 3 ^ 40 * 414749 * 2
def baseEnd_414749 : Nat := 141977058647802017553407

theorem tailTrace_414749 : CollatzResearch.WordTrace tailWord_414749 prefixEnd_414749 141977058647802017553407 := by
  unfold tailWord_414749
  simp only [CollatzResearch.WordTrace]
  refine ⟨15127138774442681334967301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10084759182961787556644867 15127138774442681334967301)
  ·
    refine ⟨2836338520208002750306369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15127138774442681334967301 2836338520208002750306369)
    ·
      refine ⟨2127253890156002062729777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2836338520208002750306369 2127253890156002062729777)
      ·
        refine ⟨1595440417617001547047333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2127253890156002062729777 1595440417617001547047333)
        ·
          refine ⟨299145078303187790071375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1595440417617001547047333 299145078303187790071375)
          ·
            refine ⟨448717617454781685107063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299145078303187790071375 448717617454781685107063)
            ·
              refine ⟨673076426182172527660595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448717617454781685107063 673076426182172527660595)
              ·
                refine ⟨1009614639273258791490893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 673076426182172527660595 1009614639273258791490893)
                ·
                  refine ⟨378605489727472046809085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1009614639273258791490893 378605489727472046809085)
                  ·
                    refine ⟨141977058647802017553407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378605489727472046809085 141977058647802017553407)
                    ·
                      rfl

theorem cell22_414749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 4, 1, 1, 1, 3, 3].length) (baseStart_414749 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414749 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414749 prefixEnd_414749 := by exact prefixLift 414749
  have htrace : WordTrace (prefixWord ++ tailWord_414749) baseStart_414749 baseEnd_414749 := by
    simpa [prefixWord, tailWord_414749, baseEnd_414749] using wordTrace_append hprefix tailTrace_414749
  have hstable : (prefixWord ++ tailWord_414749).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414749).length < 2 ^ (prefixWord ++ tailWord_414749).sum := by decide
  have hdescent : baseEnd_414749 < baseStart_414749 := by decide
  rcases family_descends (prefixWord ++ tailWord_414749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414837 : List Nat := [1, 3, 4, 3, 1, 1, 1, 1, 1, 6]
def baseStart_414837 : Nat := 118140960795 + 414837 * 2 ^ 59
def prefixEnd_414837 : Nat := 4983230072969 + 3 ^ 40 * 414837 * 2
def baseEnd_414837 : Nat := 142007182846199121353137

theorem tailTrace_414837 : CollatzResearch.WordTrace tailWord_414837 prefixEnd_414837 142007182846199121353137 := by
  unfold tailWord_414837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15130348398123872364170765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10086898932082581576113843 15130348398123872364170765)
  ·
    refine ⟨5673880649296452136564037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15130348398123872364170765 5673880649296452136564037)
    ·
      refine ⟨1063852621743084775605757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5673880649296452136564037 1063852621743084775605757)
      ·
        refine ⟨398944733153656790852159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1063852621743084775605757 398944733153656790852159)
        ·
          refine ⟨598417099730485186278239, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 398944733153656790852159 598417099730485186278239)
          ·
            refine ⟨897625649595727779417359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 598417099730485186278239 897625649595727779417359)
            ·
              refine ⟨1346438474393591669126039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897625649595727779417359 1346438474393591669126039)
              ·
                refine ⟨2019657711590387503689059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1346438474393591669126039 2019657711590387503689059)
                ·
                  refine ⟨3029486567385581255533589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2019657711590387503689059 3029486567385581255533589)
                  ·
                    refine ⟨142007182846199121353137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3029486567385581255533589 142007182846199121353137)
                    ·
                      rfl

theorem cell22_414837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 6].length) (baseStart_414837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414837 prefixEnd_414837 := by exact prefixLift 414837
  have htrace : WordTrace (prefixWord ++ tailWord_414837) baseStart_414837 baseEnd_414837 := by
    simpa [prefixWord, tailWord_414837, baseEnd_414837] using wordTrace_append hprefix tailTrace_414837
  have hstable : (prefixWord ++ tailWord_414837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414837).length < 2 ^ (prefixWord ++ tailWord_414837).sum := by decide
  have hdescent : baseEnd_414837 < baseStart_414837 := by decide
  rcases family_descends (prefixWord ++ tailWord_414837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414856 : List Nat := [2, 1, 3, 4, 3, 1, 1, 2, 2, 3]
def baseStart_414856 : Nat := 118140960795 + 414856 * 2 ^ 59
def prefixEnd_414856 : Nat := 4983230072969 + 3 ^ 40 * 414856 * 2
def baseEnd_414856 : Nat := 142013686934489405128079

theorem tailTrace_414856 : CollatzResearch.WordTrace tailWord_414856 prefixEnd_414856 142013686934489405128079 := by
  unfold tailWord_414856
  simp only [CollatzResearch.WordTrace]
  refine ⟨7565520692527519304556211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10087360923370025739408281 7565520692527519304556211)
  ·
    refine ⟨11348281038791278956834317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7565520692527519304556211 11348281038791278956834317)
    ·
      refine ⟨4255605389546729608812869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11348281038791278956834317 4255605389546729608812869)
      ·
        refine ⟨797926010540011801652413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4255605389546729608812869 797926010540011801652413)
        ·
          refine ⟨299222253952504425619655, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 797926010540011801652413 299222253952504425619655)
          ·
            refine ⟨448833380928756638429483, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299222253952504425619655 448833380928756638429483)
            ·
              refine ⟨673250071393134957644225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 448833380928756638429483 673250071393134957644225)
              ·
                refine ⟨504937553544851218233169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 673250071393134957644225 504937553544851218233169)
                ·
                  refine ⟨378703165158638413674877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 504937553544851218233169 378703165158638413674877)
                  ·
                    refine ⟨142013686934489405128079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378703165158638413674877 142013686934489405128079)
                    ·
                      rfl

theorem cell22_414856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 2, 2, 3].length) (baseStart_414856 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414856 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414856 prefixEnd_414856 := by exact prefixLift 414856
  have htrace : WordTrace (prefixWord ++ tailWord_414856) baseStart_414856 baseEnd_414856 := by
    simpa [prefixWord, tailWord_414856, baseEnd_414856] using wordTrace_append hprefix tailTrace_414856
  have hstable : (prefixWord ++ tailWord_414856).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414856).length < 2 ^ (prefixWord ++ tailWord_414856).sum := by decide
  have hdescent : baseEnd_414856 < baseStart_414856 := by decide
  rcases family_descends (prefixWord ++ tailWord_414856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414867 : List Nat := [1, 1, 1, 2, 1, 2, 6, 4, 1, 3]
def baseStart_414867 : Nat := 118140960795 + 414867 * 2 ^ 59
def prefixEnd_414867 : Nat := 4983230072969 + 3 ^ 40 * 414867 * 2
def baseEnd_414867 : Nat := 142017452459289043103045

theorem tailTrace_414867 : CollatzResearch.WordTrace tailWord_414867 prefixEnd_414867 142017452459289043103045 := by
  unfold tailWord_414867
  simp only [CollatzResearch.WordTrace]
  refine ⟨15131442588015187487762855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10087628392010124991841903 15131442588015187487762855)
  ·
    refine ⟨22697163882022781231644283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15131442588015187487762855 22697163882022781231644283)
    ·
      refine ⟨34045745823034171847466425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22697163882022781231644283 34045745823034171847466425)
      ·
        refine ⟨25534309367275628885599819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34045745823034171847466425 25534309367275628885599819)
        ·
          refine ⟨38301464050913443328399729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25534309367275628885599819 38301464050913443328399729)
          ·
            refine ⟨28726098038185082496299797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38301464050913443328399729 28726098038185082496299797)
            ·
              refine ⟨1346535845539925742014053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 28726098038185082496299797 1346535845539925742014053)
              ·
                refine ⟨252475471038736076627635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1346535845539925742014053 252475471038736076627635)
                ·
                  refine ⟨378713206558104114941453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252475471038736076627635 378713206558104114941453)
                  ·
                    refine ⟨142017452459289043103045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378713206558104114941453 142017452459289043103045)
                    ·
                      rfl

theorem cell22_414867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 4, 1, 3].length) (baseStart_414867 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414867 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414867 prefixEnd_414867 := by exact prefixLift 414867
  have htrace : WordTrace (prefixWord ++ tailWord_414867) baseStart_414867 baseEnd_414867 := by
    simpa [prefixWord, tailWord_414867, baseEnd_414867] using wordTrace_append hprefix tailTrace_414867
  have hstable : (prefixWord ++ tailWord_414867).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414867).length < 2 ^ (prefixWord ++ tailWord_414867).sum := by decide
  have hdescent : baseEnd_414867 < baseStart_414867 := by decide
  rcases family_descends (prefixWord ++ tailWord_414867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414923 : List Nat := [1, 1, 1, 1, 3, 2, 2, 1, 5, 5]
def baseStart_414923 : Nat := 118140960795 + 414923 * 2 ^ 59
def prefixEnd_414923 : Nat := 4983230072969 + 3 ^ 40 * 414923 * 2
def baseEnd_414923 : Nat := 142036622403723563702873

theorem tailTrace_414923 : CollatzResearch.WordTrace tailWord_414923 prefixEnd_414923 142036622403723563702873 := by
  unfold tailWord_414923
  simp only [CollatzResearch.WordTrace]
  refine ⟨15133485075812309051801423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10088990050541539367867615 15133485075812309051801423)
  ·
    refine ⟨22700227613718463577702135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15133485075812309051801423 22700227613718463577702135)
    ·
      refine ⟨34050341420577695366553203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22700227613718463577702135 34050341420577695366553203)
      ·
        refine ⟨51075512130866543049829805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34050341420577695366553203 51075512130866543049829805)
        ·
          refine ⟨19153317049074953643686177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51075512130866543049829805 19153317049074953643686177)
          ·
            refine ⟨14364987786806215232764633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19153317049074953643686177 14364987786806215232764633)
            ·
              refine ⟨10773740840104661424573475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14364987786806215232764633 10773740840104661424573475)
              ·
                refine ⟨16160611260156992136860213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10773740840104661424573475 16160611260156992136860213)
                ·
                  refine ⟨1515057305639718012830645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 16160611260156992136860213 1515057305639718012830645)
                  ·
                    refine ⟨142036622403723563702873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1515057305639718012830645 142036622403723563702873)
                    ·
                      rfl

theorem cell22_414923_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 2, 1, 5, 5].length) (baseStart_414923 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414923 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414923 prefixEnd_414923 := by exact prefixLift 414923
  have htrace : WordTrace (prefixWord ++ tailWord_414923) baseStart_414923 baseEnd_414923 := by
    simpa [prefixWord, tailWord_414923, baseEnd_414923] using wordTrace_append hprefix tailTrace_414923
  have hstable : (prefixWord ++ tailWord_414923).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414923).length < 2 ^ (prefixWord ++ tailWord_414923).sum := by decide
  have hdescent : baseEnd_414923 < baseStart_414923 := by decide
  rcases family_descends (prefixWord ++ tailWord_414923) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414955 : List Nat := [1, 1, 1, 1, 2, 6, 1, 3, 2, 4]
def baseStart_414955 : Nat := 118140960795 + 414955 * 2 ^ 59
def prefixEnd_414955 : Nat := 4983230072969 + 3 ^ 40 * 414955 * 2
def baseEnd_414955 : Nat := 142047576657686146902775

theorem tailTrace_414955 : CollatzResearch.WordTrace tailWord_414955 prefixEnd_414955 142047576657686146902775 := by
  unfold tailWord_414955
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134652211696378516966319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10089768141130919011310879 15134652211696378516966319)
  ·
    refine ⟨22701978317544567775449479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15134652211696378516966319 22701978317544567775449479)
    ·
      refine ⟨34052967476316851663174219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22701978317544567775449479 34052967476316851663174219)
      ·
        refine ⟨51079451214475277494761329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34052967476316851663174219 51079451214475277494761329)
        ·
          refine ⟨38309588410856458121070997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51079451214475277494761329 38309588410856458121070997)
          ·
            refine ⟨1795761956758896474425203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38309588410856458121070997 1795761956758896474425203)
            ·
              refine ⟨2693642935138344711637805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795761956758896474425203 2693642935138344711637805)
              ·
                refine ⟨1010116100676879266864177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2693642935138344711637805 1010116100676879266864177)
                ·
                  refine ⟨757587075507659450148133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010116100676879266864177 757587075507659450148133)
                  ·
                    refine ⟨142047576657686146902775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757587075507659450148133 142047576657686146902775)
                    ·
                      rfl

theorem cell22_414955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 3, 2, 4].length) (baseStart_414955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414955 prefixEnd_414955 := by exact prefixLift 414955
  have htrace : WordTrace (prefixWord ++ tailWord_414955) baseStart_414955 baseEnd_414955 := by
    simpa [prefixWord, tailWord_414955, baseEnd_414955] using wordTrace_append hprefix tailTrace_414955
  have hstable : (prefixWord ++ tailWord_414955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414955).length < 2 ^ (prefixWord ++ tailWord_414955).sum := by decide
  have hdescent : baseEnd_414955 < baseStart_414955 := by decide
  rcases family_descends (prefixWord ++ tailWord_414955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414957 : List Nat := [1, 5, 1, 2, 2, 2, 1, 2, 1, 5]
def baseStart_414957 : Nat := 118140960795 + 414957 * 2 ^ 59
def prefixEnd_414957 : Nat := 4983230072969 + 3 ^ 40 * 414957 * 2
def baseEnd_414957 : Nat := 142048261298558808352769

theorem tailTrace_414957 : CollatzResearch.WordTrace tailWord_414957 prefixEnd_414957 142048261298558808352769 := by
  unfold tailWord_414957
  simp only [CollatzResearch.WordTrace]
  refine ⟨15134725157689132858539125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10089816771792755239026083 15134725157689132858539125)
  ·
    refine ⟨1418880483533356205488043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15134725157689132858539125 1418880483533356205488043)
    ·
      refine ⟨2128320725300034308232065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1418880483533356205488043 2128320725300034308232065)
      ·
        refine ⟨1596240543975025731174049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2128320725300034308232065 1596240543975025731174049)
        ·
          refine ⟨1197180407981269298380537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1596240543975025731174049 1197180407981269298380537)
          ·
            refine ⟨897885305985951973785403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1197180407981269298380537 897885305985951973785403)
            ·
              refine ⟨1346827958978927960678105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 897885305985951973785403 1346827958978927960678105)
              ·
                refine ⟨1010120969234195970508579, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1346827958978927960678105 1010120969234195970508579)
                ·
                  refine ⟨1515181453851293955762869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1010120969234195970508579 1515181453851293955762869)
                  ·
                    refine ⟨142048261298558808352769, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1515181453851293955762869 142048261298558808352769)
                    ·
                      rfl

theorem cell22_414957_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 2, 1, 2, 1, 5].length) (baseStart_414957 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414957 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414957 prefixEnd_414957 := by exact prefixLift 414957
  have htrace : WordTrace (prefixWord ++ tailWord_414957) baseStart_414957 baseEnd_414957 := by
    simpa [prefixWord, tailWord_414957, baseEnd_414957] using wordTrace_append hprefix tailTrace_414957
  have hstable : (prefixWord ++ tailWord_414957).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414957).length < 2 ^ (prefixWord ++ tailWord_414957).sum := by decide
  have hdescent : baseEnd_414957 < baseStart_414957 := by decide
  rcases family_descends (prefixWord ++ tailWord_414957) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_414974 : List Nat := [4, 2, 2, 1, 1, 2, 1, 4, 2, 3]
def baseStart_414974 : Nat := 118140960795 + 414974 * 2 ^ 59
def prefixEnd_414974 : Nat := 4983230072969 + 3 ^ 40 * 414974 * 2
def baseEnd_414974 : Nat := 142054080745976430677717

theorem tailTrace_414974 : CollatzResearch.WordTrace tailWord_414974 prefixEnd_414974 142054080745976430677717 := by
  unfold tailWord_414974
  simp only [CollatzResearch.WordTrace]
  refine ⟨1891918149828443095238497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10090230132418363174605317 1891918149828443095238497)
  ·
    refine ⟨1418938612371332321428873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1891918149828443095238497 1418938612371332321428873)
    ·
      refine ⟨1064203959278499241071655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1418938612371332321428873 1064203959278499241071655)
      ·
        refine ⟨1596305938917748861607483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064203959278499241071655 1596305938917748861607483)
        ·
          refine ⟨2394458908376623292411225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1596305938917748861607483 2394458908376623292411225)
          ·
            refine ⟨1795844181282467469308419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2394458908376623292411225 1795844181282467469308419)
            ·
              refine ⟨2693766271923701203962629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795844181282467469308419 2693766271923701203962629)
              ·
                refine ⟨505081175985693975742993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2693766271923701203962629 505081175985693975742993)
                ·
                  refine ⟨378810881989270481807245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505081175985693975742993 378810881989270481807245)
                  ·
                    refine ⟨142054080745976430677717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378810881989270481807245 142054080745976430677717)
                    ·
                      rfl

theorem cell22_414974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 4, 2, 3].length) (baseStart_414974 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_414974 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_414974 prefixEnd_414974 := by exact prefixLift 414974
  have htrace : WordTrace (prefixWord ++ tailWord_414974) baseStart_414974 baseEnd_414974 := by
    simpa [prefixWord, tailWord_414974, baseEnd_414974] using wordTrace_append hprefix tailTrace_414974
  have hstable : (prefixWord ++ tailWord_414974).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_414974).length < 2 ^ (prefixWord ++ tailWord_414974).sum := by decide
  have hdescent : baseEnd_414974 < baseStart_414974 := by decide
  rcases family_descends (prefixWord ++ tailWord_414974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415002 : List Nat := [3, 1, 1, 3, 3, 1, 1, 1, 5, 3]
def baseStart_415002 : Nat := 118140960795 + 415002 * 2 ^ 59
def prefixEnd_415002 : Nat := 4983230072969 + 3 ^ 40 * 415002 * 2
def baseEnd_415002 : Nat := 142063665718193690977631

theorem tailTrace_415002 : CollatzResearch.WordTrace tailWord_415002 prefixEnd_415002 142063665718193690977631 := by
  unfold tailWord_415002
  simp only [CollatzResearch.WordTrace]
  refine ⟨3784091610631526385981815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10090910961684070362618173 3784091610631526385981815)
  ·
    refine ⟨5676137415947289578972723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3784091610631526385981815 5676137415947289578972723)
    ·
      refine ⟨8514206123920934368459085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676137415947289578972723 8514206123920934368459085)
      ·
        refine ⟨3192827296470350388172157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8514206123920934368459085 3192827296470350388172157)
        ·
          refine ⟨1197310236176381395564559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3192827296470350388172157 1197310236176381395564559)
          ·
            refine ⟨1795965354264572093346839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197310236176381395564559 1795965354264572093346839)
            ·
              refine ⟨2693948031396858140020259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1795965354264572093346839 2693948031396858140020259)
              ·
                refine ⟨4040922047095287210030389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2693948031396858140020259 4040922047095287210030389)
                ·
                  refine ⟨378836441915183175940349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4040922047095287210030389 378836441915183175940349)
                  ·
                    refine ⟨142063665718193690977631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 378836441915183175940349 142063665718193690977631)
                    ·
                      rfl

theorem cell22_415002_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 3, 1, 1, 1, 5, 3].length) (baseStart_415002 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415002 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415002 prefixEnd_415002 := by exact prefixLift 415002
  have htrace : WordTrace (prefixWord ++ tailWord_415002) baseStart_415002 baseEnd_415002 := by
    simpa [prefixWord, tailWord_415002, baseEnd_415002] using wordTrace_append hprefix tailTrace_415002
  have hstable : (prefixWord ++ tailWord_415002).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415002).length < 2 ^ (prefixWord ++ tailWord_415002).sum := by decide
  have hdescent : baseEnd_415002 < baseStart_415002 := by decide
  rcases family_descends (prefixWord ++ tailWord_415002) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415045 : List Nat := [1, 3, 1, 1, 1, 2, 1, 3, 5, 4]
def baseStart_415045 : Nat := 118140960795 + 415045 * 2 ^ 59
def prefixEnd_415045 : Nat := 4983230072969 + 3 ^ 40 * 415045 * 2
def baseEnd_415045 : Nat := 142078385496955912152499

theorem tailTrace_415045 : CollatzResearch.WordTrace tailWord_415045 prefixEnd_415045 142078385496955912152499 := by
  unfold tailWord_415045
  simp only [CollatzResearch.WordTrace]
  refine ⟨15137934781370323887742589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10091956520913549258495059 15137934781370323887742589)
  ·
    refine ⟨5676725543013871457903471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15137934781370323887742589 5676725543013871457903471)
    ·
      refine ⟨8515088314520807186855207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5676725543013871457903471 8515088314520807186855207)
      ·
        refine ⟨12772632471781210780282811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8515088314520807186855207 12772632471781210780282811)
        ·
          refine ⟨19158948707671816170424217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12772632471781210780282811 19158948707671816170424217)
          ·
            refine ⟨14369211530753862127818163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19158948707671816170424217 14369211530753862127818163)
            ·
              refine ⟨21553817296130793191727245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14369211530753862127818163 21553817296130793191727245)
              ·
                refine ⟨8082681486049047446897717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21553817296130793191727245 8082681486049047446897717)
                ·
                  refine ⟨757751389317098198146661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8082681486049047446897717 757751389317098198146661)
                  ·
                    refine ⟨142078385496955912152499, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757751389317098198146661 142078385496955912152499)
                    ·
                      rfl

theorem cell22_415045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 3, 5, 4].length) (baseStart_415045 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415045 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415045 prefixEnd_415045 := by exact prefixLift 415045
  have htrace : WordTrace (prefixWord ++ tailWord_415045) baseStart_415045 baseEnd_415045 := by
    simpa [prefixWord, tailWord_415045, baseEnd_415045] using wordTrace_append hprefix tailTrace_415045
  have hstable : (prefixWord ++ tailWord_415045).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415045).length < 2 ^ (prefixWord ++ tailWord_415045).sum := by decide
  have hdescent : baseEnd_415045 < baseStart_415045 := by decide
  rcases family_descends (prefixWord ++ tailWord_415045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415124 : List Nat := [2, 4, 2, 1, 2, 1, 1, 3, 2, 4]
def baseStart_415124 : Nat := 118140960795 + 415124 * 2 ^ 59
def prefixEnd_415124 : Nat := 4983230072969 + 3 ^ 40 * 415124 * 2
def baseEnd_415124 : Nat := 142105428811426039427257

theorem tailTrace_415124 : CollatzResearch.WordTrace tailWord_415124 prefixEnd_415124 142105428811426039427257 := by
  unfold tailWord_415124
  simp only [CollatzResearch.WordTrace]
  refine ⟨7570408074042060189934213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10093877432056080253245617 7570408074042060189934213)
  ·
    refine ⟨1419451513882886285612665, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7570408074042060189934213 1419451513882886285612665)
    ·
      refine ⟨1064588635412164714209499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1419451513882886285612665 1064588635412164714209499)
      ·
        refine ⟨1596882953118247071314249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064588635412164714209499 1596882953118247071314249)
        ·
          refine ⟨1197662214838685303485687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1596882953118247071314249 1197662214838685303485687)
          ·
            refine ⟨1796493322258027955228531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1197662214838685303485687 1796493322258027955228531)
            ·
              refine ⟨2694739983387041932842797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1796493322258027955228531 2694739983387041932842797)
              ·
                refine ⟨1010527493770140724816049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2694739983387041932842797 1010527493770140724816049)
                ·
                  refine ⟨757895620327605543612037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1010527493770140724816049 757895620327605543612037)
                  ·
                    refine ⟨142105428811426039427257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 757895620327605543612037 142105428811426039427257)
                    ·
                      rfl

theorem cell22_415124_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 1, 3, 2, 4].length) (baseStart_415124 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415124 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415124 prefixEnd_415124 := by exact prefixLift 415124
  have htrace : WordTrace (prefixWord ++ tailWord_415124) baseStart_415124 baseEnd_415124 := by
    simpa [prefixWord, tailWord_415124, baseEnd_415124] using wordTrace_append hprefix tailTrace_415124
  have hstable : (prefixWord ++ tailWord_415124).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415124).length < 2 ^ (prefixWord ++ tailWord_415124).sum := by decide
  have hdescent : baseEnd_415124 < baseStart_415124 := by decide
  rcases family_descends (prefixWord ++ tailWord_415124) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415261 : List Nat := [1, 4, 2, 2, 1, 1, 2, 4, 2, 3]
def baseStart_415261 : Nat := 118140960795 + 415261 * 2 ^ 59
def prefixEnd_415261 : Nat := 4983230072969 + 3 ^ 40 * 415261 * 2
def baseEnd_415261 : Nat := 142152326711203348751837

theorem tailTrace_415261 : CollatzResearch.WordTrace tailWord_415261 prefixEnd_415261 142152326711203348751837 := by
  unfold tailWord_415261
  simp only [CollatzResearch.WordTrace]
  refine ⟨15145812948587792777605637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10097208632391861851737091 15145812948587792777605637)
  ·
    refine ⟨2839839927860211145801057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15145812948587792777605637 2839839927860211145801057)
    ·
      refine ⟨2129879945895158359350793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2839839927860211145801057 2129879945895158359350793)
      ·
        refine ⟨1597409959421368769513095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2129879945895158359350793 1597409959421368769513095)
        ·
          refine ⟨2396114939132053154269643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597409959421368769513095 2396114939132053154269643)
          ·
            refine ⟨3594172408698079731404465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396114939132053154269643 3594172408698079731404465)
            ·
              refine ⟨2695629306523559798553349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3594172408698079731404465 2695629306523559798553349)
              ·
                refine ⟨505430494973167462228753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2695629306523559798553349 505430494973167462228753)
                ·
                  refine ⟨379072871229875596671565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505430494973167462228753 379072871229875596671565)
                  ·
                    refine ⟨142152326711203348751837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379072871229875596671565 142152326711203348751837)
                    ·
                      rfl

theorem cell22_415261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 4, 2, 3].length) (baseStart_415261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415261 prefixEnd_415261 := by exact prefixLift 415261
  have htrace : WordTrace (prefixWord ++ tailWord_415261) baseStart_415261 baseEnd_415261 := by
    simpa [prefixWord, tailWord_415261, baseEnd_415261] using wordTrace_append hprefix tailTrace_415261
  have hstable : (prefixWord ++ tailWord_415261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415261).length < 2 ^ (prefixWord ++ tailWord_415261).sum := by decide
  have hdescent : baseEnd_415261 < baseStart_415261 := by decide
  rcases family_descends (prefixWord ++ tailWord_415261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415274 : List Nat := [3, 1, 4, 1, 1, 1, 4, 7]
def baseStart_415274 : Nat := 118140960795 + 415274 * 2 ^ 59
def prefixEnd_415274 : Nat := 4983230072969 + 3 ^ 40 * 415274 * 2
def baseEnd_415274 : Nat := 15795197430763960908533

theorem tailTrace_415274 : CollatzResearch.WordTrace tailWord_415274 prefixEnd_415274 15795197430763960908533 := by
  unfold tailWord_415274
  simp only [CollatzResearch.WordTrace]
  refine ⟨3786571774385173999457219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10097524731693797331885917 3786571774385173999457219)
  ·
    refine ⟨5679857661577760999185829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3786571774385173999457219 5679857661577760999185829)
    ·
      refine ⟨1064973311545830187347343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5679857661577760999185829 1064973311545830187347343)
      ·
        refine ⟨1597459967318745281021015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064973311545830187347343 1597459967318745281021015)
        ·
          refine ⟨2396189950978117921531523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1597459967318745281021015 2396189950978117921531523)
          ·
            refine ⟨3594284926467176882297285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2396189950978117921531523 3594284926467176882297285)
            ·
              refine ⟨673928423712595665430741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3594284926467176882297285 673928423712595665430741)
              ·
                refine ⟨15795197430763960908533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 673928423712595665430741 15795197430763960908533)
                ·
                  rfl

theorem cell22_415274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 1, 4, 7].length) (baseStart_415274 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415274 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415274 prefixEnd_415274 := by exact prefixLift 415274
  have htrace : WordTrace (prefixWord ++ tailWord_415274) baseStart_415274 baseEnd_415274 := by
    simpa [prefixWord, tailWord_415274, baseEnd_415274] using wordTrace_append hprefix tailTrace_415274
  have hstable : (prefixWord ++ tailWord_415274).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415274).length < 2 ^ (prefixWord ++ tailWord_415274).sum := by decide
  have hdescent : baseEnd_415274 < baseStart_415274 := by decide
  rcases family_descends (prefixWord ++ tailWord_415274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415278 : List Nat := [4, 1, 3, 1, 2, 2, 1, 3, 2, 3]
def baseStart_415278 : Nat := 118140960795 + 415278 * 2 ^ 59
def prefixEnd_415278 : Nat := 4983230072969 + 3 ^ 40 * 415278 * 2
def baseEnd_415278 : Nat := 142158146158620971076785

theorem tailTrace_415278 : CollatzResearch.WordTrace tailWord_415278 prefixEnd_415278 142158146158620971076785 := by
  unfold tailWord_415278
  simp only [CollatzResearch.WordTrace]
  refine ⟨1893304123690775585121811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10097621993017469787316325 1893304123690775585121811)
  ·
    refine ⟨2839956185536163377682717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1893304123690775585121811 2839956185536163377682717)
    ·
      refine ⟨1064983569576061266631019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2839956185536163377682717 1064983569576061266631019)
      ·
        refine ⟨1597475354364091899946529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1064983569576061266631019 1597475354364091899946529)
        ·
          refine ⟨1198106515773068924959897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1597475354364091899946529 1198106515773068924959897)
          ·
            refine ⟨898579886829801693719923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1198106515773068924959897 898579886829801693719923)
            ·
              refine ⟨1347869830244702540579885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 898579886829801693719923 1347869830244702540579885)
              ·
                refine ⟨505451186341763452717457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1347869830244702540579885 505451186341763452717457)
                ·
                  refine ⟨379088389756322589538093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 505451186341763452717457 379088389756322589538093)
                  ·
                    refine ⟨142158146158620971076785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379088389756322589538093 142158146158620971076785)
                    ·
                      rfl

theorem cell22_415278_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 3, 2, 3].length) (baseStart_415278 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415278 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415278 prefixEnd_415278 := by exact prefixLift 415278
  have htrace : WordTrace (prefixWord ++ tailWord_415278) baseStart_415278 baseEnd_415278 := by
    simpa [prefixWord, tailWord_415278, baseEnd_415278] using wordTrace_append hprefix tailTrace_415278
  have hstable : (prefixWord ++ tailWord_415278).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415278).length < 2 ^ (prefixWord ++ tailWord_415278).sum := by decide
  have hdescent : baseEnd_415278 < baseStart_415278 := by decide
  rcases family_descends (prefixWord ++ tailWord_415278) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415319 : List Nat := [1, 1, 3, 2, 2, 3, 1, 4, 5]
def baseStart_415319 : Nat := 118140960795 + 415319 * 2 ^ 59
def prefixEnd_415319 : Nat := 4983230072969 + 3 ^ 40 * 415319 * 2
def baseEnd_415319 : Nat := 47390727098836843600553

theorem tailTrace_415319 : CollatzResearch.WordTrace tailWord_415319 prefixEnd_415319 47390727098836843600553 := by
  unfold tailWord_415319
  simp only [CollatzResearch.WordTrace]
  refine ⟨15147928382377668683217011, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10098618921585112455478007 15147928382377668683217011)
  ·
    refine ⟨22721892573566503024825517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15147928382377668683217011 22721892573566503024825517)
    ·
      refine ⟨8520709715087438634309569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22721892573566503024825517 8520709715087438634309569)
      ·
        refine ⟨6390532286315578975732177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8520709715087438634309569 6390532286315578975732177)
        ·
          refine ⟨4792899214736684231799133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6390532286315578975732177 4792899214736684231799133)
          ·
            refine ⟨1797337205526256586924675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4792899214736684231799133 1797337205526256586924675)
            ·
              refine ⟨2696005808289384880387013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1797337205526256586924675 2696005808289384880387013)
              ·
                refine ⟨505501089054259665072565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2696005808289384880387013 505501089054259665072565)
                ·
                  refine ⟨47390727098836843600553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 505501089054259665072565 47390727098836843600553)
                  ·
                    rfl

theorem cell22_415319_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 1, 4, 5].length) (baseStart_415319 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415319 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415319 prefixEnd_415319 := by exact prefixLift 415319
  have htrace : WordTrace (prefixWord ++ tailWord_415319) baseStart_415319 baseEnd_415319 := by
    simpa [prefixWord, tailWord_415319, baseEnd_415319] using wordTrace_append hprefix tailTrace_415319
  have hstable : (prefixWord ++ tailWord_415319).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415319).length < 2 ^ (prefixWord ++ tailWord_415319).sum := by decide
  have hdescent : baseEnd_415319 < baseStart_415319 := by decide
  rcases family_descends (prefixWord ++ tailWord_415319) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415325 : List Nat := [1, 4, 4, 2, 2, 1, 1, 7]
def baseStart_415325 : Nat := 118140960795 + 415325 * 2 ^ 59
def prefixEnd_415325 : Nat := 4983230072969 + 3 ^ 40 * 415325 * 2
def baseEnd_415325 : Nat := 15797137246569835016849

theorem tailTrace_415325 : CollatzResearch.WordTrace tailWord_415325 prefixEnd_415325 15797137246569835016849 := by
  unfold tailWord_415325
  simp only [CollatzResearch.WordTrace]
  refine ⟨15148147220355931707935429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10098764813570621138623619 15148147220355931707935429)
  ·
    refine ⟨2840277603816737195237893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15148147220355931707935429 2840277603816737195237893)
    ·
      refine ⟨532552050715638224107105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2840277603816737195237893 532552050715638224107105)
      ·
        refine ⟨399414038036728668080329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 532552050715638224107105 399414038036728668080329)
        ·
          refine ⟨299560528527546501060247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399414038036728668080329 299560528527546501060247)
          ·
            refine ⟨449340792791319751590371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299560528527546501060247 449340792791319751590371)
            ·
              refine ⟨674011189186979627385557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449340792791319751590371 674011189186979627385557)
              ·
                refine ⟨15797137246569835016849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 674011189186979627385557 15797137246569835016849)
                ·
                  rfl

theorem cell22_415325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 2, 2, 1, 1, 7].length) (baseStart_415325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415325 prefixEnd_415325 := by exact prefixLift 415325
  have htrace : WordTrace (prefixWord ++ tailWord_415325) baseStart_415325 baseEnd_415325 := by
    simpa [prefixWord, tailWord_415325, baseEnd_415325] using wordTrace_append hprefix tailTrace_415325
  have hstable : (prefixWord ++ tailWord_415325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415325).length < 2 ^ (prefixWord ++ tailWord_415325).sum := by decide
  have hdescent : baseEnd_415325 < baseStart_415325 := by decide
  rcases family_descends (prefixWord ++ tailWord_415325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415336 : List Nat := [2, 1, 4, 3, 1, 1, 2, 3, 5]
def baseStart_415336 : Nat := 118140960795 + 415336 * 2 ^ 59
def prefixEnd_415336 : Nat := 4983230072969 + 3 ^ 40 * 415336 * 2
def baseEnd_415336 : Nat := 47392666914642717708869

theorem tailTrace_415336 : CollatzResearch.WordTrace tailWord_415336 prefixEnd_415336 47392666914642717708869 := by
  unfold tailWord_415336
  simp only [CollatzResearch.WordTrace]
  refine ⟨7574274211658040293292931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10099032282210720391057241 7574274211658040293292931)
  ·
    refine ⟨11361411317487060439939397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7574274211658040293292931 11361411317487060439939397)
    ·
      refine ⟨2130264622028823832488637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11361411317487060439939397 2130264622028823832488637)
      ·
        refine ⟨798849233260808937183239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2130264622028823832488637 798849233260808937183239)
        ·
          refine ⟨1198273849891213405774859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 798849233260808937183239 1198273849891213405774859)
          ·
            refine ⟨1797410774836820108662289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198273849891213405774859 1797410774836820108662289)
            ·
              refine ⟨1348058081127615081496717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1797410774836820108662289 1348058081127615081496717)
              ·
                refine ⟨505521780422855655561269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1348058081127615081496717 505521780422855655561269)
                ·
                  refine ⟨47392666914642717708869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 505521780422855655561269 47392666914642717708869)
                  ·
                    rfl

theorem cell22_415336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 3, 5].length) (baseStart_415336 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415336 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415336 prefixEnd_415336 := by exact prefixLift 415336
  have htrace : WordTrace (prefixWord ++ tailWord_415336) baseStart_415336 baseEnd_415336 := by
    simpa [prefixWord, tailWord_415336, baseEnd_415336] using wordTrace_append hprefix tailTrace_415336
  have hstable : (prefixWord ++ tailWord_415336).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415336).length < 2 ^ (prefixWord ++ tailWord_415336).sum := by decide
  have hdescent : baseEnd_415336 < baseStart_415336 := by decide
  rcases family_descends (prefixWord ++ tailWord_415336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415396 : List Nat := [2, 3, 1, 2, 2, 2, 3, 1, 1, 5]
def baseStart_415396 : Nat := 118140960795 + 415396 * 2 ^ 59
def prefixEnd_415396 : Nat := 4983230072969 + 3 ^ 40 * 415396 * 2
def baseEnd_415396 : Nat := 142198539970107996626423

theorem tailTrace_415396 : CollatzResearch.WordTrace tailWord_415396 prefixEnd_415396 142198539970107996626423 := by
  unfold tailWord_415396
  simp only [CollatzResearch.WordTrace]
  refine ⟨7575368401549355416885021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10100491202065807222513361 7575368401549355416885021)
  ·
    refine ⟨2840763150581008281331883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7575368401549355416885021 2840763150581008281331883)
    ·
      refine ⟨4261144725871512421997825, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2840763150581008281331883 4261144725871512421997825)
      ·
        refine ⟨3195858544403634316498369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4261144725871512421997825 3195858544403634316498369)
        ·
          refine ⟨2396893908302725737373777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3195858544403634316498369 2396893908302725737373777)
          ·
            refine ⟨1797670431227044303030333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2396893908302725737373777 1797670431227044303030333)
            ·
              refine ⟨674126411710141613636375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1797670431227044303030333 674126411710141613636375)
              ·
                refine ⟨1011189617565212420454563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674126411710141613636375 1011189617565212420454563)
                ·
                  refine ⟨1516784426347818630681845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011189617565212420454563 1516784426347818630681845)
                  ·
                    refine ⟨142198539970107996626423, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1516784426347818630681845 142198539970107996626423)
                    ·
                      rfl

theorem cell22_415396_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 3, 1, 1, 5].length) (baseStart_415396 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415396 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415396 prefixEnd_415396 := by exact prefixLift 415396
  have htrace : WordTrace (prefixWord ++ tailWord_415396) baseStart_415396 baseEnd_415396 := by
    simpa [prefixWord, tailWord_415396, baseEnd_415396] using wordTrace_append hprefix tailTrace_415396
  have hstable : (prefixWord ++ tailWord_415396).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415396).length < 2 ^ (prefixWord ++ tailWord_415396).sum := by decide
  have hdescent : baseEnd_415396 < baseStart_415396 := by decide
  rcases family_descends (prefixWord ++ tailWord_415396) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415492 : List Nat := [2, 3, 2, 2, 1, 2, 4, 2, 1, 3]
def baseStart_415492 : Nat := 118140960795 + 415492 * 2 ^ 59
def prefixEnd_415492 : Nat := 4983230072969 + 3 ^ 40 * 415492 * 2
def baseEnd_415492 : Nat := 142231402731995746226129

theorem tailTrace_415492 : CollatzResearch.WordTrace tailWord_415492 prefixEnd_415492 142231402731995746226129 := by
  unfold tailWord_415492
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577119105375459614632365, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10102825473833946152843153 7577119105375459614632365)
  ·
    refine ⟨2841419664515797355487137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7577119105375459614632365 2841419664515797355487137)
    ·
      refine ⟨2131064748386848016615353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2841419664515797355487137 2131064748386848016615353)
      ·
        refine ⟨1598298561290136012461515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2131064748386848016615353 1598298561290136012461515)
        ·
          refine ⟨2397447841935204018692273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1598298561290136012461515 2397447841935204018692273)
          ·
            refine ⟨1798085881451403014019205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2397447841935204018692273 1798085881451403014019205)
            ·
              refine ⟨337141102772138065128601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1798085881451403014019205 337141102772138065128601)
              ·
                refine ⟨252855827079103548846451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337141102772138065128601 252855827079103548846451)
                ·
                  refine ⟨379283740618655323269677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252855827079103548846451 379283740618655323269677)
                  ·
                    refine ⟨142231402731995746226129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379283740618655323269677 142231402731995746226129)
                    ·
                      rfl

theorem cell22_415492_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 2, 1, 3].length) (baseStart_415492 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415492 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415492 prefixEnd_415492 := by exact prefixLift 415492
  have htrace : WordTrace (prefixWord ++ tailWord_415492) baseStart_415492 baseEnd_415492 := by
    simpa [prefixWord, tailWord_415492, baseEnd_415492] using wordTrace_append hprefix tailTrace_415492
  have hstable : (prefixWord ++ tailWord_415492).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415492).length < 2 ^ (prefixWord ++ tailWord_415492).sum := by decide
  have hdescent : baseEnd_415492 < baseStart_415492 := by decide
  rcases family_descends (prefixWord ++ tailWord_415492) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415516 : List Nat := [2, 2, 3, 1, 1, 2, 3, 2, 6]
def baseStart_415516 : Nat := 118140960795 + 415516 * 2 ^ 59
def prefixEnd_415516 : Nat := 4983230072969 + 3 ^ 40 * 415516 * 2
def baseEnd_415516 : Nat := 47413206140822561208685

theorem tailTrace_415516 : CollatzResearch.WordTrace tailWord_415516 prefixEnd_415516 47413206140822561208685 := by
  unfold tailWord_415516
  simp only [CollatzResearch.WordTrace]
  refine ⟨7577556781331985664069201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10103409041775980885425601 7577556781331985664069201)
  ·
    refine ⟨5683167585998989248051901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7577556781331985664069201 5683167585998989248051901)
    ·
      refine ⟨2131187844749620968019463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5683167585998989248051901 2131187844749620968019463)
      ·
        refine ⟨3196781767124431452029195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2131187844749620968019463 3196781767124431452029195)
        ·
          refine ⟨4795172650686647178043793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3196781767124431452029195 4795172650686647178043793)
          ·
            refine ⟨3596379488014985383532845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4795172650686647178043793 3596379488014985383532845)
            ·
              refine ⟨1348642308005619518824817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3596379488014985383532845 1348642308005619518824817)
              ·
                refine ⟨1011481731004214639118613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1348642308005619518824817 1011481731004214639118613)
                ·
                  refine ⟨47413206140822561208685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1011481731004214639118613 47413206140822561208685)
                  ·
                    rfl

theorem cell22_415516_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 3, 2, 6].length) (baseStart_415516 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415516 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415516 prefixEnd_415516 := by exact prefixLift 415516
  have htrace : WordTrace (prefixWord ++ tailWord_415516) baseStart_415516 baseEnd_415516 := by
    simpa [prefixWord, tailWord_415516, baseEnd_415516] using wordTrace_append hprefix tailTrace_415516
  have hstable : (prefixWord ++ tailWord_415516).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415516).length < 2 ^ (prefixWord ++ tailWord_415516).sum := by decide
  have hdescent : baseEnd_415516 < baseStart_415516 := by decide
  rcases family_descends (prefixWord ++ tailWord_415516) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415550 : List Nat := [4, 2, 1, 2, 2, 1, 2, 4, 4]
def baseStart_415550 : Nat := 118140960795 + 415550 * 2 ^ 59
def prefixEnd_415550 : Nat := 4983230072969 + 3 ^ 40 * 415550 * 2
def baseEnd_415550 : Nat := 47417085772434309425317

theorem tailTrace_415550 : CollatzResearch.WordTrace tailWord_415550 prefixEnd_415550 47417085772434309425317 := by
  unfold tailWord_415550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1894544205567599391859513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10104235763027196756584069 1894544205567599391859513)
  ·
    refine ⟨1420908154175699543894635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1894544205567599391859513 1420908154175699543894635)
    ·
      refine ⟨2131362231263549315841953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1420908154175699543894635 2131362231263549315841953)
      ·
        refine ⟨1598521673447661986881465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2131362231263549315841953 1598521673447661986881465)
        ·
          refine ⟨1198891255085746490161099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1598521673447661986881465 1198891255085746490161099)
          ·
            refine ⟨1798336882628619735241649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198891255085746490161099 1798336882628619735241649)
            ·
              refine ⟨1348752661971464801431237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1798336882628619735241649 1348752661971464801431237)
              ·
                refine ⟨252891124119649650268357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1348752661971464801431237 252891124119649650268357)
                ·
                  refine ⟨47417085772434309425317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 252891124119649650268357 47417085772434309425317)
                  ·
                    rfl

theorem cell22_415550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 2, 4, 4].length) (baseStart_415550 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415550 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415550 prefixEnd_415550 := by exact prefixLift 415550
  have htrace : WordTrace (prefixWord ++ tailWord_415550) baseStart_415550 baseEnd_415550 := by
    simpa [prefixWord, tailWord_415550, baseEnd_415550] using wordTrace_append hprefix tailTrace_415550
  have hstable : (prefixWord ++ tailWord_415550).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415550).length < 2 ^ (prefixWord ++ tailWord_415550).sum := by decide
  have hdescent : baseEnd_415550 < baseStart_415550 := by decide
  rcases family_descends (prefixWord ++ tailWord_415550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415565 : List Nat := [1, 6, 1, 2, 1, 1, 3, 1, 1, 5]
def baseStart_415565 : Nat := 118140960795 + 415565 * 2 ^ 59
def prefixEnd_415565 : Nat := 4983230072969 + 3 ^ 40 * 415565 * 2
def baseEnd_415565 : Nat := 142256392123847889150905

theorem tailTrace_415565 : CollatzResearch.WordTrace tailWord_415565 prefixEnd_415565 142256392123847889150905 := by
  unfold tailWord_415565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15156900739486452696672149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10104600492990968464448099 15156900739486452696672149)
  ·
    refine ⟨710479722163427470156507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 15156900739486452696672149 710479722163427470156507)
    ·
      refine ⟨1065719583245141205234761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 710479722163427470156507 1065719583245141205234761)
      ·
        refine ⟨799289687433855903926071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1065719583245141205234761 799289687433855903926071)
        ·
          refine ⟨1198934531150783855889107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799289687433855903926071 1198934531150783855889107)
          ·
            refine ⟨1798401796726175783833661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1198934531150783855889107 1798401796726175783833661)
            ·
              refine ⟨674400673772315918937623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1798401796726175783833661 674400673772315918937623)
              ·
                refine ⟨1011601010658473878406435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674400673772315918937623 1011601010658473878406435)
                ·
                  refine ⟨1517401515987710817609653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1011601010658473878406435 1517401515987710817609653)
                  ·
                    refine ⟨142256392123847889150905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1517401515987710817609653 142256392123847889150905)
                    ·
                      rfl

theorem cell22_415565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 1, 3, 1, 1, 5].length) (baseStart_415565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415565 prefixEnd_415565 := by exact prefixLift 415565
  have htrace : WordTrace (prefixWord ++ tailWord_415565) baseStart_415565 baseEnd_415565 := by
    simpa [prefixWord, tailWord_415565, baseEnd_415565] using wordTrace_append hprefix tailTrace_415565
  have hstable : (prefixWord ++ tailWord_415565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415565).length < 2 ^ (prefixWord ++ tailWord_415565).sum := by decide
  have hdescent : baseEnd_415565 < baseStart_415565 := by decide
  rcases family_descends (prefixWord ++ tailWord_415565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415610 : List Nat := [3, 1, 1, 1, 1, 1, 4, 6, 1, 3]
def baseStart_415610 : Nat := 118140960795 + 415610 * 2 ^ 59
def prefixEnd_415610 : Nat := 4983230072969 + 3 ^ 40 * 415610 * 2
def baseEnd_415610 : Nat := 142271796543482771775767

theorem tailTrace_415610 : CollatzResearch.WordTrace tailWord_415610 prefixEnd_415610 142271796543482771775767 := by
  unfold tailWord_415610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3789635506080856345515071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10105694682882283588040189 3789635506080856345515071)
  ·
    refine ⟨5684453259121284518272607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3789635506080856345515071 5684453259121284518272607)
    ·
      refine ⟨8526679888681926777408911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684453259121284518272607 8526679888681926777408911)
      ·
        refine ⟨12790019833022890166113367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8526679888681926777408911 12790019833022890166113367)
        ·
          refine ⟨19185029749534335249170051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12790019833022890166113367 19185029749534335249170051)
          ·
            refine ⟨28777544624301502873755077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19185029749534335249170051 28777544624301502873755077)
            ·
              refine ⟨5395789617056531788829077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28777544624301502873755077 5395789617056531788829077)
              ·
                refine ⟨252927638299524927601363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5395789617056531788829077 252927638299524927601363)
                ·
                  refine ⟨379391457449287391402045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 252927638299524927601363 379391457449287391402045)
                  ·
                    refine ⟨142271796543482771775767, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379391457449287391402045 142271796543482771775767)
                    ·
                      rfl

theorem cell22_415610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 6, 1, 3].length) (baseStart_415610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415610 prefixEnd_415610 := by exact prefixLift 415610
  have htrace : WordTrace (prefixWord ++ tailWord_415610) baseStart_415610 baseEnd_415610 := by
    simpa [prefixWord, tailWord_415610, baseEnd_415610] using wordTrace_append hprefix tailTrace_415610
  have hstable : (prefixWord ++ tailWord_415610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415610).length < 2 ^ (prefixWord ++ tailWord_415610).sum := by decide
  have hdescent : baseEnd_415610 < baseStart_415610 := by decide
  rcases family_descends (prefixWord ++ tailWord_415610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415621 : List Nat := [1, 3, 1, 1, 3, 2, 2, 1, 1, 7]
def baseStart_415621 : Nat := 118140960795 + 415621 * 2 ^ 59
def prefixEnd_415621 : Nat := 4983230072969 + 3 ^ 40 * 415621 * 2
def baseEnd_415621 : Nat := 142275562068282409750733

theorem tailTrace_415621 : CollatzResearch.WordTrace tailWord_415621 prefixEnd_415621 142275562068282409750733 := by
  unfold tailWord_415621
  simp only [CollatzResearch.WordTrace]
  refine ⟨15158943227283574260710717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10105962151522382840473811 15158943227283574260710717)
  ·
    refine ⟨5684603710231340347766519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15158943227283574260710717 5684603710231340347766519)
    ·
      refine ⟨8526905565347010521649779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5684603710231340347766519 8526905565347010521649779)
      ·
        refine ⟨12790358348020515782474669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8526905565347010521649779 12790358348020515782474669)
        ·
          refine ⟨4796384380507693418428001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12790358348020515782474669 4796384380507693418428001)
          ·
            refine ⟨3597288285380770063821001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4796384380507693418428001 3597288285380770063821001)
            ·
              refine ⟨2697966214035577547865751, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597288285380770063821001 2697966214035577547865751)
              ·
                refine ⟨4046949321053366321798627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2697966214035577547865751 4046949321053366321798627)
                ·
                  refine ⟨6070423981580049482697941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4046949321053366321798627 6070423981580049482697941)
                  ·
                    refine ⟨142275562068282409750733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6070423981580049482697941 142275562068282409750733)
                    ·
                      rfl

theorem cell22_415621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 7].length) (baseStart_415621 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415621 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415621 prefixEnd_415621 := by exact prefixLift 415621
  have htrace : WordTrace (prefixWord ++ tailWord_415621) baseStart_415621 baseEnd_415621 := by
    simpa [prefixWord, tailWord_415621, baseEnd_415621] using wordTrace_append hprefix tailTrace_415621
  have hstable : (prefixWord ++ tailWord_415621).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415621).length < 2 ^ (prefixWord ++ tailWord_415621).sum := by decide
  have hdescent : baseEnd_415621 < baseStart_415621 := by decide
  rcases family_descends (prefixWord ++ tailWord_415621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415653 : List Nat := [1, 3, 1, 2, 1, 1, 1, 7, 1, 4]
def baseStart_415653 : Nat := 118140960795 + 415653 * 2 ^ 59
def prefixEnd_415653 : Nat := 4983230072969 + 3 ^ 40 * 415653 * 2
def baseEnd_415653 : Nat := 142286516322244992950635

theorem tailTrace_415653 : CollatzResearch.WordTrace tailWord_415653 prefixEnd_415653 142286516322244992950635 := by
  unfold tailWord_415653
  simp only [CollatzResearch.WordTrace]
  refine ⟨15160110363167643725875613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10106740242111762483917075 15160110363167643725875613)
  ·
    refine ⟨5685041386187866397203355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15160110363167643725875613 5685041386187866397203355)
    ·
      refine ⟨8527562079281799595805033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5685041386187866397203355 8527562079281799595805033)
      ·
        refine ⟨6395671559461349696853775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8527562079281799595805033 6395671559461349696853775)
        ·
          refine ⟨9593507339192024545280663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6395671559461349696853775 9593507339192024545280663)
          ·
            refine ⟨14390261008788036817920995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9593507339192024545280663 14390261008788036817920995)
            ·
              refine ⟨21585391513182055226881493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14390261008788036817920995 21585391513182055226881493)
              ·
                refine ⟨505907613590204419380035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21585391513182055226881493 505907613590204419380035)
                ·
                  refine ⟨758861420385306629070053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 505907613590204419380035 758861420385306629070053)
                  ·
                    refine ⟨142286516322244992950635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 758861420385306629070053 142286516322244992950635)
                    ·
                      rfl

theorem cell22_415653_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 1, 7, 1, 4].length) (baseStart_415653 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415653 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415653 prefixEnd_415653 := by exact prefixLift 415653
  have htrace : WordTrace (prefixWord ++ tailWord_415653) baseStart_415653 baseEnd_415653 := by
    simpa [prefixWord, tailWord_415653, baseEnd_415653] using wordTrace_append hprefix tailTrace_415653
  have hstable : (prefixWord ++ tailWord_415653).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415653).length < 2 ^ (prefixWord ++ tailWord_415653).sum := by decide
  have hdescent : baseEnd_415653 < baseStart_415653 := by decide
  rcases family_descends (prefixWord ++ tailWord_415653) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415696 : List Nat := [2, 1, 1, 1, 1, 2, 4, 10]
def baseStart_415696 : Nat := 118140960795 + 415696 * 2 ^ 59
def prefixEnd_415696 : Nat := 4983230072969 + 3 ^ 40 * 415696 * 2
def baseEnd_415696 : Nat := 15811248455667468236167

theorem tailTrace_415696 : CollatzResearch.WordTrace tailWord_415696 prefixEnd_415696 15811248455667468236167 := by
  unfold tailWord_415696
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580839351005931034845471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10107785801341241379793961 7580839351005931034845471)
  ·
    refine ⟨11371259026508896552268207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7580839351005931034845471 11371259026508896552268207)
    ·
      refine ⟨17056888539763344828402311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11371259026508896552268207 17056888539763344828402311)
      ·
        refine ⟨25585332809645017242603467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17056888539763344828402311 25585332809645017242603467)
        ·
          refine ⟨38377999214467525863905201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25585332809645017242603467 38377999214467525863905201)
          ·
            refine ⟨28783499410850644397928901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38377999214467525863905201 28783499410850644397928901)
            ·
              refine ⟨5396906139534495824611669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 28783499410850644397928901 5396906139534495824611669)
              ·
                refine ⟨15811248455667468236167, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 5396906139534495824611669 15811248455667468236167)
                ·
                  rfl

theorem cell22_415696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 4, 10].length) (baseStart_415696 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415696 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415696 prefixEnd_415696 := by exact prefixLift 415696
  have htrace : WordTrace (prefixWord ++ tailWord_415696) baseStart_415696 baseEnd_415696 := by
    simpa [prefixWord, tailWord_415696, baseEnd_415696] using wordTrace_append hprefix tailTrace_415696
  have hstable : (prefixWord ++ tailWord_415696).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415696).length < 2 ^ (prefixWord ++ tailWord_415696).sum := by decide
  have hdescent : baseEnd_415696 < baseStart_415696 := by decide
  rcases family_descends (prefixWord ++ tailWord_415696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415700 : List Nat := [2, 4, 1, 2, 1, 1, 2, 2, 4, 3]
def baseStart_415700 : Nat := 118140960795 + 415700 * 2 ^ 59
def prefixEnd_415700 : Nat := 4983230072969 + 3 ^ 40 * 415700 * 2
def baseEnd_415700 : Nat := 142302605382752537025491

theorem tailTrace_415700 : CollatzResearch.WordTrace tailWord_415700 prefixEnd_415700 142302605382752537025491 := by
  unfold tailWord_415700
  simp only [CollatzResearch.WordTrace]
  refine ⟨7580912296998685376418277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10107883062664913835224369 7580912296998685376418277)
  ·
    refine ⟨1421421055687253508078427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7580912296998685376418277 1421421055687253508078427)
    ·
      refine ⟨2132131583530880262117641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1421421055687253508078427 2132131583530880262117641)
      ·
        refine ⟨1599098687648160196588231, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2132131583530880262117641 1599098687648160196588231)
        ·
          refine ⟨2398648031472240294882347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599098687648160196588231 2398648031472240294882347)
          ·
            refine ⟨3597972047208360442323521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398648031472240294882347 3597972047208360442323521)
            ·
              refine ⟨2698479035406270331742641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3597972047208360442323521 2698479035406270331742641)
              ·
                refine ⟨2023859276554702748806981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2698479035406270331742641 2023859276554702748806981)
                ·
                  refine ⟨379473614354006765401309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2023859276554702748806981 379473614354006765401309)
                  ·
                    refine ⟨142302605382752537025491, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379473614354006765401309 142302605382752537025491)
                    ·
                      rfl

theorem cell22_415700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 2, 2, 4, 3].length) (baseStart_415700 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415700 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415700 prefixEnd_415700 := by exact prefixLift 415700
  have htrace : WordTrace (prefixWord ++ tailWord_415700) baseStart_415700 baseEnd_415700 := by
    simpa [prefixWord, tailWord_415700, baseEnd_415700] using wordTrace_append hprefix tailTrace_415700
  have hstable : (prefixWord ++ tailWord_415700).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415700).length < 2 ^ (prefixWord ++ tailWord_415700).sum := by decide
  have hdescent : baseEnd_415700 < baseStart_415700 := by decide
  rcases family_descends (prefixWord ++ tailWord_415700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415734 : List Nat := [5, 1, 1, 1, 5, 1, 1, 1, 1, 5]
def baseStart_415734 : Nat := 118140960795 + 415734 * 2 ^ 59
def prefixEnd_415734 : Nat := 4983230072969 + 3 ^ 40 * 415734 * 2
def baseEnd_415734 : Nat := 142314244277587781675387

theorem tailTrace_415734 : CollatzResearch.WordTrace tailWord_415734 prefixEnd_415734 142314244277587781675387 := by
  unfold tailWord_415734
  simp only [CollatzResearch.WordTrace]
  refine ⟨947691542242137159973391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10108709783916129706382837 947691542242137159973391)
  ·
    refine ⟨1421537313363205739960087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 947691542242137159973391 1421537313363205739960087)
    ·
      refine ⟨2132305970044808609940131, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1421537313363205739960087 2132305970044808609940131)
      ·
        refine ⟨3198458955067212914910197, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132305970044808609940131 3198458955067212914910197)
        ·
          refine ⟨299855527037551210772831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3198458955067212914910197 299855527037551210772831)
          ·
            refine ⟨449783290556326816159247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299855527037551210772831 449783290556326816159247)
            ·
              refine ⟨674674935834490224238871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449783290556326816159247 674674935834490224238871)
              ·
                refine ⟨1012012403751735336358307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 674674935834490224238871 1012012403751735336358307)
                ·
                  refine ⟨1518018605627603004537461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1012012403751735336358307 1518018605627603004537461)
                  ·
                    refine ⟨142314244277587781675387, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1518018605627603004537461 142314244277587781675387)
                    ·
                      rfl

theorem cell22_415734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 5, 1, 1, 1, 1, 5].length) (baseStart_415734 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415734 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415734 prefixEnd_415734 := by exact prefixLift 415734
  have htrace : WordTrace (prefixWord ++ tailWord_415734) baseStart_415734 baseEnd_415734 := by
    simpa [prefixWord, tailWord_415734, baseEnd_415734] using wordTrace_append hprefix tailTrace_415734
  have hstable : (prefixWord ++ tailWord_415734).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415734).length < 2 ^ (prefixWord ++ tailWord_415734).sum := by decide
  have hdescent : baseEnd_415734 < baseStart_415734 := by decide
  rcases family_descends (prefixWord ++ tailWord_415734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415745 : List Nat := [1, 2, 4, 1, 2, 1, 1, 4, 3, 3]
def baseStart_415745 : Nat := 118140960795 + 415745 * 2 ^ 59
def prefixEnd_415745 : Nat := 4983230072969 + 3 ^ 40 * 415745 * 2
def baseEnd_415745 : Nat := 142318009802387419650353

theorem tailTrace_415745 : CollatzResearch.WordTrace tailWord_415745 prefixEnd_415745 142318009802387419650353 := by
  unfold tailWord_415745
  simp only [CollatzResearch.WordTrace]
  refine ⟨15163465878834343438224689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10108977252556228958816459 15163465878834343438224689)
  ·
    refine ⟨11372599409125757578668517, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15163465878834343438224689 11372599409125757578668517)
    ·
      refine ⟨2132362389211079546000347, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11372599409125757578668517 2132362389211079546000347)
      ·
        refine ⟨3198543583816619319000521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2132362389211079546000347 3198543583816619319000521)
        ·
          refine ⟨2398907687862464489250391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198543583816619319000521 2398907687862464489250391)
          ·
            refine ⟨3598361531793696733875587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398907687862464489250391 3598361531793696733875587)
            ·
              refine ⟨5397542297690545100813381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598361531793696733875587 5397542297690545100813381)
              ·
                refine ⟨1012039180816977206402509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5397542297690545100813381 1012039180816977206402509)
                ·
                  refine ⟨379514692806366452400941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012039180816977206402509 379514692806366452400941)
                  ·
                    refine ⟨142318009802387419650353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379514692806366452400941 142318009802387419650353)
                    ·
                      rfl

theorem cell22_415745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 4, 3, 3].length) (baseStart_415745 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415745 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415745 prefixEnd_415745 := by exact prefixLift 415745
  have htrace : WordTrace (prefixWord ++ tailWord_415745) baseStart_415745 baseEnd_415745 := by
    simpa [prefixWord, tailWord_415745, baseEnd_415745] using wordTrace_append hprefix tailTrace_415745
  have hstable : (prefixWord ++ tailWord_415745).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415745).length < 2 ^ (prefixWord ++ tailWord_415745).sum := by decide
  have hdescent : baseEnd_415745 < baseStart_415745 := by decide
  rcases family_descends (prefixWord ++ tailWord_415745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415758 : List Nat := [4, 1, 1, 2, 2, 1, 1, 1, 9]
def baseStart_415758 : Nat := 118140960795 + 415758 * 2 ^ 59
def prefixEnd_415758 : Nat := 4983230072969 + 3 ^ 40 * 415758 * 2
def baseEnd_415758 : Nat := 47440819989353239691771

theorem tailTrace_415758 : CollatzResearch.WordTrace tailWord_415758 prefixEnd_415758 47440819989353239691771 := by
  unfold tailWord_415758
  simp only [CollatzResearch.WordTrace]
  refine ⟨1895492503473405832305991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10109293351858164438965285 1895492503473405832305991)
  ·
    refine ⟨2843238755210108748458987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1895492503473405832305991 2843238755210108748458987)
    ·
      refine ⟨4264858132815163122688481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843238755210108748458987 4264858132815163122688481)
      ·
        refine ⟨3198643599611372342016361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4264858132815163122688481 3198643599611372342016361)
        ·
          refine ⟨2398982699708529256512271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3198643599611372342016361 2398982699708529256512271)
          ·
            refine ⟨3598474049562793884768407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2398982699708529256512271 3598474049562793884768407)
            ·
              refine ⟨5397711074344190827152611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3598474049562793884768407 5397711074344190827152611)
              ·
                refine ⟨8096566611516286240728917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5397711074344190827152611 8096566611516286240728917)
                ·
                  refine ⟨47440819989353239691771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8096566611516286240728917 47440819989353239691771)
                  ·
                    rfl

theorem cell22_415758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 1, 1, 9].length) (baseStart_415758 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415758 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415758 prefixEnd_415758 := by exact prefixLift 415758
  have htrace : WordTrace (prefixWord ++ tailWord_415758) baseStart_415758 baseEnd_415758 := by
    simpa [prefixWord, tailWord_415758, baseEnd_415758] using wordTrace_append hprefix tailTrace_415758
  have hstable : (prefixWord ++ tailWord_415758).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415758).length < 2 ^ (prefixWord ++ tailWord_415758).sum := by decide
  have hdescent : baseEnd_415758 < baseStart_415758 := by decide
  rcases family_descends (prefixWord ++ tailWord_415758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415764 : List Nat := [2, 4, 3, 2, 2, 1, 8]
def baseStart_415764 : Nat := 118140960795 + 415764 * 2 ^ 59
def prefixEnd_415764 : Nat := 4983230072969 + 3 ^ 40 * 415764 * 2
def baseEnd_415764 : Nat := 5271278292247322349085

theorem tailTrace_415764 : CollatzResearch.WordTrace tailWord_415764 prefixEnd_415764 5271278292247322349085 := by
  unfold tailWord_415764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582079432882754841583173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10109439243843673122110897 7582079432882754841583173)
  ·
    refine ⟨1421639893665516532796845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7582079432882754841583173 1421639893665516532796845)
    ·
      refine ⟨533114960124568699798817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1421639893665516532796845 533114960124568699798817)
      ·
        refine ⟨399836220093426524849113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 533114960124568699798817 399836220093426524849113)
        ·
          refine ⟨299877165070069893636835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 399836220093426524849113 299877165070069893636835)
          ·
            refine ⟨449815747605104840455253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 299877165070069893636835 449815747605104840455253)
            ·
              refine ⟨5271278292247322349085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 449815747605104840455253 5271278292247322349085)
              ·
                rfl

theorem cell22_415764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 2, 1, 8].length) (baseStart_415764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415764 prefixEnd_415764 := by exact prefixLift 415764
  have htrace : WordTrace (prefixWord ++ tailWord_415764) baseStart_415764 baseEnd_415764 := by
    simpa [prefixWord, tailWord_415764, baseEnd_415764] using wordTrace_append hprefix tailTrace_415764
  have hstable : (prefixWord ++ tailWord_415764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415764).length < 2 ^ (prefixWord ++ tailWord_415764).sum := by decide
  have hdescent : baseEnd_415764 < baseStart_415764 := by decide
  rcases family_descends (prefixWord ++ tailWord_415764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415779 : List Nat := [1, 1, 1, 4, 3, 1, 5, 2, 1, 3]
def baseStart_415779 : Nat := 118140960795 + 415779 * 2 ^ 59
def prefixEnd_415779 : Nat := 4983230072969 + 3 ^ 40 * 415779 * 2
def baseEnd_415779 : Nat := 142329648697222664300249

theorem tailTrace_415779 : CollatzResearch.WordTrace tailWord_415779 prefixEnd_415779 142329648697222664300249 := by
  unfold tailWord_415779
  simp only [CollatzResearch.WordTrace]
  refine ⟨15164705960711167244962391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10109803973807444829974927 15164705960711167244962391)
  ·
    refine ⟨22747058941066750867443587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15164705960711167244962391 22747058941066750867443587)
    ·
      refine ⟨34120588411600126301165381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22747058941066750867443587 34120588411600126301165381)
      ·
        refine ⟨6397610327175023681468509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34120588411600126301165381 6397610327175023681468509)
        ·
          refine ⟨2399103872690633880550691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6397610327175023681468509 2399103872690633880550691)
          ·
            refine ⟨3598655809035950820826037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399103872690633880550691 3598655809035950820826037)
            ·
              refine ⟨337373982097120389452441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3598655809035950820826037 337373982097120389452441)
              ·
                refine ⟨253030486572840292089331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337373982097120389452441 253030486572840292089331)
                ·
                  refine ⟨379545729859260438133997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253030486572840292089331 379545729859260438133997)
                  ·
                    refine ⟨142329648697222664300249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379545729859260438133997 142329648697222664300249)
                    ·
                      rfl

theorem cell22_415779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 2, 1, 3].length) (baseStart_415779 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415779 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415779 prefixEnd_415779 := by exact prefixLift 415779
  have htrace : WordTrace (prefixWord ++ tailWord_415779) baseStart_415779 baseEnd_415779 := by
    simpa [prefixWord, tailWord_415779, baseEnd_415779] using wordTrace_append hprefix tailTrace_415779
  have hstable : (prefixWord ++ tailWord_415779).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415779).length < 2 ^ (prefixWord ++ tailWord_415779).sum := by decide
  have hdescent : baseEnd_415779 < baseStart_415779 := by decide
  rcases family_descends (prefixWord ++ tailWord_415779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415792 : List Nat := [2, 1, 1, 1, 2, 7, 2, 1, 5]
def baseStart_415792 : Nat := 118140960795 + 415792 * 2 ^ 59
def prefixEnd_415792 : Nat := 4983230072969 + 3 ^ 40 * 415792 * 2
def baseEnd_415792 : Nat := 47444699620964987908403

theorem tailTrace_415792 : CollatzResearch.WordTrace tailWord_415792 prefixEnd_415792 47444699620964987908403 := by
  unfold tailWord_415792
  simp only [CollatzResearch.WordTrace]
  refine ⟨7582590054832035232592815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10110120073109380310123753 7582590054832035232592815)
  ·
    refine ⟨11373885082248052848889223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7582590054832035232592815 11373885082248052848889223)
    ·
      refine ⟨17060827623372079273333835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11373885082248052848889223 17060827623372079273333835)
      ·
        refine ⟨25591241435058118910000753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17060827623372079273333835 25591241435058118910000753)
        ·
          refine ⟨19193431076293589182500565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25591241435058118910000753 19193431076293589182500565)
          ·
            refine ⟨449846040850630996464857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19193431076293589182500565 449846040850630996464857)
            ·
              refine ⟨337384530637973247348643, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449846040850630996464857 337384530637973247348643)
              ·
                refine ⟨506076795956959871022965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337384530637973247348643 506076795956959871022965)
                ·
                  refine ⟨47444699620964987908403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 506076795956959871022965 47444699620964987908403)
                  ·
                    rfl

theorem cell22_415792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 7, 2, 1, 5].length) (baseStart_415792 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415792 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415792 prefixEnd_415792 := by exact prefixLift 415792
  have htrace : WordTrace (prefixWord ++ tailWord_415792) baseStart_415792 baseEnd_415792 := by
    simpa [prefixWord, tailWord_415792, baseEnd_415792] using wordTrace_append hprefix tailTrace_415792
  have hstable : (prefixWord ++ tailWord_415792).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415792).length < 2 ^ (prefixWord ++ tailWord_415792).sum := by decide
  have hdescent : baseEnd_415792 < baseStart_415792 := by decide
  rcases family_descends (prefixWord ++ tailWord_415792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415805 : List Nat := [1, 4, 1, 3, 1, 1, 3, 1, 3, 4]
def baseStart_415805 : Nat := 118140960795 + 415805 * 2 ^ 59
def prefixEnd_415805 : Nat := 4983230072969 + 3 ^ 40 * 415805 * 2
def baseEnd_415805 : Nat := 142338549028567263150169

theorem tailTrace_415805 : CollatzResearch.WordTrace tailWord_415805 prefixEnd_415805 142338549028567263150169 := by
  unfold tailWord_415805
  simp only [CollatzResearch.WordTrace]
  refine ⟨15165654258616973685408869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10110436172411315790272579 15165654258616973685408869)
  ·
    refine ⟨2843560173490682566014163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15165654258616973685408869 2843560173490682566014163)
    ·
      refine ⟨4265340260236023849021245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2843560173490682566014163 4265340260236023849021245)
      ·
        refine ⟨1599502597588508943382967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4265340260236023849021245 1599502597588508943382967)
        ·
          refine ⟨2399253896382763415074451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1599502597588508943382967 2399253896382763415074451)
          ·
            refine ⟨3598880844574145122611677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2399253896382763415074451 3598880844574145122611677)
            ·
              refine ⟨1349580316715304420979379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3598880844574145122611677 1349580316715304420979379)
              ·
                refine ⟨2024370475072956631469069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1349580316715304420979379 2024370475072956631469069)
                ·
                  refine ⟨759138928152358736800901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2024370475072956631469069 759138928152358736800901)
                  ·
                    refine ⟨142338549028567263150169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759138928152358736800901 142338549028567263150169)
                    ·
                      rfl

theorem cell22_415805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 1, 3, 1, 3, 4].length) (baseStart_415805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415805 prefixEnd_415805 := by exact prefixLift 415805
  have htrace : WordTrace (prefixWord ++ tailWord_415805) baseStart_415805 baseEnd_415805 := by
    simpa [prefixWord, tailWord_415805, baseEnd_415805] using wordTrace_append hprefix tailTrace_415805
  have hstable : (prefixWord ++ tailWord_415805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415805).length < 2 ^ (prefixWord ++ tailWord_415805).sum := by decide
  have hdescent : baseEnd_415805 < baseStart_415805 := by decide
  rcases family_descends (prefixWord ++ tailWord_415805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415830 : List Nat := [5, 2, 2, 1, 1, 3, 2, 2, 1, 3]
def baseStart_415830 : Nat := 118140960795 + 415830 * 2 ^ 59
def prefixEnd_415830 : Nat := 4983230072969 + 3 ^ 40 * 415830 * 2
def baseEnd_415830 : Nat := 142347107039475531275093

theorem tailTrace_415830 : CollatzResearch.WordTrace tailWord_415830 prefixEnd_415830 142347107039475531275093 := by
  unfold tailWord_415830
  simp only [CollatzResearch.WordTrace]
  refine ⟨947910380220400184691809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10111044055684268636712629 947910380220400184691809)
  ·
    refine ⟨710932785165300138518857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 947910380220400184691809 710932785165300138518857)
    ·
      refine ⟨533199588873975103889143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 710932785165300138518857 533199588873975103889143)
      ·
        refine ⟨799799383310962655833715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533199588873975103889143 799799383310962655833715)
        ·
          refine ⟨1199699074966443983750573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 799799383310962655833715 1199699074966443983750573)
          ·
            refine ⟨449887153112416493906465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1199699074966443983750573 449887153112416493906465)
            ·
              refine ⟨337415364834312370429849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 449887153112416493906465 337415364834312370429849)
              ·
                refine ⟨253061523625734277822387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 337415364834312370429849 253061523625734277822387)
                ·
                  refine ⟨379592285438601416733581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253061523625734277822387 379592285438601416733581)
                  ·
                    refine ⟨142347107039475531275093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379592285438601416733581 142347107039475531275093)
                    ·
                      rfl

theorem cell22_415830_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 2, 1, 3].length) (baseStart_415830 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415830 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415830 prefixEnd_415830 := by exact prefixLift 415830
  have htrace : WordTrace (prefixWord ++ tailWord_415830) baseStart_415830 baseEnd_415830 := by
    simpa [prefixWord, tailWord_415830, baseEnd_415830] using wordTrace_append hprefix tailTrace_415830
  have hstable : (prefixWord ++ tailWord_415830).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415830).length < 2 ^ (prefixWord ++ tailWord_415830).sum := by decide
  have hdescent : baseEnd_415830 < baseStart_415830 := by decide
  rcases family_descends (prefixWord ++ tailWord_415830) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415852 : List Nat := [2, 2, 1, 1, 3, 3, 2, 3, 2, 3]
def baseStart_415852 : Nat := 118140960795 + 415852 * 2 ^ 59
def prefixEnd_415852 : Nat := 4983230072969 + 3 ^ 40 * 415852 * 2
def baseEnd_415852 : Nat := 142354638089074807225025

theorem tailTrace_415852 : CollatzResearch.WordTrace tailWord_415852 prefixEnd_415852 142354638089074807225025 := by
  unfold tailWord_415852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7583684244723350356184905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10111578992964467141579873 7583684244723350356184905)
  ·
    refine ⟨5687763183542512767138679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7583684244723350356184905 5687763183542512767138679)
    ·
      refine ⟨8531644775313769150708019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5687763183542512767138679 8531644775313769150708019)
      ·
        refine ⟨12797467162970653726062029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8531644775313769150708019 12797467162970653726062029)
        ·
          refine ⟨4799050186113995147273261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12797467162970653726062029 4799050186113995147273261)
          ·
            refine ⟨1799643819792748180227473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4799050186113995147273261 1799643819792748180227473)
            ·
              refine ⟨1349732864844561135170605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1799643819792748180227473 1349732864844561135170605)
              ·
                refine ⟨506149824316710425688977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1349732864844561135170605 506149824316710425688977)
                ·
                  refine ⟨379612368237532819266733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506149824316710425688977 379612368237532819266733)
                  ·
                    refine ⟨142354638089074807225025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379612368237532819266733 142354638089074807225025)
                    ·
                      rfl

theorem cell22_415852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 3].length) (baseStart_415852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415852 prefixEnd_415852 := by exact prefixLift 415852
  have htrace : WordTrace (prefixWord ++ tailWord_415852) baseStart_415852 baseEnd_415852 := by
    simpa [prefixWord, tailWord_415852, baseEnd_415852] using wordTrace_append hprefix tailTrace_415852
  have hstable : (prefixWord ++ tailWord_415852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415852).length < 2 ^ (prefixWord ++ tailWord_415852).sum := by decide
  have hdescent : baseEnd_415852 < baseStart_415852 := by decide
  rcases family_descends (prefixWord ++ tailWord_415852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415886 : List Nat := [4, 1, 1, 3, 3, 2, 1, 2, 2, 3]
def baseStart_415886 : Nat := 118140960795 + 415886 * 2 ^ 59
def prefixEnd_415886 : Nat := 4983230072969 + 3 ^ 40 * 415886 * 2
def baseEnd_415886 : Nat := 142366276983910051874921

theorem tailTrace_415886 : CollatzResearch.WordTrace tailWord_415886 prefixEnd_415886 142366276983910051874921 := by
  unfold tailWord_415886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1896076071415440564888439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10112405714215683012738341 1896076071415440564888439)
  ·
    refine ⟨2844114107123160847332659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1896076071415440564888439 2844114107123160847332659)
    ·
      refine ⟨4266171160684741270998989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2844114107123160847332659 4266171160684741270998989)
      ·
        refine ⟨1599814185256777976624621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4266171160684741270998989 1599814185256777976624621)
        ·
          refine ⟨599930319471291741234233, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1599814185256777976624621 599930319471291741234233)
          ·
            refine ⟨449947739603468805925675, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 599930319471291741234233 449947739603468805925675)
            ·
              refine ⟨674921609405203208888513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 449947739603468805925675 674921609405203208888513)
              ·
                refine ⟨506191207053902406666385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 674921609405203208888513 506191207053902406666385)
                ·
                  refine ⟨379643405290426804999789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 506191207053902406666385 379643405290426804999789)
                  ·
                    refine ⟨142366276983910051874921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379643405290426804999789 142366276983910051874921)
                    ·
                      rfl

theorem cell22_415886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 2, 2, 3].length) (baseStart_415886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415886 prefixEnd_415886 := by exact prefixLift 415886
  have htrace : WordTrace (prefixWord ++ tailWord_415886) baseStart_415886 baseEnd_415886 := by
    simpa [prefixWord, tailWord_415886, baseEnd_415886] using wordTrace_append hprefix tailTrace_415886
  have hstable : (prefixWord ++ tailWord_415886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415886).length < 2 ^ (prefixWord ++ tailWord_415886).sum := by decide
  have hdescent : baseEnd_415886 < baseStart_415886 := by decide
  rcases family_descends (prefixWord ++ tailWord_415886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415948 : List Nat := [2, 2, 1, 6, 2, 1, 1, 1, 3, 3]
def baseStart_415948 : Nat := 118140960795 + 415948 * 2 ^ 59
def prefixEnd_415948 : Nat := 4983230072969 + 3 ^ 40 * 415948 * 2
def baseEnd_415948 : Nat := 142387500850962556824731

theorem tailTrace_415948 : CollatzResearch.WordTrace tailWord_415948 prefixEnd_415948 142387500850962556824731 := by
  unfold tailWord_415948
  simp only [CollatzResearch.WordTrace]
  refine ⟨7585434948549454553932249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10113913264732606071909665 7585434948549454553932249)
  ·
    refine ⟨5689076211412090915449187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7585434948549454553932249 5689076211412090915449187)
    ·
      refine ⟨8533614317118136373173781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5689076211412090915449187 8533614317118136373173781)
      ·
        refine ⟨400013171114912642492521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 8533614317118136373173781 400013171114912642492521)
        ·
          refine ⟨300009878336184481869391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 400013171114912642492521 300009878336184481869391)
          ·
            refine ⟨450014817504276722804087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 300009878336184481869391 450014817504276722804087)
            ·
              refine ⟨675022226256415084206131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450014817504276722804087 675022226256415084206131)
              ·
                refine ⟨1012533339384622626309197, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 675022226256415084206131 1012533339384622626309197)
                ·
                  refine ⟨379700002269233484865949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1012533339384622626309197 379700002269233484865949)
                  ·
                    refine ⟨142387500850962556824731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379700002269233484865949 142387500850962556824731)
                    ·
                      rfl

theorem cell22_415948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 2, 1, 1, 1, 3, 3].length) (baseStart_415948 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415948 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415948 prefixEnd_415948 := by exact prefixLift 415948
  have htrace : WordTrace (prefixWord ++ tailWord_415948) baseStart_415948 baseEnd_415948 := by
    simpa [prefixWord, tailWord_415948, baseEnd_415948] using wordTrace_append hprefix tailTrace_415948
  have hstable : (prefixWord ++ tailWord_415948).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415948).length < 2 ^ (prefixWord ++ tailWord_415948).sum := by decide
  have hdescent : baseEnd_415948 < baseStart_415948 := by decide
  rcases family_descends (prefixWord ++ tailWord_415948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_415985 : List Nat := [1, 2, 2, 2, 2, 1, 2, 3, 1, 6]
def baseStart_415985 : Nat := 118140960795 + 415985 * 2 ^ 59
def prefixEnd_415985 : Nat := 4983230072969 + 3 ^ 40 * 415985 * 2
def baseEnd_415985 : Nat := 142400166707106793649617

theorem tailTrace_415985 : CollatzResearch.WordTrace tailWord_415985 prefixEnd_415985 142400166707106793649617 := by
  unfold tailWord_415985
  simp only [CollatzResearch.WordTrace]
  refine ⟨15172219397964864426961409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10114812931976576284640939 15172219397964864426961409)
  ·
    refine ⟨11379164548473648320221057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15172219397964864426961409 11379164548473648320221057)
    ·
      refine ⟨8534373411355236240165793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11379164548473648320221057 8534373411355236240165793)
      ·
        refine ⟨6400780058516427180124345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8534373411355236240165793 6400780058516427180124345)
        ·
          refine ⟨4800585043887320385093259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6400780058516427180124345 4800585043887320385093259)
          ·
            refine ⟨7200877565830980577639889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4800585043887320385093259 7200877565830980577639889)
            ·
              refine ⟨5400658174373235433229917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7200877565830980577639889 5400658174373235433229917)
              ·
                refine ⟨2025246815389963287461219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5400658174373235433229917 2025246815389963287461219)
                ·
                  refine ⟨3037870223084944931191829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2025246815389963287461219 3037870223084944931191829)
                  ·
                    refine ⟨142400166707106793649617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3037870223084944931191829 142400166707106793649617)
                    ·
                      rfl

theorem cell22_415985_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 6].length) (baseStart_415985 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_415985 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_415985 prefixEnd_415985 := by exact prefixLift 415985
  have htrace : WordTrace (prefixWord ++ tailWord_415985) baseStart_415985 baseEnd_415985 := by
    simpa [prefixWord, tailWord_415985, baseEnd_415985] using wordTrace_append hprefix tailTrace_415985
  have hstable : (prefixWord ++ tailWord_415985).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_415985).length < 2 ^ (prefixWord ++ tailWord_415985).sum := by decide
  have hdescent : baseEnd_415985 < baseStart_415985 := by decide
  rcases family_descends (prefixWord ++ tailWord_415985) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416017 : List Nat := [1, 2, 2, 1, 1, 7, 1, 7]
def baseStart_416017 : Nat := 118140960795 + 416017 * 2 ^ 59
def prefixEnd_416017 : Nat := 4983230072969 + 3 ^ 40 * 416017 * 2
def baseEnd_416017 : Nat := 15823457884563264094391

theorem tailTrace_416017 : CollatzResearch.WordTrace tailWord_416017 prefixEnd_416017 15823457884563264094391 := by
  unfold tailWord_416017
  simp only [CollatzResearch.WordTrace]
  refine ⟨15173386533848933892126305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10115591022565955928084203 15173386533848933892126305)
  ·
    refine ⟨11380039900386700419094729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15173386533848933892126305 11380039900386700419094729)
    ·
      refine ⟨8535029925290025314321047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11380039900386700419094729 8535029925290025314321047)
      ·
        refine ⟨12802544887935037971481571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8535029925290025314321047 12802544887935037971481571)
        ·
          refine ⟨19203817331902556957222357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12802544887935037971481571 19203817331902556957222357)
          ·
            refine ⟨450089468716466178684899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 19203817331902556957222357 450089468716466178684899)
            ·
              refine ⟨675134203074699268027349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450089468716466178684899 675134203074699268027349)
              ·
                refine ⟨15823457884563264094391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 675134203074699268027349 15823457884563264094391)
                ·
                  rfl

theorem cell22_416017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 7, 1, 7].length) (baseStart_416017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416017 prefixEnd_416017 := by exact prefixLift 416017
  have htrace : WordTrace (prefixWord ++ tailWord_416017) baseStart_416017 baseEnd_416017 := by
    simpa [prefixWord, tailWord_416017, baseEnd_416017] using wordTrace_append hprefix tailTrace_416017
  have hstable : (prefixWord ++ tailWord_416017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416017).length < 2 ^ (prefixWord ++ tailWord_416017).sum := by decide
  have hdescent : baseEnd_416017 < baseStart_416017 := by decide
  rcases family_descends (prefixWord ++ tailWord_416017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416034 : List Nat := [3, 3, 1, 1, 3, 2, 3, 6]
def baseStart_416034 : Nat := 118140960795 + 416034 * 2 ^ 59
def prefixEnd_416034 : Nat := 4983230072969 + 3 ^ 40 * 416034 * 2
def baseEnd_416034 : Nat := 15824104489831888797163

theorem tailTrace_416034 : CollatzResearch.WordTrace tailWord_416034 prefixEnd_416034 15824104489831888797163 := by
  unfold tailWord_416034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3793501643696836448873789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10116004383191563863663437 3793501643696836448873789)
  ·
    refine ⟨1422563116386313668327671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3793501643696836448873789 1422563116386313668327671)
    ·
      refine ⟨2133844674579470502491507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422563116386313668327671 2133844674579470502491507)
      ·
        refine ⟨3200767011869205753737261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2133844674579470502491507 3200767011869205753737261)
        ·
          refine ⟨1200287629450952157651473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3200767011869205753737261 1200287629450952157651473)
          ·
            refine ⟨900215722088214118238605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1200287629450952157651473 900215722088214118238605)
            ·
              refine ⟨337580895783080294339477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 900215722088214118238605 337580895783080294339477)
              ·
                refine ⟨15824104489831888797163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 337580895783080294339477 15824104489831888797163)
                ·
                  rfl

theorem cell22_416034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_416034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416034 prefixEnd_416034 := by exact prefixLift 416034
  have htrace : WordTrace (prefixWord ++ tailWord_416034) baseStart_416034 baseEnd_416034 := by
    simpa [prefixWord, tailWord_416034, baseEnd_416034] using wordTrace_append hprefix tailTrace_416034
  have hstable : (prefixWord ++ tailWord_416034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416034).length < 2 ^ (prefixWord ++ tailWord_416034).sum := by decide
  have hdescent : baseEnd_416034 < baseStart_416034 := by decide
  rcases family_descends (prefixWord ++ tailWord_416034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416075 : List Nat := [1, 1, 1, 1, 3, 1, 1, 3, 2, 8]
def baseStart_416075 : Nat := 118140960795 + 416075 * 2 ^ 59
def prefixEnd_416075 : Nat := 4983230072969 + 3 ^ 40 * 416075 * 2
def baseEnd_416075 : Nat := 142430975546376558899341

theorem tailTrace_416075 : CollatzResearch.WordTrace tailWord_416075 prefixEnd_416075 142430975546376558899341 := by
  unfold tailWord_416075
  simp only [CollatzResearch.WordTrace]
  refine ⟨15175501967638809797737679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10117001311759206531825119 15175501967638809797737679)
  ·
    refine ⟨22763252951458214696606519, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15175501967638809797737679 22763252951458214696606519)
    ·
      refine ⟨34144879427187322044909779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22763252951458214696606519 34144879427187322044909779)
      ·
        refine ⟨51217319140780983067364669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34144879427187322044909779 51217319140780983067364669)
        ·
          refine ⟨19206494677792868650261751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51217319140780983067364669 19206494677792868650261751)
          ·
            refine ⟨28809742016689302975392627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19206494677792868650261751 28809742016689302975392627)
            ·
              refine ⟨43214613025033954463088941, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28809742016689302975392627 43214613025033954463088941)
              ·
                refine ⟨16205479884387732923658353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43214613025033954463088941 16205479884387732923658353)
                ·
                  refine ⟨12154109913290799692743765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16205479884387732923658353 12154109913290799692743765)
                  ·
                    refine ⟨142430975546376558899341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 12154109913290799692743765 142430975546376558899341)
                    ·
                      rfl

theorem cell22_416075_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 8].length) (baseStart_416075 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416075 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416075 prefixEnd_416075 := by exact prefixLift 416075
  have htrace : WordTrace (prefixWord ++ tailWord_416075) baseStart_416075 baseEnd_416075 := by
    simpa [prefixWord, tailWord_416075, baseEnd_416075] using wordTrace_append hprefix tailTrace_416075
  have hstable : (prefixWord ++ tailWord_416075).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416075).length < 2 ^ (prefixWord ++ tailWord_416075).sum := by decide
  have hdescent : baseEnd_416075 < baseStart_416075 := by decide
  rcases family_descends (prefixWord ++ tailWord_416075) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416109 : List Nat := [1, 5, 1, 1, 1, 2, 1, 5, 1, 4]
def baseStart_416109 : Nat := 118140960795 + 416109 * 2 ^ 59
def prefixEnd_416109 : Nat := 4983230072969 + 3 ^ 40 * 416109 * 2
def baseEnd_416109 : Nat := 142442614441211803549237

theorem tailTrace_416109 : CollatzResearch.WordTrace tailWord_416109 prefixEnd_416109 142442614441211803549237 := by
  unfold tailWord_416109
  simp only [CollatzResearch.WordTrace]
  refine ⟨15176742049515633604475381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10117828033010422402983587 15176742049515633604475381)
  ·
    refine ⟨1422819567142090650419567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15176742049515633604475381 1422819567142090650419567)
    ·
      refine ⟨2134229350713135975629351, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1422819567142090650419567 2134229350713135975629351)
      ·
        refine ⟨3201344026069703963444027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2134229350713135975629351 3201344026069703963444027)
        ·
          refine ⟨4802016039104555945166041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3201344026069703963444027 4802016039104555945166041)
          ·
            refine ⟨3601512029328416958874531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4802016039104555945166041 3601512029328416958874531)
            ·
              refine ⟨5402268043992625438311797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3601512029328416958874531 5402268043992625438311797)
              ·
                refine ⟨506462629124308634841731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5402268043992625438311797 506462629124308634841731)
                ·
                  refine ⟨759693943686462952262597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506462629124308634841731 759693943686462952262597)
                  ·
                    refine ⟨142442614441211803549237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759693943686462952262597 142442614441211803549237)
                    ·
                      rfl

theorem cell22_416109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 5, 1, 4].length) (baseStart_416109 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416109 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416109 prefixEnd_416109 := by exact prefixLift 416109
  have htrace : WordTrace (prefixWord ++ tailWord_416109) baseStart_416109 baseEnd_416109 := by
    simpa [prefixWord, tailWord_416109, baseEnd_416109] using wordTrace_append hprefix tailTrace_416109
  have hstable : (prefixWord ++ tailWord_416109).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416109).length < 2 ^ (prefixWord ++ tailWord_416109).sum := by decide
  have hdescent : baseEnd_416109 < baseStart_416109 := by decide
  rcases family_descends (prefixWord ++ tailWord_416109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416130 : List Nat := [3, 4, 2, 1, 2, 2, 2, 1, 5]
def baseStart_416130 : Nat := 118140960795 + 416130 * 2 ^ 59
def prefixEnd_416130 : Nat := 4983230072969 + 3 ^ 40 * 416130 * 2
def baseEnd_416130 : Nat := 47483267723458249591391

theorem tailTrace_416130 : CollatzResearch.WordTrace tailWord_416130 prefixEnd_416130 47483267723458249591391 := by
  unfold tailWord_416130
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794376995609888547747461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10118338654959702793993229 3794376995609888547747461)
  ·
    refine ⟨711445686676854102702649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3794376995609888547747461 711445686676854102702649)
    ·
      refine ⟨533584265007640577026987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 711445686676854102702649 533584265007640577026987)
      ·
        refine ⟨800376397511460865540481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533584265007640577026987 800376397511460865540481)
        ·
          refine ⟨600282298133595649155361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 800376397511460865540481 600282298133595649155361)
          ·
            refine ⟨450211723600196736866521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 600282298133595649155361 450211723600196736866521)
            ·
              refine ⟨337658792700147552649891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 450211723600196736866521 337658792700147552649891)
              ·
                refine ⟨506488189050221328974837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 337658792700147552649891 506488189050221328974837)
                ·
                  refine ⟨47483267723458249591391, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 506488189050221328974837 47483267723458249591391)
                  ·
                    rfl

theorem cell22_416130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_416130 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416130 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416130 prefixEnd_416130 := by exact prefixLift 416130
  have htrace : WordTrace (prefixWord ++ tailWord_416130) baseStart_416130 baseEnd_416130 := by
    simpa [prefixWord, tailWord_416130, baseEnd_416130] using wordTrace_append hprefix tailTrace_416130
  have hstable : (prefixWord ++ tailWord_416130).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416130).length < 2 ^ (prefixWord ++ tailWord_416130).sum := by decide
  have hdescent : baseEnd_416130 < baseStart_416130 := by decide
  rcases family_descends (prefixWord ++ tailWord_416130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416154 : List Nat := [3, 1, 1, 4, 1, 2, 1, 3, 2, 4]
def baseStart_416154 : Nat := 118140960795 + 416154 * 2 ^ 59
def prefixEnd_416154 : Nat := 4983230072969 + 3 ^ 40 * 416154 * 2
def baseEnd_416154 : Nat := 142458018860846686174099

theorem tailTrace_416154 : CollatzResearch.WordTrace tailWord_416154 prefixEnd_416154 142458018860846686174099 := by
  unfold tailWord_416154
  simp only [CollatzResearch.WordTrace]
  refine ⟨3794595833588151572465879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10118922222901737526575677 3794595833588151572465879)
  ·
    refine ⟨5691893750382227358698819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3794595833588151572465879 5691893750382227358698819)
    ·
      refine ⟨8537840625573341038048229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5691893750382227358698819 8537840625573341038048229)
      ·
        refine ⟨1600845117295001444634043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8537840625573341038048229 1600845117295001444634043)
        ·
          refine ⟨2401267675942502166951065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1600845117295001444634043 2401267675942502166951065)
          ·
            refine ⟨1800950756956876625213299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2401267675942502166951065 1800950756956876625213299)
            ·
              refine ⟨2701426135435314937819949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1800950756956876625213299 2701426135435314937819949)
              ·
                refine ⟨1013034800788243101682481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2701426135435314937819949 1013034800788243101682481)
                ·
                  refine ⟨759776100591182326261861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013034800788243101682481 759776100591182326261861)
                  ·
                    refine ⟨142458018860846686174099, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 759776100591182326261861 142458018860846686174099)
                    ·
                      rfl

theorem cell22_416154_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 3, 2, 4].length) (baseStart_416154 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416154 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416154 prefixEnd_416154 := by exact prefixLift 416154
  have htrace : WordTrace (prefixWord ++ tailWord_416154) baseStart_416154 baseEnd_416154 := by
    simpa [prefixWord, tailWord_416154, baseEnd_416154] using wordTrace_append hprefix tailTrace_416154
  have hstable : (prefixWord ++ tailWord_416154).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416154).length < 2 ^ (prefixWord ++ tailWord_416154).sum := by decide
  have hdescent : baseEnd_416154 < baseStart_416154 := by decide
  rcases family_descends (prefixWord ++ tailWord_416154) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416184 : List Nat := [2, 1, 2, 1, 2, 2, 1, 5, 3, 3]
def baseStart_416184 : Nat := 118140960795 + 416184 * 2 ^ 59
def prefixEnd_416184 : Nat := 4983230072969 + 3 ^ 40 * 416184 * 2
def baseEnd_416184 : Nat := 142468288473936607924007

theorem tailTrace_416184 : CollatzResearch.WordTrace tailWord_416184 prefixEnd_416184 142468288473936607924007 := by
  unfold tailWord_416184
  simp only [CollatzResearch.WordTrace]
  refine ⟨7589738762121960706727803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10119651682829280942303737 7589738762121960706727803)
  ·
    refine ⟨11384608143182941060091705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7589738762121960706727803 11384608143182941060091705)
    ·
      refine ⟨8538456107387205795068779, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11384608143182941060091705 8538456107387205795068779)
      ·
        refine ⟨12807684161080808692603169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8538456107387205795068779 12807684161080808692603169)
        ·
          refine ⟨9605763120810606519452377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12807684161080808692603169 9605763120810606519452377)
          ·
            refine ⟨7204322340607954889589283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9605763120810606519452377 7204322340607954889589283)
            ·
              refine ⟨10806483510911932334383925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7204322340607954889589283 10806483510911932334383925)
              ·
                refine ⟨1013107829147993656348493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10806483510911932334383925 1013107829147993656348493)
                ·
                  refine ⟨379915435930497621130685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1013107829147993656348493 379915435930497621130685)
                  ·
                    refine ⟨142468288473936607924007, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379915435930497621130685 142468288473936607924007)
                    ·
                      rfl

theorem cell22_416184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 5, 3, 3].length) (baseStart_416184 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416184 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416184 prefixEnd_416184 := by exact prefixLift 416184
  have htrace : WordTrace (prefixWord ++ tailWord_416184) baseStart_416184 baseEnd_416184 := by
    simpa [prefixWord, tailWord_416184, baseEnd_416184] using wordTrace_append hprefix tailTrace_416184
  have hstable : (prefixWord ++ tailWord_416184).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416184).length < 2 ^ (prefixWord ++ tailWord_416184).sum := by decide
  have hdescent : baseEnd_416184 < baseStart_416184 := by decide
  rcases family_descends (prefixWord ++ tailWord_416184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416218 : List Nat := [3, 1, 1, 2, 3, 1, 4, 3, 1, 3]
def baseStart_416218 : Nat := 118140960795 + 416218 * 2 ^ 59
def prefixEnd_416218 : Nat := 4983230072969 + 3 ^ 40 * 416218 * 2
def baseEnd_416218 : Nat := 142479927368771852573903

theorem tailTrace_416218 : CollatzResearch.WordTrace tailWord_416218 prefixEnd_416218 142479927368771852573903 := by
  unfold tailWord_416218
  simp only [CollatzResearch.WordTrace]
  refine ⟨3795179401530186305048327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10120478404080496813462205 3795179401530186305048327)
  ·
    refine ⟨5692769102295279457572491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3795179401530186305048327 5692769102295279457572491)
    ·
      refine ⟨8539153653442919186358737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5692769102295279457572491 8539153653442919186358737)
      ·
        refine ⟨6404365240082189389769053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8539153653442919186358737 6404365240082189389769053)
        ·
          refine ⟨2401636965030821021163395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6404365240082189389769053 2401636965030821021163395)
          ·
            refine ⟨3602455447546231531745093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2401636965030821021163395 3602455447546231531745093)
            ·
              refine ⟨675460396414918412202205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3602455447546231531745093 675460396414918412202205)
              ·
                refine ⟨253297648655594404575827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675460396414918412202205 253297648655594404575827)
                ·
                  refine ⟨379946472983391606863741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253297648655594404575827 379946472983391606863741)
                  ·
                    refine ⟨142479927368771852573903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379946472983391606863741 142479927368771852573903)
                    ·
                      rfl

theorem cell22_416218_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 3, 1, 3].length) (baseStart_416218 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416218 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416218 prefixEnd_416218 := by exact prefixLift 416218
  have htrace : WordTrace (prefixWord ++ tailWord_416218) baseStart_416218 baseEnd_416218 := by
    simpa [prefixWord, tailWord_416218, baseEnd_416218] using wordTrace_append hprefix tailTrace_416218
  have hstable : (prefixWord ++ tailWord_416218).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416218).length < 2 ^ (prefixWord ++ tailWord_416218).sum := by decide
  have hdescent : baseEnd_416218 < baseStart_416218 := by decide
  rcases family_descends (prefixWord ++ tailWord_416218) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416269 : List Nat := [1, 7, 1, 1, 1, 3, 1, 3, 1, 3]
def baseStart_416269 : Nat := 118140960795 + 416269 * 2 ^ 59
def prefixEnd_416269 : Nat := 4983230072969 + 3 ^ 40 * 416269 * 2
def baseEnd_416269 : Nat := 142497385711024719548747

theorem tailTrace_416269 : CollatzResearch.WordTrace tailWord_416269 prefixEnd_416269 142497385711024719548747 := by
  unfold tailWord_416269
  simp only [CollatzResearch.WordTrace]
  refine ⟨15182577728935980930299861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10121718485957320620199907 15182577728935980930299861)
  ·
    refine ⟨355841665521937053053903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 15182577728935980930299861 355841665521937053053903)
    ·
      refine ⟨533762498282905579580855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 355841665521937053053903 533762498282905579580855)
      ·
        refine ⟨800643747424358369371283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533762498282905579580855 800643747424358369371283)
        ·
          refine ⟨1200965621136537554056925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800643747424358369371283 1200965621136537554056925)
          ·
            refine ⟨450362107926201582771347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1200965621136537554056925 450362107926201582771347)
            ·
              refine ⟨675543161889302374157021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450362107926201582771347 675543161889302374157021)
              ·
                refine ⟨253328685708488390308883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675543161889302374157021 253328685708488390308883)
                ·
                  refine ⟨379993028562732585463325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253328685708488390308883 379993028562732585463325)
                  ·
                    refine ⟨142497385711024719548747, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 379993028562732585463325 142497385711024719548747)
                    ·
                      rfl

theorem cell22_416269_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 3, 1, 3].length) (baseStart_416269 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416269 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416269 prefixEnd_416269 := by exact prefixLift 416269
  have htrace : WordTrace (prefixWord ++ tailWord_416269) baseStart_416269 baseEnd_416269 := by
    simpa [prefixWord, tailWord_416269, baseEnd_416269] using wordTrace_append hprefix tailTrace_416269
  have hstable : (prefixWord ++ tailWord_416269).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416269).length < 2 ^ (prefixWord ++ tailWord_416269).sum := by decide
  have hdescent : baseEnd_416269 < baseStart_416269 := by decide
  rcases family_descends (prefixWord ++ tailWord_416269) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416291 : List Nat := [1, 1, 1, 4, 4, 1, 2, 1, 4, 3]
def baseStart_416291 : Nat := 118140960795 + 416291 * 2 ^ 59
def prefixEnd_416291 : Nat := 4983230072969 + 3 ^ 40 * 416291 * 2
def baseEnd_416291 : Nat := 142504916760623995498679

theorem tailTrace_416291 : CollatzResearch.WordTrace tailWord_416291 prefixEnd_416291 142504916760623995498679 := by
  unfold tailWord_416291
  simp only [CollatzResearch.WordTrace]
  refine ⟨15183380134856278687600727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10122253423237519125067151 15183380134856278687600727)
  ·
    refine ⟨22775070202284418031401091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15183380134856278687600727 22775070202284418031401091)
    ·
      refine ⟨34162605303426627047101637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22775070202284418031401091 34162605303426627047101637)
      ·
        refine ⟨6405488494392492571331557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34162605303426627047101637 6405488494392492571331557)
        ·
          refine ⟨1201029092698592357124667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6405488494392492571331557 1201029092698592357124667)
          ·
            refine ⟨1801543639047888535687001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201029092698592357124667 1801543639047888535687001)
            ·
              refine ⟨1351157729285916401765251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1801543639047888535687001 1351157729285916401765251)
              ·
                refine ⟨2026736593928874602647877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1351157729285916401765251 2026736593928874602647877)
                ·
                  refine ⟨380013111361663987996477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2026736593928874602647877 380013111361663987996477)
                  ·
                    refine ⟨142504916760623995498679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380013111361663987996477 142504916760623995498679)
                    ·
                      rfl

theorem cell22_416291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 4, 1, 2, 1, 4, 3].length) (baseStart_416291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416291 prefixEnd_416291 := by exact prefixLift 416291
  have htrace : WordTrace (prefixWord ++ tailWord_416291) baseStart_416291 baseEnd_416291 := by
    simpa [prefixWord, tailWord_416291, baseEnd_416291] using wordTrace_append hprefix tailTrace_416291
  have hstable : (prefixWord ++ tailWord_416291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416291).length < 2 ^ (prefixWord ++ tailWord_416291).sum := by decide
  have hdescent : baseEnd_416291 < baseStart_416291 := by decide
  rcases family_descends (prefixWord ++ tailWord_416291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416364 : List Nat := [2, 2, 1, 1, 3, 1, 3, 1, 1, 7]
def baseStart_416364 : Nat := 118140960795 + 416364 * 2 ^ 59
def prefixEnd_416364 : Nat := 4983230072969 + 3 ^ 40 * 416364 * 2
def baseEnd_416364 : Nat := 142529906152476138423455

theorem tailTrace_416364 : CollatzResearch.WordTrace tailWord_416364 prefixEnd_416364 142529906152476138423455 := by
  unfold tailWord_416364
  simp only [CollatzResearch.WordTrace]
  refine ⟨7593021331795906077504073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10124028442394541436672097 7593021331795906077504073)
  ·
    refine ⟨5694765998846929558128055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7593021331795906077504073 5694765998846929558128055)
    ·
      refine ⟨8542148998270394337192083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5694765998846929558128055 8542148998270394337192083)
      ·
        refine ⟨12813223497405591505788125, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8542148998270394337192083 12813223497405591505788125)
        ·
          refine ⟨4804958811527096814670547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12813223497405591505788125 4804958811527096814670547)
          ·
            refine ⟨7207438217290645222005821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4804958811527096814670547 7207438217290645222005821)
            ·
              refine ⟨2702789331483991958252183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7207438217290645222005821 2702789331483991958252183)
              ·
                refine ⟨4054183997225987937378275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2702789331483991958252183 4054183997225987937378275)
                ·
                  refine ⟨6081275995838981906067413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4054183997225987937378275 6081275995838981906067413)
                  ·
                    refine ⟨142529906152476138423455, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6081275995838981906067413 142529906152476138423455)
                    ·
                      rfl

theorem cell22_416364_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 7].length) (baseStart_416364 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416364 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416364 prefixEnd_416364 := by exact prefixLift 416364
  have htrace : WordTrace (prefixWord ++ tailWord_416364) baseStart_416364 baseEnd_416364 := by
    simpa [prefixWord, tailWord_416364, baseEnd_416364] using wordTrace_append hprefix tailTrace_416364
  have hstable : (prefixWord ++ tailWord_416364).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416364).length < 2 ^ (prefixWord ++ tailWord_416364).sum := by decide
  have hdescent : baseEnd_416364 < baseStart_416364 := by decide
  rcases family_descends (prefixWord ++ tailWord_416364) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416430 : List Nat := [4, 1, 4, 1, 1, 1, 1, 4, 1, 4]
def baseStart_416430 : Nat := 118140960795 + 416430 * 2 ^ 59
def prefixEnd_416430 : Nat := 4983230072969 + 3 ^ 40 * 416430 * 2
def baseEnd_416430 : Nat := 142552499301273966273253

theorem tailTrace_416430 : CollatzResearch.WordTrace tailWord_416430 prefixEnd_416430 142552499301273966273253 := by
  unfold tailWord_416430
  simp only [CollatzResearch.WordTrace]
  refine ⟨1898556235169088178363843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10125633254235136951273829 1898556235169088178363843)
  ·
    refine ⟨2847834352753632267545765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1898556235169088178363843 2847834352753632267545765)
    ·
      refine ⟨533968941141306050164831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2847834352753632267545765 533968941141306050164831)
      ·
        refine ⟨800953411711959075247247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 533968941141306050164831 800953411711959075247247)
        ·
          refine ⟨1201430117567938612870871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 800953411711959075247247 1201430117567938612870871)
          ·
            refine ⟨1802145176351907919306307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1201430117567938612870871 1802145176351907919306307)
            ·
              refine ⟨2703217764527861878959461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1802145176351907919306307 2703217764527861878959461)
              ·
                refine ⟨506853330848974102304899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2703217764527861878959461 506853330848974102304899)
                ·
                  refine ⟨760279996273461153457349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 506853330848974102304899 760279996273461153457349)
                  ·
                    refine ⟨142552499301273966273253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760279996273461153457349 142552499301273966273253)
                    ·
                      rfl

theorem cell22_416430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 4, 1, 4].length) (baseStart_416430 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416430 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416430 prefixEnd_416430 := by exact prefixLift 416430
  have htrace : WordTrace (prefixWord ++ tailWord_416430) baseStart_416430 baseEnd_416430 := by
    simpa [prefixWord, tailWord_416430, baseEnd_416430] using wordTrace_append hprefix tailTrace_416430
  have hstable : (prefixWord ++ tailWord_416430).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416430).length < 2 ^ (prefixWord ++ tailWord_416430).sum := by decide
  have hdescent : baseEnd_416430 < baseStart_416430 := by decide
  rcases family_descends (prefixWord ++ tailWord_416430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416441 : List Nat := [1, 2, 1, 4, 1, 1, 1, 5, 2, 4]
def baseStart_416441 : Nat := 118140960795 + 416441 * 2 ^ 59
def prefixEnd_416441 : Nat := 4983230072969 + 3 ^ 40 * 416441 * 2
def baseEnd_416441 : Nat := 142556264826073604248219

theorem tailTrace_416441 : CollatzResearch.WordTrace tailWord_416441 prefixEnd_416441 142556264826073604248219 := by
  unfold tailWord_416441
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188851084312854305561177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10125900722875236203707451 15188851084312854305561177)
  ·
    refine ⟨11391638313234640729170883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15188851084312854305561177 11391638313234640729170883)
    ·
      refine ⟨17087457469851961093756325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11391638313234640729170883 17087457469851961093756325)
      ·
        refine ⟨3203898275597242705079311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17087457469851961093756325 3203898275597242705079311)
        ·
          refine ⟨4805847413395864057618967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203898275597242705079311 4805847413395864057618967)
          ·
            refine ⟨7208771120093796086428451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4805847413395864057618967 7208771120093796086428451)
            ·
              refine ⟨10813156680140694129642677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7208771120093796086428451 10813156680140694129642677)
              ·
                refine ⟨1013733438763190074654001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 10813156680140694129642677 1013733438763190074654001)
                ·
                  refine ⟨760300079072392555990501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013733438763190074654001 760300079072392555990501)
                  ·
                    refine ⟨142556264826073604248219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760300079072392555990501 142556264826073604248219)
                    ·
                      rfl

theorem cell22_416441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 5, 2, 4].length) (baseStart_416441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416441 prefixEnd_416441 := by exact prefixLift 416441
  have htrace : WordTrace (prefixWord ++ tailWord_416441) baseStart_416441 baseEnd_416441 := by
    simpa [prefixWord, tailWord_416441, baseEnd_416441] using wordTrace_append hprefix tailTrace_416441
  have hstable : (prefixWord ++ tailWord_416441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416441).length < 2 ^ (prefixWord ++ tailWord_416441).sum := by decide
  have hdescent : baseEnd_416441 < baseStart_416441 := by decide
  rcases family_descends (prefixWord ++ tailWord_416441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416445 : List Nat := [1, 4, 1, 2, 1, 5, 1, 3, 4]
def baseStart_416445 : Nat := 118140960795 + 416445 * 2 ^ 59
def prefixEnd_416445 : Nat := 4983230072969 + 3 ^ 40 * 416445 * 2
def baseEnd_416445 : Nat := 47519211369272975716069

theorem tailTrace_416445 : CollatzResearch.WordTrace tailWord_416445 prefixEnd_416445 47519211369272975716069 := by
  unfold tailWord_416445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15188996976298362988706789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10125997984198908659137859 15188996976298362988706789)
  ·
    refine ⟨2847936933055943060382523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15188996976298362988706789 2847936933055943060382523)
    ·
      refine ⟨4271905399583914590573785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2847936933055943060382523 4271905399583914590573785)
      ·
        refine ⟨3203929049687935942930339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4271905399583914590573785 3203929049687935942930339)
        ·
          refine ⟨4805893574531903914395509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3203929049687935942930339 4805893574531903914395509)
          ·
            refine ⟨450552522612365991974579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4805893574531903914395509 450552522612365991974579)
            ·
              refine ⟨675828783918548987961869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 450552522612365991974579 675828783918548987961869)
              ·
                refine ⟨253435793969455870485701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 675828783918548987961869 253435793969455870485701)
                ·
                  refine ⟨47519211369272975716069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253435793969455870485701 47519211369272975716069)
                  ·
                    rfl

theorem cell22_416445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 5, 1, 3, 4].length) (baseStart_416445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416445 prefixEnd_416445 := by exact prefixLift 416445
  have htrace : WordTrace (prefixWord ++ tailWord_416445) baseStart_416445 baseEnd_416445 := by
    simpa [prefixWord, tailWord_416445, baseEnd_416445] using wordTrace_append hprefix tailTrace_416445
  have hstable : (prefixWord ++ tailWord_416445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416445).length < 2 ^ (prefixWord ++ tailWord_416445).sum := by decide
  have hdescent : baseEnd_416445 < baseStart_416445 := by decide
  rcases family_descends (prefixWord ++ tailWord_416445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416456 : List Nat := [2, 1, 3, 1, 2, 5, 8]
def baseStart_416456 : Nat := 118140960795 + 416456 * 2 ^ 59
def prefixEnd_416456 : Nat := 4983230072969 + 3 ^ 40 * 416456 * 2
def baseEnd_416456 : Nat := 5280051838245132041599

theorem tailTrace_416456 : CollatzResearch.WordTrace tailWord_416456 prefixEnd_416456 5280051838245132041599 := by
  unfold tailWord_416456
  simp only [CollatzResearch.WordTrace]
  refine ⟨7594699089629255933678611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10126265452839007911571481 7594699089629255933678611)
  ·
    refine ⟨11392048634443883900517917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7594699089629255933678611 11392048634443883900517917)
    ·
      refine ⟨4272018237916456462694219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11392048634443883900517917 4272018237916456462694219)
      ·
        refine ⟨6408027356874684694041329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272018237916456462694219 6408027356874684694041329)
        ·
          refine ⟨4806020517656013520530997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6408027356874684694041329 4806020517656013520530997)
          ·
            refine ⟨450564423530251267549781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4806020517656013520530997 450564423530251267549781)
            ·
              refine ⟨5280051838245132041599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 450564423530251267549781 5280051838245132041599)
              ·
                rfl

theorem cell22_416456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 5, 8].length) (baseStart_416456 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416456 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416456 prefixEnd_416456 := by exact prefixLift 416456
  have htrace : WordTrace (prefixWord ++ tailWord_416456) baseStart_416456 baseEnd_416456 := by
    simpa [prefixWord, tailWord_416456, baseEnd_416456] using wordTrace_append hprefix tailTrace_416456
  have hstable : (prefixWord ++ tailWord_416456).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416456).length < 2 ^ (prefixWord ++ tailWord_416456).sum := by decide
  have hdescent : baseEnd_416456 < baseStart_416456 := by decide
  rcases family_descends (prefixWord ++ tailWord_416456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416458 : List Nat := [3, 1, 2, 1, 4, 2, 1, 2, 2, 4]
def baseStart_416458 : Nat := 118140960795 + 416458 * 2 ^ 59
def prefixEnd_416458 : Nat := 4983230072969 + 3 ^ 40 * 416458 * 2
def baseEnd_416458 : Nat := 142562084273491226573167

theorem tailTrace_416458 : CollatzResearch.WordTrace tailWord_416458 prefixEnd_416458 142562084273491226573167 := by
  unfold tailWord_416458
  simp only [CollatzResearch.WordTrace]
  refine ⟨3797367781312816552232507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10126314083500844139286685 3797367781312816552232507)
  ·
    refine ⟨5696051671969224828348761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3797367781312816552232507 5696051671969224828348761)
    ·
      refine ⟨4272038753976918621261571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5696051671969224828348761 4272038753976918621261571)
      ·
        refine ⟨6408058130965377931892357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4272038753976918621261571 6408058130965377931892357)
        ·
          refine ⟨1201510899556008362229817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6408058130965377931892357 1201510899556008362229817)
          ·
            refine ⟨901133174667006271672363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201510899556008362229817 901133174667006271672363)
            ·
              refine ⟨1351699762000509407508545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901133174667006271672363 1351699762000509407508545)
              ·
                refine ⟨1013774821500382055631409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1351699762000509407508545 1013774821500382055631409)
                ·
                  refine ⟨760331116125286541723557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1013774821500382055631409 760331116125286541723557)
                  ·
                    refine ⟨142562084273491226573167, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760331116125286541723557 142562084273491226573167)
                    ·
                      rfl

theorem cell22_416458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 2, 2, 4].length) (baseStart_416458 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416458 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416458 prefixEnd_416458 := by exact prefixLift 416458
  have htrace : WordTrace (prefixWord ++ tailWord_416458) baseStart_416458 baseEnd_416458 := by
    simpa [prefixWord, tailWord_416458, baseEnd_416458] using wordTrace_append hprefix tailTrace_416458
  have hstable : (prefixWord ++ tailWord_416458).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416458).length < 2 ^ (prefixWord ++ tailWord_416458).sum := by decide
  have hdescent : baseEnd_416458 < baseStart_416458 := by decide
  rcases family_descends (prefixWord ++ tailWord_416458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416531 : List Nat := [1, 1, 1, 2, 1, 3, 3, 1, 5, 4]
def baseStart_416531 : Nat := 118140960795 + 416531 * 2 ^ 59
def prefixEnd_416531 : Nat := 4983230072969 + 3 ^ 40 * 416531 * 2
def baseEnd_416531 : Nat := 142587073665343369497943

theorem tailTrace_416531 : CollatzResearch.WordTrace tailWord_416531 prefixEnd_416531 142587073665343369497943 := by
  unfold tailWord_416531
  simp only [CollatzResearch.WordTrace]
  refine ⟨15192133653986799676337447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10128089102657866450891631 15192133653986799676337447)
  ·
    refine ⟨22788200480980199514506171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15192133653986799676337447 22788200480980199514506171)
    ·
      refine ⟨34182300721470299271759257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22788200480980199514506171 34182300721470299271759257)
      ·
        refine ⟨25636725541102724453819443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34182300721470299271759257 25636725541102724453819443)
        ·
          refine ⟨38455088311654086680729165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25636725541102724453819443 38455088311654086680729165)
          ·
            refine ⟨14420658116870282505273437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38455088311654086680729165 14420658116870282505273437)
            ·
              refine ⟨5407746793826355939477539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14420658116870282505273437 5407746793826355939477539)
              ·
                refine ⟨8111620190739533909216309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5407746793826355939477539 8111620190739533909216309)
                ·
                  refine ⟨760464392881831303989029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8111620190739533909216309 760464392881831303989029)
                  ·
                    refine ⟨142587073665343369497943, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760464392881831303989029 142587073665343369497943)
                    ·
                      rfl

theorem cell22_416531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 3, 1, 5, 4].length) (baseStart_416531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416531 prefixEnd_416531 := by exact prefixLift 416531
  have htrace : WordTrace (prefixWord ++ tailWord_416531) baseStart_416531 baseEnd_416531 := by
    simpa [prefixWord, tailWord_416531, baseEnd_416531] using wordTrace_append hprefix tailTrace_416531
  have hstable : (prefixWord ++ tailWord_416531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416531).length < 2 ^ (prefixWord ++ tailWord_416531).sum := by decide
  have hdescent : baseEnd_416531 < baseStart_416531 := by decide
  rcases family_descends (prefixWord ++ tailWord_416531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416565 : List Nat := [1, 3, 3, 1, 3, 2, 1, 3, 1, 4]
def baseStart_416565 : Nat := 118140960795 + 416565 * 2 ^ 59
def prefixEnd_416565 : Nat := 4983230072969 + 3 ^ 40 * 416565 * 2
def baseEnd_416565 : Nat := 142598712560178614147839

theorem tailTrace_416565 : CollatzResearch.WordTrace tailWord_416565 prefixEnd_416565 142598712560178614147839 := by
  unfold tailWord_416565
  simp only [CollatzResearch.WordTrace]
  refine ⟨15193373735863623483075149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10128915823909082322050099 15193373735863623483075149)
  ·
    refine ⟨5697515150948858806153181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15193373735863623483075149 5697515150948858806153181)
    ·
      refine ⟨2136568181605822052307443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5697515150948858806153181 2136568181605822052307443)
      ·
        refine ⟨3204852272408733078461165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2136568181605822052307443 3204852272408733078461165)
        ·
          refine ⟨1201819602153274904422937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3204852272408733078461165 1201819602153274904422937)
          ·
            refine ⟨901364701614956178317203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1201819602153274904422937 901364701614956178317203)
            ·
              refine ⟨1352047052422434267475805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 901364701614956178317203 1352047052422434267475805)
              ·
                refine ⟨507017644658412850303427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1352047052422434267475805 507017644658412850303427)
                ·
                  refine ⟨760526466987619275455141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507017644658412850303427 760526466987619275455141)
                  ·
                    refine ⟨142598712560178614147839, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 760526466987619275455141 142598712560178614147839)
                    ·
                      rfl

theorem cell22_416565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 3, 2, 1, 3, 1, 4].length) (baseStart_416565 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416565 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416565 prefixEnd_416565 := by exact prefixLift 416565
  have htrace : WordTrace (prefixWord ++ tailWord_416565) baseStart_416565 baseEnd_416565 := by
    simpa [prefixWord, tailWord_416565, baseEnd_416565] using wordTrace_append hprefix tailTrace_416565
  have hstable : (prefixWord ++ tailWord_416565).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416565).length < 2 ^ (prefixWord ++ tailWord_416565).sum := by decide
  have hdescent : baseEnd_416565 < baseStart_416565 := by decide
  rcases family_descends (prefixWord ++ tailWord_416565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416623 : List Nat := [1, 1, 2, 1, 3, 1, 1, 4, 5, 3]
def baseStart_416623 : Nat := 118140960795 + 416623 * 2 ^ 59
def prefixEnd_416623 : Nat := 4983230072969 + 3 ^ 40 * 416623 * 2
def baseEnd_416623 : Nat := 142618567145485796197661

theorem tailTrace_416623 : CollatzResearch.WordTrace tailWord_416623 prefixEnd_416623 142618567145485796197661 := by
  unfold tailWord_416623
  simp only [CollatzResearch.WordTrace]
  refine ⟨15195489169653499388686523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10130326113102332925791015 15195489169653499388686523)
  ·
    refine ⟨22793233754480249083029785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15195489169653499388686523 22793233754480249083029785)
    ·
      refine ⟨17094925315860186812272339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22793233754480249083029785 17094925315860186812272339)
      ·
        refine ⟨25642387973790280218408509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17094925315860186812272339 25642387973790280218408509)
        ·
          refine ⟨9615895490171355081903191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25642387973790280218408509 9615895490171355081903191)
          ·
            refine ⟨14423843235257032622854787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9615895490171355081903191 14423843235257032622854787)
            ·
              refine ⟨21635764852885548934282181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14423843235257032622854787 21635764852885548934282181)
              ·
                refine ⟨4056705909916040425177909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21635764852885548934282181 4056705909916040425177909)
                ·
                  refine ⟨380316179054628789860429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4056705909916040425177909 380316179054628789860429)
                  ·
                    refine ⟨142618567145485796197661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380316179054628789860429 142618567145485796197661)
                    ·
                      rfl

theorem cell22_416623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 1, 4, 5, 3].length) (baseStart_416623 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416623 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416623 prefixEnd_416623 := by exact prefixLift 416623
  have htrace : WordTrace (prefixWord ++ tailWord_416623) baseStart_416623 baseEnd_416623 := by
    simpa [prefixWord, tailWord_416623, baseEnd_416623] using wordTrace_append hprefix tailTrace_416623
  have hstable : (prefixWord ++ tailWord_416623).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416623).length < 2 ^ (prefixWord ++ tailWord_416623).sum := by decide
  have hdescent : baseEnd_416623 < baseStart_416623 := by decide
  rcases family_descends (prefixWord ++ tailWord_416623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416698 : List Nat := [3, 1, 1, 1, 2, 1, 4, 3, 6]
def baseStart_416698 : Nat := 118140960795 + 416698 * 2 ^ 59
def prefixEnd_416698 : Nat := 4983230072969 + 3 ^ 40 * 416698 * 2
def baseEnd_416698 : Nat := 47548080392736866857477

theorem tailTrace_416698 : CollatzResearch.WordTrace tailWord_416698 prefixEnd_416698 47548080392736866857477 := by
  unfold tailWord_416698
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799556161095446799416687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10132149762921191465111165 3799556161095446799416687)
  ·
    refine ⟨5699334241643170199125031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3799556161095446799416687 5699334241643170199125031)
    ·
      refine ⟨8549001362464755298687547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699334241643170199125031 8549001362464755298687547)
      ·
        refine ⟨12823502043697132948031321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8549001362464755298687547 12823502043697132948031321)
        ·
          refine ⟨9617626532772849711023491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12823502043697132948031321 9617626532772849711023491)
          ·
            refine ⟨14426439799159274566535237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9617626532772849711023491 14426439799159274566535237)
            ·
              refine ⟨2704957462342363981225357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14426439799159274566535237 2704957462342363981225357)
              ·
                refine ⟨1014359048378386492959509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2704957462342363981225357 1014359048378386492959509)
                ·
                  refine ⟨47548080392736866857477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1014359048378386492959509 47548080392736866857477)
                  ·
                    rfl

theorem cell22_416698_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 4, 3, 6].length) (baseStart_416698 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416698 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416698 prefixEnd_416698 := by exact prefixLift 416698
  have htrace : WordTrace (prefixWord ++ tailWord_416698) baseStart_416698 baseEnd_416698 := by
    simpa [prefixWord, tailWord_416698, baseEnd_416698] using wordTrace_append hprefix tailTrace_416698
  have hstable : (prefixWord ++ tailWord_416698).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416698).length < 2 ^ (prefixWord ++ tailWord_416698).sum := by decide
  have hdescent : baseEnd_416698 < baseStart_416698 := by decide
  rcases family_descends (prefixWord ++ tailWord_416698) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416730 : List Nat := [3, 1, 1, 2, 4, 1, 2, 2, 1, 5]
def baseStart_416730 : Nat := 118140960795 + 416730 * 2 ^ 59
def prefixEnd_416730 : Nat := 4983230072969 + 3 ^ 40 * 416730 * 2
def baseEnd_416730 : Nat := 142655195432173183772333

theorem tailTrace_416730 : CollatzResearch.WordTrace tailWord_416730 prefixEnd_416730 142655195432173183772333 := by
  unfold tailWord_416730
  simp only [CollatzResearch.WordTrace]
  refine ⟨3799847945066464165707911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10132927853510571108554429 3799847945066464165707911)
  ·
    refine ⟨5699771917599696248561867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3799847945066464165707911 5699771917599696248561867)
    ·
      refine ⟨8549657876399544372842801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5699771917599696248561867 8549657876399544372842801)
      ·
        refine ⟨6412243407299658279632101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8549657876399544372842801 6412243407299658279632101)
        ·
          refine ⟨1202295638868685927431019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6412243407299658279632101 1202295638868685927431019)
          ·
            refine ⟨1803443458303028891146529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1202295638868685927431019 1803443458303028891146529)
            ·
              refine ⟨1352582593727271668359897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1803443458303028891146529 1352582593727271668359897)
              ·
                refine ⟨1014436945295453751269923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1352582593727271668359897 1014436945295453751269923)
                ·
                  refine ⟨1521655417943180626904885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014436945295453751269923 1521655417943180626904885)
                  ·
                    refine ⟨142655195432173183772333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1521655417943180626904885 142655195432173183772333)
                    ·
                      rfl

theorem cell22_416730_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 1, 2, 2, 1, 5].length) (baseStart_416730 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416730 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416730 prefixEnd_416730 := by exact prefixLift 416730
  have htrace : WordTrace (prefixWord ++ tailWord_416730) baseStart_416730 baseEnd_416730 := by
    simpa [prefixWord, tailWord_416730, baseEnd_416730] using wordTrace_append hprefix tailTrace_416730
  have hstable : (prefixWord ++ tailWord_416730).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416730).length < 2 ^ (prefixWord ++ tailWord_416730).sum := by decide
  have hdescent : baseEnd_416730 < baseStart_416730 := by decide
  rcases family_descends (prefixWord ++ tailWord_416730) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416764 : List Nat := [2, 2, 2, 1, 2, 4, 3, 1, 2, 3]
def baseStart_416764 : Nat := 118140960795 + 416764 * 2 ^ 59
def prefixEnd_416764 : Nat := 4983230072969 + 3 ^ 40 * 416764 * 2
def baseEnd_416764 : Nat := 142666834327008428422229

theorem tailTrace_416764 : CollatzResearch.WordTrace tailWord_416764 prefixEnd_416764 142666834327008428422229 := by
  unfold tailWord_416764
  simp only [CollatzResearch.WordTrace]
  refine ⟨7600315931071340234784673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10133754574761786979712897 7600315931071340234784673)
  ·
    refine ⟨5700236948303505176088505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7600315931071340234784673 5700236948303505176088505)
    ·
      refine ⟨4275177711227628882066379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5700236948303505176088505 4275177711227628882066379)
      ·
        refine ⟨6412766566841443323099569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4275177711227628882066379 6412766566841443323099569)
        ·
          refine ⟨4809574925131082492324677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6412766566841443323099569 4809574925131082492324677)
          ·
            refine ⟨901795298462077967310877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4809574925131082492324677 901795298462077967310877)
            ·
              refine ⟨338173236923279237741579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 901795298462077967310877 338173236923279237741579)
              ·
                refine ⟨507259855384918856612369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 338173236923279237741579 507259855384918856612369)
                ·
                  refine ⟨380444891538689142459277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507259855384918856612369 380444891538689142459277)
                  ·
                    refine ⟨142666834327008428422229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380444891538689142459277 142666834327008428422229)
                    ·
                      rfl

theorem cell22_416764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 1, 2, 3].length) (baseStart_416764 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416764 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416764 prefixEnd_416764 := by exact prefixLift 416764
  have htrace : WordTrace (prefixWord ++ tailWord_416764) baseStart_416764 baseEnd_416764 := by
    simpa [prefixWord, tailWord_416764, baseEnd_416764] using wordTrace_append hprefix tailTrace_416764
  have hstable : (prefixWord ++ tailWord_416764).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416764).length < 2 ^ (prefixWord ++ tailWord_416764).sum := by decide
  have hdescent : baseEnd_416764 < baseStart_416764 := by decide
  rcases family_descends (prefixWord ++ tailWord_416764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416805 : List Nat := [1, 3, 1, 2, 2, 2, 2, 4, 5]
def baseStart_416805 : Nat := 118140960795 + 416805 * 2 ^ 59
def prefixEnd_416805 : Nat := 4983230072969 + 3 ^ 40 * 416805 * 2
def baseEnd_416805 : Nat := 47560289821632662715701

theorem tailTrace_416805 : CollatzResearch.WordTrace tailWord_416805 prefixEnd_416805 47560289821632662715701 := by
  unfold tailWord_416805
  simp only [CollatzResearch.WordTrace]
  refine ⟨15202127254994144471811869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10134751503329429647874579 15202127254994144471811869)
  ·
    refine ⟨5700797720622804176929451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15202127254994144471811869 5700797720622804176929451)
    ·
      refine ⟨8551196580934206265394177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5700797720622804176929451 8551196580934206265394177)
      ·
        refine ⟨6413397435700654699045633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8551196580934206265394177 6413397435700654699045633)
        ·
          refine ⟨4810048076775491024284225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6413397435700654699045633 4810048076775491024284225)
          ·
            refine ⟨3607536057581618268213169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4810048076775491024284225 3607536057581618268213169)
            ·
              refine ⟨2705652043186213701159877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3607536057581618268213169 2705652043186213701159877)
              ·
                refine ⟨507309758097415068967477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2705652043186213701159877 507309758097415068967477)
                ·
                  refine ⟨47560289821632662715701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 507309758097415068967477 47560289821632662715701)
                  ·
                    rfl

theorem cell22_416805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 2, 2, 4, 5].length) (baseStart_416805 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416805 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416805 prefixEnd_416805 := by exact prefixLift 416805
  have htrace : WordTrace (prefixWord ++ tailWord_416805) baseStart_416805 baseEnd_416805 := by
    simpa [prefixWord, tailWord_416805, baseEnd_416805] using wordTrace_append hprefix tailTrace_416805
  have hstable : (prefixWord ++ tailWord_416805).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416805).length < 2 ^ (prefixWord ++ tailWord_416805).sum := by decide
  have hdescent : baseEnd_416805 < baseStart_416805 := by decide
  rcases family_descends (prefixWord ++ tailWord_416805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416835 : List Nat := [1, 1, 1, 3, 1, 2, 5, 1, 3, 4]
def baseStart_416835 : Nat := 118140960795 + 416835 * 2 ^ 59
def prefixEnd_416835 : Nat := 4983230072969 + 3 ^ 40 * 416835 * 2
def baseEnd_416835 : Nat := 142691139077987909897011

theorem tailTrace_416835 : CollatzResearch.WordTrace tailWord_416835 prefixEnd_416835 142691139077987909897011 := by
  unfold tailWord_416835
  simp only [CollatzResearch.WordTrace]
  refine ⟨15203221444885459595403959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10135480963256973063602639 15203221444885459595403959)
  ·
    refine ⟨22804832167328189393105939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15203221444885459595403959 22804832167328189393105939)
    ·
      refine ⟨34207248250992284089658909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22804832167328189393105939 34207248250992284089658909)
      ·
        refine ⟨12827718094122106533622091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34207248250992284089658909 12827718094122106533622091)
        ·
          refine ⟨19241577141183159800433137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12827718094122106533622091 19241577141183159800433137)
          ·
            refine ⟨14431182855887369850324853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19241577141183159800433137 14431182855887369850324853)
            ·
              refine ⟨1352923392739440923467955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14431182855887369850324853 1352923392739440923467955)
              ·
                refine ⟨2029385089109161385201933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1352923392739440923467955 2029385089109161385201933)
                ·
                  refine ⟨761019408415935519450725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2029385089109161385201933 761019408415935519450725)
                  ·
                    refine ⟨142691139077987909897011, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 761019408415935519450725 142691139077987909897011)
                    ·
                      rfl

theorem cell22_416835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 1, 3, 4].length) (baseStart_416835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416835 prefixEnd_416835 := by exact prefixLift 416835
  have htrace : WordTrace (prefixWord ++ tailWord_416835) baseStart_416835 baseEnd_416835 := by
    simpa [prefixWord, tailWord_416835, baseEnd_416835] using wordTrace_append hprefix tailTrace_416835
  have hstable : (prefixWord ++ tailWord_416835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416835).length < 2 ^ (prefixWord ++ tailWord_416835).sum := by decide
  have hdescent : baseEnd_416835 < baseStart_416835 := by decide
  rcases family_descends (prefixWord ++ tailWord_416835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416852 : List Nat := [2, 4, 1, 1, 1, 1, 2, 5, 1, 4]
def baseStart_416852 : Nat := 118140960795 + 416852 * 2 ^ 59
def prefixEnd_416852 : Nat := 4983230072969 + 3 ^ 40 * 416852 * 2
def baseEnd_416852 : Nat := 142696958525405532221959

theorem tailTrace_416852 : CollatzResearch.WordTrace tailWord_416852 prefixEnd_416852 142696958525405532221959 := by
  unfold tailWord_416852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7601920742911935749386405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10135894323882580999181873 7601920742911935749386405)
  ·
    refine ⟨1425360139295987953009951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7601920742911935749386405 1425360139295987953009951)
    ·
      refine ⟨2138040208943981929514927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1425360139295987953009951 2138040208943981929514927)
      ·
        refine ⟨3207060313415972894272391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2138040208943981929514927 3207060313415972894272391)
        ·
          refine ⟨4810590470123959341408587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3207060313415972894272391 4810590470123959341408587)
          ·
            refine ⟨7215885705185939012112881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4810590470123959341408587 7215885705185939012112881)
            ·
              refine ⟨5411914278889454259084661, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7215885705185939012112881 5411914278889454259084661)
              ·
                refine ⟨507366963645886336789187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 5411914278889454259084661 507366963645886336789187)
                ·
                  refine ⟨761050445468829505183781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507366963645886336789187 761050445468829505183781)
                  ·
                    refine ⟨142696958525405532221959, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 761050445468829505183781 142696958525405532221959)
                    ·
                      rfl

theorem cell22_416852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 2, 5, 1, 4].length) (baseStart_416852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416852 prefixEnd_416852 := by exact prefixLift 416852
  have htrace : WordTrace (prefixWord ++ tailWord_416852) baseStart_416852 baseEnd_416852 := by
    simpa [prefixWord, tailWord_416852, baseEnd_416852] using wordTrace_append hprefix tailTrace_416852
  have hstable : (prefixWord ++ tailWord_416852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416852).length < 2 ^ (prefixWord ++ tailWord_416852).sum := by decide
  have hdescent : baseEnd_416852 < baseStart_416852 := by decide
  rcases family_descends (prefixWord ++ tailWord_416852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416880 : List Nat := [2, 1, 1, 1, 5, 1, 2, 2, 1, 6]
def baseStart_416880 : Nat := 118140960795 + 416880 * 2 ^ 59
def prefixEnd_416880 : Nat := 4983230072969 + 3 ^ 40 * 416880 * 2
def baseEnd_416880 : Nat := 142706543497622792521873

theorem tailTrace_416880 : CollatzResearch.WordTrace tailWord_416880 prefixEnd_416880 142706543497622792521873 := by
  unfold tailWord_416880
  simp only [CollatzResearch.WordTrace]
  refine ⟨7602431364861216140396047, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10136575153148288187194729 7602431364861216140396047)
  ·
    refine ⟨11403647047291824210594071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7602431364861216140396047 11403647047291824210594071)
    ·
      refine ⟨17105470570937736315891107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11403647047291824210594071 17105470570937736315891107)
      ·
        refine ⟨25658205856406604473836661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17105470570937736315891107 25658205856406604473836661)
        ·
          refine ⟨2405456799038119169422187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25658205856406604473836661 2405456799038119169422187)
          ·
            refine ⟨3608185198557178754133281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405456799038119169422187 3608185198557178754133281)
            ·
              refine ⟨2706138898917884065599961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3608185198557178754133281 2706138898917884065599961)
              ·
                refine ⟨2029604174188413049199971, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2706138898917884065599961 2029604174188413049199971)
                ·
                  refine ⟨3044406261282619573799957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029604174188413049199971 3044406261282619573799957)
                  ·
                    refine ⟨142706543497622792521873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3044406261282619573799957 142706543497622792521873)
                    ·
                      rfl

theorem cell22_416880_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 1, 2, 2, 1, 6].length) (baseStart_416880 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416880 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416880 prefixEnd_416880 := by exact prefixLift 416880
  have htrace : WordTrace (prefixWord ++ tailWord_416880) baseStart_416880 baseEnd_416880 := by
    simpa [prefixWord, tailWord_416880, baseEnd_416880] using wordTrace_append hprefix tailTrace_416880
  have hstable : (prefixWord ++ tailWord_416880).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416880).length < 2 ^ (prefixWord ++ tailWord_416880).sum := by decide
  have hdescent : baseEnd_416880 < baseStart_416880 := by decide
  rcases family_descends (prefixWord ++ tailWord_416880) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416882 : List Nat := [3, 2, 1, 2, 2, 1, 4, 1, 1, 5]
def baseStart_416882 : Nat := 118140960795 + 416882 * 2 ^ 59
def prefixEnd_416882 : Nat := 4983230072969 + 3 ^ 40 * 416882 * 2
def baseEnd_416882 : Nat := 142707228138495453971867

theorem tailTrace_416882 : CollatzResearch.WordTrace tailWord_416882 prefixEnd_416882 142707228138495453971867 := by
  unfold tailWord_416882
  simp only [CollatzResearch.WordTrace]
  refine ⟨3801233918928796655591225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10136623783810124414909933 3801233918928796655591225)
  ·
    refine ⟨2850925439196597491693419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3801233918928796655591225 2850925439196597491693419)
    ·
      refine ⟨4276388158794896237540129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2850925439196597491693419 4276388158794896237540129)
      ·
        refine ⟨3207291119096172178155097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4276388158794896237540129 3207291119096172178155097)
        ·
          refine ⟨2405468339322129133616323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3207291119096172178155097 2405468339322129133616323)
          ·
            refine ⟨3608202508983193700424485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2405468339322129133616323 3608202508983193700424485)
            ·
              refine ⟨676537970434348818829591, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3608202508983193700424485 676537970434348818829591)
              ·
                refine ⟨1014806955651523228244387, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676537970434348818829591 1014806955651523228244387)
                ·
                  refine ⟨1522210433477284842366581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1014806955651523228244387 1522210433477284842366581)
                  ·
                    refine ⟨142707228138495453971867, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1522210433477284842366581 142707228138495453971867)
                    ·
                      rfl

theorem cell22_416882_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 4, 1, 1, 5].length) (baseStart_416882 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416882 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416882 prefixEnd_416882 := by exact prefixLift 416882
  have htrace : WordTrace (prefixWord ++ tailWord_416882) baseStart_416882 baseEnd_416882 := by
    simpa [prefixWord, tailWord_416882, baseEnd_416882] using wordTrace_append hprefix tailTrace_416882
  have hstable : (prefixWord ++ tailWord_416882).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416882).length < 2 ^ (prefixWord ++ tailWord_416882).sum := by decide
  have hdescent : baseEnd_416882 < baseStart_416882 := by decide
  rcases family_descends (prefixWord ++ tailWord_416882) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416897 : List Nat := [1, 2, 4, 2, 2, 2, 1, 1, 1, 6]
def baseStart_416897 : Nat := 118140960795 + 416897 * 2 ^ 59
def prefixEnd_416897 : Nat := 4983230072969 + 3 ^ 40 * 416897 * 2
def baseEnd_416897 : Nat := 142712362945040414846821

theorem tailTrace_416897 : CollatzResearch.WordTrace tailWord_416897 prefixEnd_416897 142712362945040414846821 := by
  unfold tailWord_416897
  simp only [CollatzResearch.WordTrace]
  refine ⟨15205482770660844184160945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10136988513773896122773963 15205482770660844184160945)
  ·
    refine ⟨11404112077995633138120709, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15205482770660844184160945 11404112077995633138120709)
    ·
      refine ⟨2138271014624181213397633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11404112077995633138120709 2138271014624181213397633)
      ·
        refine ⟨1603703260968135910048225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138271014624181213397633 1603703260968135910048225)
        ·
          refine ⟨1202777445726101932536169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1603703260968135910048225 1202777445726101932536169)
          ·
            refine ⟨902083084294576449402127, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1202777445726101932536169 902083084294576449402127)
            ·
              refine ⟨1353124626441864674103191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902083084294576449402127 1353124626441864674103191)
              ·
                refine ⟨2029686939662797011154787, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1353124626441864674103191 2029686939662797011154787)
                ·
                  refine ⟨3044530409494195516732181, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2029686939662797011154787 3044530409494195516732181)
                  ·
                    refine ⟨142712362945040414846821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3044530409494195516732181 142712362945040414846821)
                    ·
                      rfl

theorem cell22_416897_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 2, 2, 2, 1, 1, 1, 6].length) (baseStart_416897 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416897 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416897 prefixEnd_416897 := by exact prefixLift 416897
  have htrace : WordTrace (prefixWord ++ tailWord_416897) baseStart_416897 baseEnd_416897 := by
    simpa [prefixWord, tailWord_416897, baseEnd_416897] using wordTrace_append hprefix tailTrace_416897
  have hstable : (prefixWord ++ tailWord_416897).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416897).length < 2 ^ (prefixWord ++ tailWord_416897).sum := by decide
  have hdescent : baseEnd_416897 < baseStart_416897 := by decide
  rcases family_descends (prefixWord ++ tailWord_416897) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416955 : List Nat := [1, 1, 1, 1, 1, 2, 4, 2, 4, 5]
def baseStart_416955 : Nat := 118140960795 + 416955 * 2 ^ 59
def prefixEnd_416955 : Nat := 4983230072969 + 3 ^ 40 * 416955 * 2
def baseEnd_416955 : Nat := 142732217530347596896643

theorem tailTrace_416955 : CollatzResearch.WordTrace tailWord_416955 prefixEnd_416955 142732217530347596896643 := by
  unfold tailWord_416955
  simp only [CollatzResearch.WordTrace]
  refine ⟨15207598204450720089772319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10138398802967146726514879 15207598204450720089772319)
  ·
    refine ⟨22811397306676080134658479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15207598204450720089772319 22811397306676080134658479)
    ·
      refine ⟨34217095960014120201987719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22811397306676080134658479 34217095960014120201987719)
      ·
        refine ⟨51325643940021180302981579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34217095960014120201987719 51325643940021180302981579)
        ·
          refine ⟨76988465910031770454472369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51325643940021180302981579 76988465910031770454472369)
          ·
            refine ⟨57741349432523827840854277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 76988465910031770454472369 57741349432523827840854277)
            ·
              refine ⟨10826503018598217720160177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57741349432523827840854277 10826503018598217720160177)
              ·
                refine ⟨8119877263948663290120133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10826503018598217720160177 8119877263948663290120133)
                ·
                  refine ⟨1522476986990374366897525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 8119877263948663290120133 1522476986990374366897525)
                  ·
                    refine ⟨142732217530347596896643, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1522476986990374366897525 142732217530347596896643)
                    ·
                      rfl

theorem cell22_416955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 4, 2, 4, 5].length) (baseStart_416955 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416955 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416955 prefixEnd_416955 := by exact prefixLift 416955
  have htrace : WordTrace (prefixWord ++ tailWord_416955) baseStart_416955 baseEnd_416955 := by
    simpa [prefixWord, tailWord_416955, baseEnd_416955] using wordTrace_append hprefix tailTrace_416955
  have hstable : (prefixWord ++ tailWord_416955).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416955).length < 2 ^ (prefixWord ++ tailWord_416955).sum := by decide
  have hdescent : baseEnd_416955 < baseStart_416955 := by decide
  rcases family_descends (prefixWord ++ tailWord_416955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_416978 : List Nat := [3, 2, 2, 2, 1, 1, 5, 2, 1, 3]
def baseStart_416978 : Nat := 118140960795 + 416978 * 2 ^ 59
def prefixEnd_416978 : Nat := 4983230072969 + 3 ^ 40 * 416978 * 2
def baseEnd_416978 : Nat := 142740090900383203571573

theorem tailTrace_416978 : CollatzResearch.WordTrace tailWord_416978 prefixEnd_416978 142740090900383203571573 := by
  unfold tailWord_416978
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802109270841848754464897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10138958055578263345239725 3802109270841848754464897)
  ·
    refine ⟨2851581953131386565848673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3802109270841848754464897 2851581953131386565848673)
    ·
      refine ⟨2138686464848539924386505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2851581953131386565848673 2138686464848539924386505)
      ·
        refine ⟨1604014848636404943289879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2138686464848539924386505 1604014848636404943289879)
        ·
          refine ⟨2406022272954607414934819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604014848636404943289879 2406022272954607414934819)
          ·
            refine ⟨3609033409431911122402229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2406022272954607414934819 3609033409431911122402229)
            ·
              refine ⟨338346882134241667725209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3609033409431911122402229 338346882134241667725209)
              ·
                refine ⟨253760161600681250793907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338346882134241667725209 253760161600681250793907)
                ·
                  refine ⟨380640242401021876190861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 253760161600681250793907 380640242401021876190861)
                  ·
                    refine ⟨142740090900383203571573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380640242401021876190861 142740090900383203571573)
                    ·
                      rfl

theorem cell22_416978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 2, 1, 3].length) (baseStart_416978 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_416978 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_416978 prefixEnd_416978 := by exact prefixLift 416978
  have htrace : WordTrace (prefixWord ++ tailWord_416978) baseStart_416978 baseEnd_416978 := by
    simpa [prefixWord, tailWord_416978, baseEnd_416978] using wordTrace_append hprefix tailTrace_416978
  have hstable : (prefixWord ++ tailWord_416978).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_416978).length < 2 ^ (prefixWord ++ tailWord_416978).sum := by decide
  have hdescent : baseEnd_416978 < baseStart_416978 := by decide
  rcases family_descends (prefixWord ++ tailWord_416978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417004 : List Nat := [2, 2, 1, 1, 2, 4, 3, 2, 1, 4]
def baseStart_417004 : Nat := 118140960795 + 417004 * 2 ^ 59
def prefixEnd_417004 : Nat := 4983230072969 + 3 ^ 40 * 417004 * 2
def baseEnd_417004 : Nat := 142748991231727802421493

theorem tailTrace_417004 : CollatzResearch.WordTrace tailWord_417004 prefixEnd_417004 142748991231727802421493 := by
  unfold tailWord_417004
  simp only [CollatzResearch.WordTrace]
  refine ⟨7604692690636600729153033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10139590254182134305537377 7604692690636600729153033)
  ·
    refine ⟨5703519517977450546864775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7604692690636600729153033 5703519517977450546864775)
    ·
      refine ⟨8555279276966175820297163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703519517977450546864775 8555279276966175820297163)
      ·
        refine ⟨12832918915449263730445745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8555279276966175820297163 12832918915449263730445745)
        ·
          refine ⟨9624689186586947797834309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12832918915449263730445745 9624689186586947797834309)
          ·
            refine ⟨1804629222485052712093933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9624689186586947797834309 1804629222485052712093933)
            ·
              refine ⟨676735958431894767035225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804629222485052712093933 676735958431894767035225)
              ·
                refine ⟨507551968823921075276419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676735958431894767035225 507551968823921075276419)
                ·
                  refine ⟨761327953235881612914629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 507551968823921075276419 761327953235881612914629)
                  ·
                    refine ⟨142748991231727802421493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 761327953235881612914629 142748991231727802421493)
                    ·
                      rfl

theorem cell22_417004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 4].length) (baseStart_417004 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417004 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417004 prefixEnd_417004 := by exact prefixLift 417004
  have htrace : WordTrace (prefixWord ++ tailWord_417004) baseStart_417004 baseEnd_417004 := by
    simpa [prefixWord, tailWord_417004, baseEnd_417004] using wordTrace_append hprefix tailTrace_417004
  have hstable : (prefixWord ++ tailWord_417004).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417004).length < 2 ^ (prefixWord ++ tailWord_417004).sum := by decide
  have hdescent : baseEnd_417004 < baseStart_417004 := by decide
  rcases family_descends (prefixWord ++ tailWord_417004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417017 : List Nat := [1, 2, 1, 3, 1, 1, 5, 2, 1, 5]
def baseStart_417017 : Nat := 118140960795 + 417017 * 2 ^ 59
def prefixEnd_417017 : Nat := 4983230072969 + 3 ^ 40 * 417017 * 2
def baseEnd_417017 : Nat := 142753441397400101846453

theorem tailTrace_417017 : CollatzResearch.WordTrace tailWord_417017 prefixEnd_417017 142753441397400101846453 := by
  unfold tailWord_417017
  simp only [CollatzResearch.WordTrace]
  refine ⟨15209859530226104678529305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10139906353484069785686203 15209859530226104678529305)
  ·
    refine ⟨11407394647669578508896979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15209859530226104678529305 11407394647669578508896979)
    ·
      refine ⟨17111091971504367763345469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11407394647669578508896979 17111091971504367763345469)
      ·
        refine ⟨6416659489314137911254551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17111091971504367763345469 6416659489314137911254551)
        ·
          refine ⟨9624989233971206866881827, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6416659489314137911254551 9624989233971206866881827)
          ·
            refine ⟨14437483850956810300322741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9624989233971206866881827 14437483850956810300322741)
            ·
              refine ⟨1353514111027200965655257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 14437483850956810300322741 1353514111027200965655257)
              ·
                refine ⟨1015135583270400724241443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1353514111027200965655257 1015135583270400724241443)
                ·
                  refine ⟨1522703374905601086362165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015135583270400724241443 1522703374905601086362165)
                  ·
                    refine ⟨142753441397400101846453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1522703374905601086362165 142753441397400101846453)
                    ·
                      rfl

theorem cell22_417017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 5, 2, 1, 5].length) (baseStart_417017 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417017 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417017 prefixEnd_417017 := by exact prefixLift 417017
  have htrace : WordTrace (prefixWord ++ tailWord_417017) baseStart_417017 baseEnd_417017 := by
    simpa [prefixWord, tailWord_417017, baseEnd_417017] using wordTrace_append hprefix tailTrace_417017
  have hstable : (prefixWord ++ tailWord_417017).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417017).length < 2 ^ (prefixWord ++ tailWord_417017).sum := by decide
  have hdescent : baseEnd_417017 < baseStart_417017 := by decide
  rcases family_descends (prefixWord ++ tailWord_417017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417036 : List Nat := [2, 2, 1, 2, 2, 3, 4, 2, 4]
def baseStart_417036 : Nat := 118140960795 + 417036 * 2 ^ 59
def prefixEnd_417036 : Nat := 4983230072969 + 3 ^ 40 * 417036 * 2
def baseEnd_417036 : Nat := 47586648495230128540465

theorem tailTrace_417036 : CollatzResearch.WordTrace tailWord_417036 prefixEnd_417036 47586648495230128540465 := by
  unfold tailWord_417036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7605276258578635461735481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10140368344771513948980641 7605276258578635461735481)
  ·
    refine ⟨5703957193933976596301611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7605276258578635461735481 5703957193933976596301611)
    ·
      refine ⟨8555935790900964894452417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5703957193933976596301611 8555935790900964894452417)
      ·
        refine ⟨6416951843175723670839313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8555935790900964894452417 6416951843175723670839313)
        ·
          refine ⟨4812713882381792753129485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6416951843175723670839313 4812713882381792753129485)
          ·
            refine ⟨1804767705893172282423557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4812713882381792753129485 1804767705893172282423557)
            ·
              refine ⟨338393944854969802954417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1804767705893172282423557 338393944854969802954417)
              ·
                refine ⟨253795458641227352215813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338393944854969802954417 253795458641227352215813)
                ·
                  refine ⟨47586648495230128540465, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253795458641227352215813 47586648495230128540465)
                  ·
                    rfl

theorem cell22_417036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 4, 2, 4].length) (baseStart_417036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417036 prefixEnd_417036 := by exact prefixLift 417036
  have htrace : WordTrace (prefixWord ++ tailWord_417036) baseStart_417036 baseEnd_417036 := by
    simpa [prefixWord, tailWord_417036, baseEnd_417036] using wordTrace_append hprefix tailTrace_417036
  have hstable : (prefixWord ++ tailWord_417036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417036).length < 2 ^ (prefixWord ++ tailWord_417036).sum := by decide
  have hdescent : baseEnd_417036 < baseStart_417036 := by decide
  rcases family_descends (prefixWord ++ tailWord_417036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417066 : List Nat := [3, 1, 4, 2, 1, 1, 3, 1, 2, 4]
def baseStart_417066 : Nat := 118140960795 + 417066 * 2 ^ 59
def prefixEnd_417066 : Nat := 4983230072969 + 3 ^ 40 * 417066 * 2
def baseEnd_417066 : Nat := 142770215098780307371303

theorem tailTrace_417066 : CollatzResearch.WordTrace tailWord_417066 prefixEnd_417066 142770215098780307371303 := by
  unfold tailWord_417066
  simp only [CollatzResearch.WordTrace]
  refine ⟨3802911676762146511765763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10141097804699057364708701 3802911676762146511765763)
  ·
    refine ⟨5704367515143219767648645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3802911676762146511765763 5704367515143219767648645)
    ·
      refine ⟨1069568909089353706434121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5704367515143219767648645 1069568909089353706434121)
      ·
        refine ⟨802176681817015279825591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1069568909089353706434121 802176681817015279825591)
        ·
          refine ⟨1203265022725522919738387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 802176681817015279825591 1203265022725522919738387)
          ·
            refine ⟨1804897534088284379607581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1203265022725522919738387 1804897534088284379607581)
            ·
              refine ⟨676836575283106642352843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1804897534088284379607581 676836575283106642352843)
              ·
                refine ⟨1015254862924659963529265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 676836575283106642352843 1015254862924659963529265)
                ·
                  refine ⟨761441147193494972646949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1015254862924659963529265 761441147193494972646949)
                  ·
                    refine ⟨142770215098780307371303, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 761441147193494972646949 142770215098780307371303)
                    ·
                      rfl

theorem cell22_417066_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 3, 1, 2, 4].length) (baseStart_417066 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417066 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417066 prefixEnd_417066 := by exact prefixLift 417066
  have htrace : WordTrace (prefixWord ++ tailWord_417066) baseStart_417066 baseEnd_417066 := by
    simpa [prefixWord, tailWord_417066, baseEnd_417066] using wordTrace_append hprefix tailTrace_417066
  have hstable : (prefixWord ++ tailWord_417066).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417066).length < 2 ^ (prefixWord ++ tailWord_417066).sum := by decide
  have hdescent : baseEnd_417066 < baseStart_417066 := by decide
  rcases family_descends (prefixWord ++ tailWord_417066) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417085 : List Nat := [1, 4, 1, 5, 1, 2, 1, 2, 2, 3]
def baseStart_417085 : Nat := 118140960795 + 417085 * 2 ^ 59
def prefixEnd_417085 : Nat := 4983230072969 + 3 ^ 40 * 417085 * 2
def baseEnd_417085 : Nat := 142776719187070591146245

theorem tailTrace_417085 : CollatzResearch.WordTrace tailWord_417085 prefixEnd_417085 142776719187070591146245 := by
  unfold tailWord_417085
  simp only [CollatzResearch.WordTrace]
  refine ⟨15212339693979752292004709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10141559795986501528003139 15212339693979752292004709)
  ·
    refine ⟨2852313692621203554750883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15212339693979752292004709 2852313692621203554750883)
    ·
      refine ⟨4278470538931805332126325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2852313692621203554750883 4278470538931805332126325)
      ·
        refine ⟨401106613024856749886843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4278470538931805332126325 401106613024856749886843)
        ·
          refine ⟨601659919537285124830265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 401106613024856749886843 601659919537285124830265)
          ·
            refine ⟨451244939652963843622699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 601659919537285124830265 451244939652963843622699)
            ·
              refine ⟨676867409479445765434049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 451244939652963843622699 676867409479445765434049)
              ·
                refine ⟨507650557109584324075537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 676867409479445765434049 507650557109584324075537)
                ·
                  refine ⟨380737917832188243056653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507650557109584324075537 380737917832188243056653)
                  ·
                    refine ⟨142776719187070591146245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380737917832188243056653 142776719187070591146245)
                    ·
                      rfl

theorem cell22_417085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 2, 2, 3].length) (baseStart_417085 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417085 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417085 prefixEnd_417085 := by exact prefixLift 417085
  have htrace : WordTrace (prefixWord ++ tailWord_417085) baseStart_417085 baseEnd_417085 := by
    simpa [prefixWord, tailWord_417085, baseEnd_417085] using wordTrace_append hprefix tailTrace_417085
  have hstable : (prefixWord ++ tailWord_417085).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417085).length < 2 ^ (prefixWord ++ tailWord_417085).sum := by decide
  have hdescent : baseEnd_417085 < baseStart_417085 := by decide
  rcases family_descends (prefixWord ++ tailWord_417085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417107 : List Nat := [1, 1, 1, 2, 1, 1, 5, 3, 2, 5]
def baseStart_417107 : Nat := 118140960795 + 417107 * 2 ^ 59
def prefixEnd_417107 : Nat := 4983230072969 + 3 ^ 40 * 417107 * 2
def baseEnd_417107 : Nat := 142784250236669867096177

theorem tailTrace_417107 : CollatzResearch.WordTrace tailWord_417107 prefixEnd_417107 142784250236669867096177 := by
  unfold tailWord_417107
  simp only [CollatzResearch.WordTrace]
  refine ⟨15213142099900050049305575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10142094733266700032870383 15213142099900050049305575)
  ·
    refine ⟨22819713149850075073958363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15213142099900050049305575 22819713149850075073958363)
    ·
      refine ⟨34229569724775112610937545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22819713149850075073958363 34229569724775112610937545)
      ·
        refine ⟨25672177293581334458203159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34229569724775112610937545 25672177293581334458203159)
        ·
          refine ⟨38508265940372001687304739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25672177293581334458203159 38508265940372001687304739)
          ·
            refine ⟨57762398910558002530957109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38508265940372001687304739 57762398910558002530957109)
            ·
              refine ⟨5415224897864812737277229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57762398910558002530957109 5415224897864812737277229)
              ·
                refine ⟨2030709336699304776478961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5415224897864812737277229 2030709336699304776478961)
                ·
                  refine ⟨1523032002524478582359221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 2030709336699304776478961 1523032002524478582359221)
                  ·
                    refine ⟨142784250236669867096177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1523032002524478582359221 142784250236669867096177)
                    ·
                      rfl

theorem cell22_417107_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 3, 2, 5].length) (baseStart_417107 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417107 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417107 prefixEnd_417107 := by exact prefixLift 417107
  have htrace : WordTrace (prefixWord ++ tailWord_417107) baseStart_417107 baseEnd_417107 := by
    simpa [prefixWord, tailWord_417107, baseEnd_417107] using wordTrace_append hprefix tailTrace_417107
  have hstable : (prefixWord ++ tailWord_417107).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417107).length < 2 ^ (prefixWord ++ tailWord_417107).sum := by decide
  have hdescent : baseEnd_417107 < baseStart_417107 := by decide
  rcases family_descends (prefixWord ++ tailWord_417107) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417137 : List Nat := [1, 2, 2, 2, 1, 2, 2, 2, 8]
def baseStart_417137 : Nat := 118140960795 + 417137 * 2 ^ 59
def prefixEnd_417137 : Nat := 4983230072969 + 3 ^ 40 * 417137 * 2
def baseEnd_417137 : Nat := 47598173283253262948695

theorem tailTrace_417137 : CollatzResearch.WordTrace tailWord_417137 prefixEnd_417137 47598173283253262948695 := by
  unfold tailWord_417137
  simp only [CollatzResearch.WordTrace]
  refine ⟨15214236289791365172897665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10142824193194243448598443 15214236289791365172897665)
  ·
    refine ⟨11410677217343523879673249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15214236289791365172897665 11410677217343523879673249)
    ·
      refine ⟨8558007913007642909754937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11410677217343523879673249 8558007913007642909754937)
      ·
        refine ⟨6418505934755732182316203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8558007913007642909754937 6418505934755732182316203)
        ·
          refine ⟨9627758902133598273474305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6418505934755732182316203 9627758902133598273474305)
          ·
            refine ⟨7220819176600198705105729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9627758902133598273474305 7220819176600198705105729)
            ·
              refine ⟨5415614382450149028829297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7220819176600198705105729 5415614382450149028829297)
              ·
                refine ⟨4061710786837611771621973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5415614382450149028829297 4061710786837611771621973)
                ·
                  refine ⟨47598173283253262948695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4061710786837611771621973 47598173283253262948695)
                  ·
                    rfl

theorem cell22_417137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 2, 2, 8].length) (baseStart_417137 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417137 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417137 prefixEnd_417137 := by exact prefixLift 417137
  have htrace : WordTrace (prefixWord ++ tailWord_417137) baseStart_417137 baseEnd_417137 := by
    simpa [prefixWord, tailWord_417137, baseEnd_417137] using wordTrace_append hprefix tailTrace_417137
  have hstable : (prefixWord ++ tailWord_417137).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417137).length < 2 ^ (prefixWord ++ tailWord_417137).sum := by decide
  have hdescent : baseEnd_417137 < baseStart_417137 := by decide
  rcases family_descends (prefixWord ++ tailWord_417137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417186 : List Nat := [3, 3, 1, 2, 1, 3, 1, 2, 1, 5]
def baseStart_417186 : Nat := 118140960795 + 417186 * 2 ^ 59
def prefixEnd_417186 : Nat := 4983230072969 + 3 ^ 40 * 417186 * 2
def baseEnd_417186 : Nat := 142811293551139994370935

theorem tailTrace_417186 : CollatzResearch.WordTrace tailWord_417186 prefixEnd_417186 142811293551139994370935 := by
  unfold tailWord_417186
  simp only [CollatzResearch.WordTrace]
  refine ⟨3804005866653461635357853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10144015644409231027620941 3804005866653461635357853)
  ·
    refine ⟨1426502199995048113259195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3804005866653461635357853 1426502199995048113259195)
    ·
      refine ⟨2139753299992572169888793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426502199995048113259195 2139753299992572169888793)
      ·
        refine ⟨1604814974994429127416595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2139753299992572169888793 1604814974994429127416595)
        ·
          refine ⟨2407222462491643691124893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1604814974994429127416595 2407222462491643691124893)
          ·
            refine ⟨902708423434366384171835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2407222462491643691124893 902708423434366384171835)
            ·
              refine ⟨1354062635151549576257753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 902708423434366384171835 1354062635151549576257753)
              ·
                refine ⟨1015546976363662182193315, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1354062635151549576257753 1015546976363662182193315)
                ·
                  refine ⟨1523320464545493273289973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1015546976363662182193315 1523320464545493273289973)
                  ·
                    refine ⟨142811293551139994370935, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1523320464545493273289973 142811293551139994370935)
                    ·
                      rfl

theorem cell22_417186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 3, 1, 2, 1, 5].length) (baseStart_417186 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417186 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417186 prefixEnd_417186 := by exact prefixLift 417186
  have htrace : WordTrace (prefixWord ++ tailWord_417186) baseStart_417186 baseEnd_417186 := by
    simpa [prefixWord, tailWord_417186, baseEnd_417186] using wordTrace_append hprefix tailTrace_417186
  have hstable : (prefixWord ++ tailWord_417186).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417186).length < 2 ^ (prefixWord ++ tailWord_417186).sum := by decide
  have hdescent : baseEnd_417186 < baseStart_417186 := by decide
  rcases family_descends (prefixWord ++ tailWord_417186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417205 : List Nat := [1, 3, 3, 2, 2, 3, 2, 2, 4]
def baseStart_417205 : Nat := 118140960795 + 417205 * 2 ^ 59
def prefixEnd_417205 : Nat := 4983230072969 + 3 ^ 40 * 417205 * 2
def baseEnd_417205 : Nat := 47605932546476759381959

theorem tailTrace_417205 : CollatzResearch.WordTrace tailWord_417205 prefixEnd_417205 47605932546476759381959 := by
  unfold tailWord_417205
  simp only [CollatzResearch.WordTrace]
  refine ⟨15216716453545012786373069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10144477635696675190915379 15216716453545012786373069)
  ·
    refine ⟨5706268670079379794889901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15216716453545012786373069 5706268670079379794889901)
    ·
      refine ⟨2139850751279767423083713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5706268670079379794889901 2139850751279767423083713)
      ·
        refine ⟨1604888063459825567312785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2139850751279767423083713 1604888063459825567312785)
        ·
          refine ⟨1203666047594869175484589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1604888063459825567312785 1203666047594869175484589)
          ·
            refine ⟨451374767848075940806721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1203666047594869175484589 451374767848075940806721)
            ·
              refine ⟨338531075886056955605041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 451374767848075940806721 338531075886056955605041)
              ·
                refine ⟨253898306914542716703781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 338531075886056955605041 253898306914542716703781)
                ·
                  refine ⟨47605932546476759381959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 253898306914542716703781 47605932546476759381959)
                  ·
                    rfl

theorem cell22_417205_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 3, 2, 2, 4].length) (baseStart_417205 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417205 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417205 prefixEnd_417205 := by exact prefixLift 417205
  have htrace : WordTrace (prefixWord ++ tailWord_417205) baseStart_417205 baseEnd_417205 := by
    simpa [prefixWord, tailWord_417205, baseEnd_417205] using wordTrace_append hprefix tailTrace_417205
  have hstable : (prefixWord ++ tailWord_417205).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417205).length < 2 ^ (prefixWord ++ tailWord_417205).sum := by decide
  have hdescent : baseEnd_417205 < baseStart_417205 := by decide
  rcases family_descends (prefixWord ++ tailWord_417205) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417214 : List Nat := [4, 2, 1, 1, 1, 1, 1, 2, 2, 7]
def baseStart_417214 : Nat := 118140960795 + 417214 * 2 ^ 59
def prefixEnd_417214 : Nat := 4983230072969 + 3 ^ 40 * 417214 * 2
def baseEnd_417214 : Nat := 142820878523357254670849

theorem tailTrace_417214 : CollatzResearch.WordTrace tailWord_417214 prefixEnd_417214 142820878523357254670849 := by
  unfold tailWord_417214
  simp only [CollatzResearch.WordTrace]
  refine ⟨1902130588814050915431337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10144696473674938215633797 1902130588814050915431337)
  ·
    refine ⟨1426597941610538186573503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1902130588814050915431337 1426597941610538186573503)
    ·
      refine ⟨2139896912415807279860255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1426597941610538186573503 2139896912415807279860255)
      ·
        refine ⟨3209845368623710919790383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2139896912415807279860255 3209845368623710919790383)
        ·
          refine ⟨4814768052935566379685575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3209845368623710919790383 4814768052935566379685575)
          ·
            refine ⟨7222152079403349569528363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4814768052935566379685575 7222152079403349569528363)
            ·
              refine ⟨10833228119105024354292545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7222152079403349569528363 10833228119105024354292545)
              ·
                refine ⟨8124921089328768265719409, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10833228119105024354292545 8124921089328768265719409)
                ·
                  refine ⟨6093690816996576199289557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8124921089328768265719409 6093690816996576199289557)
                  ·
                    refine ⟨142820878523357254670849, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6093690816996576199289557 142820878523357254670849)
                    ·
                      rfl

theorem cell22_417214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 1, 2, 2, 7].length) (baseStart_417214 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417214 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417214 prefixEnd_417214 := by exact prefixLift 417214
  have htrace : WordTrace (prefixWord ++ tailWord_417214) baseStart_417214 baseEnd_417214 := by
    simpa [prefixWord, tailWord_417214, baseEnd_417214] using wordTrace_append hprefix tailTrace_417214
  have hstable : (prefixWord ++ tailWord_417214).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417214).length < 2 ^ (prefixWord ++ tailWord_417214).sum := by decide
  have hdescent : baseEnd_417214 < baseStart_417214 := by decide
  rcases family_descends (prefixWord ++ tailWord_417214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417289 : List Nat := [1, 2, 1, 1, 3, 1, 3, 4, 6]
def baseStart_417289 : Nat := 118140960795 + 417289 * 2 ^ 59
def prefixEnd_417289 : Nat := 4983230072969 + 3 ^ 40 * 417289 * 2
def baseEnd_417289 : Nat := 47615517518694019681873

theorem tailTrace_417289 : CollatzResearch.WordTrace tailWord_417289 prefixEnd_417289 47615517518694019681873 := by
  unfold tailWord_417289
  simp only [CollatzResearch.WordTrace]
  refine ⟨15219780185240695132430921, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10146520123493796754953947 15219780185240695132430921)
  ·
    refine ⟨11414835138930521349323191, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15219780185240695132430921 11414835138930521349323191)
    ·
      refine ⟨17122252708395782023984787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11414835138930521349323191 17122252708395782023984787)
      ·
        refine ⟨25683379062593673035977181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17122252708395782023984787 25683379062593673035977181)
        ·
          refine ⟨9631267148472627388491443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25683379062593673035977181 9631267148472627388491443)
          ·
            refine ⟨14446900722708941082737165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9631267148472627388491443 14446900722708941082737165)
            ·
              refine ⟨5417587771015852906026437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14446900722708941082737165 5417587771015852906026437)
              ·
                refine ⟨1015797707065472419879957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5417587771015852906026437 1015797707065472419879957)
                ·
                  refine ⟨47615517518694019681873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1015797707065472419879957 47615517518694019681873)
                  ·
                    rfl

theorem cell22_417289_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 3, 4, 6].length) (baseStart_417289 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417289 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417289 prefixEnd_417289 := by exact prefixLift 417289
  have htrace : WordTrace (prefixWord ++ tailWord_417289) baseStart_417289 baseEnd_417289 := by
    simpa [prefixWord, tailWord_417289, baseEnd_417289] using wordTrace_append hprefix tailTrace_417289
  have hstable : (prefixWord ++ tailWord_417289).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417289).length < 2 ^ (prefixWord ++ tailWord_417289).sum := by decide
  have hdescent : baseEnd_417289 < baseStart_417289 := by decide
  rcases family_descends (prefixWord ++ tailWord_417289) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417338 : List Nat := [3, 1, 1, 1, 3, 2, 3, 3, 2, 3]
def baseStart_417338 : Nat := 118140960795 + 417338 * 2 ^ 59
def prefixEnd_417338 : Nat := 4983230072969 + 3 ^ 40 * 417338 * 2
def baseEnd_417338 : Nat := 142863326257462264570469

theorem tailTrace_417338 : CollatzResearch.WordTrace tailWord_417338 prefixEnd_417338 142863326257462264570469 := by
  unfold tailWord_417338
  simp only [CollatzResearch.WordTrace]
  refine ⟨3805391840515794125241167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10147711574708784333976445 3805391840515794125241167)
  ·
    refine ⟨5708087760773691187861751, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3805391840515794125241167 5708087760773691187861751)
    ·
      refine ⟨8562131641160536781792627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5708087760773691187861751 8562131641160536781792627)
      ·
        refine ⟨12843197461740805172688941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8562131641160536781792627 12843197461740805172688941)
        ·
          refine ⟨4816199048152801939758353, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12843197461740805172688941 4816199048152801939758353)
          ·
            refine ⟨3612149286114601454818765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4816199048152801939758353 3612149286114601454818765)
            ·
              refine ⟨1354555982292975545557037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3612149286114601454818765 1354555982292975545557037)
              ·
                refine ⟨507958493359865829583889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1354555982292975545557037 507958493359865829583889)
                ·
                  refine ⟨380968870019899372187917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 507958493359865829583889 380968870019899372187917)
                  ·
                    refine ⟨142863326257462264570469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 380968870019899372187917 142863326257462264570469)
                    ·
                      rfl

theorem cell22_417338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 2, 3, 3, 2, 3].length) (baseStart_417338 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417338 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417338 prefixEnd_417338 := by exact prefixLift 417338
  have htrace : WordTrace (prefixWord ++ tailWord_417338) baseStart_417338 baseEnd_417338 := by
    simpa [prefixWord, tailWord_417338, baseEnd_417338] using wordTrace_append hprefix tailTrace_417338
  have hstable : (prefixWord ++ tailWord_417338).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417338).length < 2 ^ (prefixWord ++ tailWord_417338).sum := by decide
  have hdescent : baseEnd_417338 < baseStart_417338 := by decide
  rcases family_descends (prefixWord ++ tailWord_417338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417381 : List Nat := [1, 3, 1, 3, 3, 1, 1, 1, 2, 6]
def baseStart_417381 : Nat := 118140960795 + 417381 * 2 ^ 59
def prefixEnd_417381 : Nat := 4983230072969 + 3 ^ 40 * 417381 * 2
def baseEnd_417381 : Nat := 142878046036224485745337

theorem tailTrace_417381 : CollatzResearch.WordTrace tailWord_417381 prefixEnd_417381 142878046036224485745337 := by
  unfold tailWord_417381
  simp only [CollatzResearch.WordTrace]
  refine ⟨15223135700907394844779997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10148757133938263229853331 15223135700907394844779997)
  ·
    refine ⟨5708675887840273066792499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15223135700907394844779997 5708675887840273066792499)
    ·
      refine ⟨8563013831760409600188749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5708675887840273066792499 8563013831760409600188749)
      ·
        refine ⟨3211130186910153600070781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8563013831760409600188749 3211130186910153600070781)
        ·
          refine ⟨1204173820091307600026543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3211130186910153600070781 1204173820091307600026543)
          ·
            refine ⟨1806260730136961400039815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204173820091307600026543 1806260730136961400039815)
            ·
              refine ⟨2709391095205442100059723, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1806260730136961400039815 2709391095205442100059723)
              ·
                refine ⟨4064086642808163150089585, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2709391095205442100059723 4064086642808163150089585)
                ·
                  refine ⟨3048064982106122362567189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4064086642808163150089585 3048064982106122362567189)
                  ·
                    refine ⟨142878046036224485745337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3048064982106122362567189 142878046036224485745337)
                    ·
                      rfl

theorem cell22_417381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 1, 1, 1, 2, 6].length) (baseStart_417381 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417381 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417381 prefixEnd_417381 := by exact prefixLift 417381
  have htrace : WordTrace (prefixWord ++ tailWord_417381) baseStart_417381 baseEnd_417381 := by
    simpa [prefixWord, tailWord_417381, baseEnd_417381] using wordTrace_append hprefix tailTrace_417381
  have hstable : (prefixWord ++ tailWord_417381).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417381).length < 2 ^ (prefixWord ++ tailWord_417381).sum := by decide
  have hdescent : baseEnd_417381 < baseStart_417381 := by decide
  rcases family_descends (prefixWord ++ tailWord_417381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417471 : List Nat := [1, 1, 2, 2, 2, 3, 1, 3, 1, 6]
def baseStart_417471 : Nat := 118140960795 + 417471 * 2 ^ 59
def prefixEnd_417471 : Nat := 4983230072969 + 3 ^ 40 * 417471 * 2
def baseEnd_417471 : Nat := 142908854875494250995061

theorem tailTrace_417471 : CollatzResearch.WordTrace tailWord_417471 prefixEnd_417471 142908854875494250995061 := by
  unfold tailWord_417471
  simp only [CollatzResearch.WordTrace]
  refine ⟨15226418270581340215556267, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10150945513720893477037511 15226418270581340215556267)
  ·
    refine ⟨22839627405872010323334401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15226418270581340215556267 22839627405872010323334401)
    ·
      refine ⟨17129720554404007742500801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22839627405872010323334401 17129720554404007742500801)
      ·
        refine ⟨12847290415803005806875601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17129720554404007742500801 12847290415803005806875601)
        ·
          refine ⟨9635467811852254355156701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12847290415803005806875601 9635467811852254355156701)
          ·
            refine ⟨3613300429444595383183763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9635467811852254355156701 3613300429444595383183763)
            ·
              refine ⟨5419950644166893074775645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3613300429444595383183763 5419950644166893074775645)
              ·
                refine ⟨2032481491562584903040867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5419950644166893074775645 2032481491562584903040867)
                ·
                  refine ⟨3048722237343877354561301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2032481491562584903040867 3048722237343877354561301)
                  ·
                    refine ⟨142908854875494250995061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3048722237343877354561301 142908854875494250995061)
                    ·
                      rfl

theorem cell22_417471_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 3, 1, 3, 1, 6].length) (baseStart_417471 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417471 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417471 prefixEnd_417471 := by exact prefixLift 417471
  have htrace : WordTrace (prefixWord ++ tailWord_417471) baseStart_417471 baseEnd_417471 := by
    simpa [prefixWord, tailWord_417471, baseEnd_417471] using wordTrace_append hprefix tailTrace_417471
  have hstable : (prefixWord ++ tailWord_417471).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417471).length < 2 ^ (prefixWord ++ tailWord_417471).sum := by decide
  have hdescent : baseEnd_417471 < baseStart_417471 := by decide
  rcases family_descends (prefixWord ++ tailWord_417471) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417490 : List Nat := [3, 2, 2, 2, 2, 1, 2, 1, 4, 3]
def baseStart_417490 : Nat := 118140960795 + 417490 * 2 ^ 59
def prefixEnd_417490 : Nat := 4983230072969 + 3 ^ 40 * 417490 * 2
def baseEnd_417490 : Nat := 142915358963784534770003

theorem tailTrace_417490 : CollatzResearch.WordTrace tailWord_417490 prefixEnd_417490 142915358963784534770003 := by
  unfold tailWord_417490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3806777814378126615124481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10151407505008337640331949 3806777814378126615124481)
  ·
    refine ⟨2855083360783594961343361, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3806777814378126615124481 2855083360783594961343361)
    ·
      refine ⟨2141312520587696221007521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2855083360783594961343361 2141312520587696221007521)
      ·
        refine ⟨1605984390440772165755641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2141312520587696221007521 1605984390440772165755641)
        ·
          refine ⟨1204488292830579124316731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1605984390440772165755641 1204488292830579124316731)
          ·
            refine ⟨1806732439245868686475097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1204488292830579124316731 1806732439245868686475097)
            ·
              refine ⟨1355049329434401514856323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1806732439245868686475097 1355049329434401514856323)
              ·
                refine ⟨2032573994151602272284485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1355049329434401514856323 2032573994151602272284485)
                ·
                  refine ⟨381107623903425426053341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2032573994151602272284485 381107623903425426053341)
                  ·
                    refine ⟨142915358963784534770003, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381107623903425426053341 142915358963784534770003)
                    ·
                      rfl

theorem cell22_417490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 2, 1, 2, 1, 4, 3].length) (baseStart_417490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417490 prefixEnd_417490 := by exact prefixLift 417490
  have htrace : WordTrace (prefixWord ++ tailWord_417490) baseStart_417490 baseEnd_417490 := by
    simpa [prefixWord, tailWord_417490, baseEnd_417490] using wordTrace_append hprefix tailTrace_417490
  have hstable : (prefixWord ++ tailWord_417490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417490).length < 2 ^ (prefixWord ++ tailWord_417490).sum := by decide
  have hdescent : baseEnd_417490 < baseStart_417490 := by decide
  rcases family_descends (prefixWord ++ tailWord_417490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417507 : List Nat := [1, 1, 1, 7, 2, 1, 1, 3, 2, 3]
def baseStart_417507 : Nat := 118140960795 + 417507 * 2 ^ 59
def prefixEnd_417507 : Nat := 4983230072969 + 3 ^ 40 * 417507 * 2
def baseEnd_417507 : Nat := 142921178411202157094951

theorem tailTrace_417507 : CollatzResearch.WordTrace tailWord_417507 prefixEnd_417507 142921178411202157094951 := by
  unfold tailWord_417507
  simp only [CollatzResearch.WordTrace]
  refine ⟨15227731298450918363866775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10151820865633945575911183 15227731298450918363866775)
  ·
    refine ⟨22841596947676377545800163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15227731298450918363866775 22841596947676377545800163)
    ·
      refine ⟨34262395421514566318700245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22841596947676377545800163 34262395421514566318700245)
      ·
        refine ⟨803024892691747648094537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 34262395421514566318700245 803024892691747648094537)
        ·
          refine ⟨602268669518810736070903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803024892691747648094537 602268669518810736070903)
          ·
            refine ⟨903403004278216104106355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602268669518810736070903 903403004278216104106355)
            ·
              refine ⟨1355104506417324156159533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 903403004278216104106355 1355104506417324156159533)
              ·
                refine ⟨508164189906496558559825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1355104506417324156159533 508164189906496558559825)
                ·
                  refine ⟨381123142429872418919869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508164189906496558559825 381123142429872418919869)
                  ·
                    refine ⟨142921178411202157094951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381123142429872418919869 142921178411202157094951)
                    ·
                      rfl

theorem cell22_417507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 2, 1, 1, 3, 2, 3].length) (baseStart_417507 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417507 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417507 prefixEnd_417507 := by exact prefixLift 417507
  have htrace : WordTrace (prefixWord ++ tailWord_417507) baseStart_417507 baseEnd_417507 := by
    simpa [prefixWord, tailWord_417507, baseEnd_417507] using wordTrace_append hprefix tailTrace_417507
  have hstable : (prefixWord ++ tailWord_417507).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417507).length < 2 ^ (prefixWord ++ tailWord_417507).sum := by decide
  have hdescent : baseEnd_417507 < baseStart_417507 := by decide
  rcases family_descends (prefixWord ++ tailWord_417507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417531 : List Nat := [1, 1, 1, 1, 1, 3, 1, 6, 7]
def baseStart_417531 : Nat := 118140960795 + 417531 * 2 ^ 59
def prefixEnd_417531 : Nat := 4983230072969 + 3 ^ 40 * 417531 * 2
def baseEnd_417531 : Nat := 47643131367224698164959

theorem tailTrace_417531 : CollatzResearch.WordTrace tailWord_417531 prefixEnd_417531 47643131367224698164959 := by
  unfold tailWord_417531
  simp only [CollatzResearch.WordTrace]
  refine ⟨15228606650363970462740447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10152404433575980308493631 15228606650363970462740447)
  ·
    refine ⟨22842909975545955694110671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15228606650363970462740447 22842909975545955694110671)
    ·
      refine ⟨34264364963318933541166007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22842909975545955694110671 34264364963318933541166007)
      ·
        refine ⟨51396547444978400311749011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34264364963318933541166007 51396547444978400311749011)
        ·
          refine ⟨77094821167467600467623517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51396547444978400311749011 77094821167467600467623517)
          ·
            refine ⟨28910557937800350175358819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77094821167467600467623517 28910557937800350175358819)
            ·
              refine ⟨43365836906700525263038229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28910557937800350175358819 43365836906700525263038229)
              ·
                refine ⟨2032773605001587121704917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 43365836906700525263038229 2032773605001587121704917)
                ·
                  refine ⟨47643131367224698164959, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2032773605001587121704917 47643131367224698164959)
                  ·
                    rfl

theorem cell22_417531_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 6, 7].length) (baseStart_417531 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417531 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417531 prefixEnd_417531 := by exact prefixLift 417531
  have htrace : WordTrace (prefixWord ++ tailWord_417531) baseStart_417531 baseEnd_417531 := by
    simpa [prefixWord, tailWord_417531, baseEnd_417531] using wordTrace_append hprefix tailTrace_417531
  have hstable : (prefixWord ++ tailWord_417531).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417531).length < 2 ^ (prefixWord ++ tailWord_417531).sum := by decide
  have hdescent : baseEnd_417531 < baseStart_417531 := by decide
  rcases family_descends (prefixWord ++ tailWord_417531) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417548 : List Nat := [2, 2, 1, 2, 2, 1, 3, 4, 5]
def baseStart_417548 : Nat := 118140960795 + 417548 * 2 ^ 59
def prefixEnd_417548 : Nat := 4983230072969 + 3 ^ 40 * 417548 * 2
def baseEnd_417548 : Nat := 47645071183030572273275

theorem tailTrace_417548 : CollatzResearch.WordTrace tailWord_417548 prefixEnd_417548 47645071183030572273275 := by
  unfold tailWord_417548
  simp only [CollatzResearch.WordTrace]
  refine ⟨7614613345651191183054649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10152817794201588244072865 7614613345651191183054649)
  ·
    refine ⟨5710960009238393387290987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7614613345651191183054649 5710960009238393387290987)
    ·
      refine ⟨8566440013857590080936481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5710960009238393387290987 8566440013857590080936481)
      ·
        refine ⟨6424830010393192560702361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8566440013857590080936481 6424830010393192560702361)
        ·
          refine ⟨4818622507794894420526771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6424830010393192560702361 4818622507794894420526771)
          ·
            refine ⟨7227933761692341630790157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4818622507794894420526771 7227933761692341630790157)
            ·
              refine ⟨2710475160634628111546309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7227933761692341630790157 2710475160634628111546309)
              ·
                refine ⟨508214092618992770914933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2710475160634628111546309 508214092618992770914933)
                ·
                  refine ⟨47645071183030572273275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508214092618992770914933 47645071183030572273275)
                  ·
                    rfl

theorem cell22_417548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 1, 3, 4, 5].length) (baseStart_417548 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417548 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417548 prefixEnd_417548 := by exact prefixLift 417548
  have htrace : WordTrace (prefixWord ++ tailWord_417548) baseStart_417548 baseEnd_417548 := by
    simpa [prefixWord, tailWord_417548, baseEnd_417548] using wordTrace_append hprefix tailTrace_417548
  have hstable : (prefixWord ++ tailWord_417548).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417548).length < 2 ^ (prefixWord ++ tailWord_417548).sum := by decide
  have hdescent : baseEnd_417548 < baseStart_417548 := by decide
  rcases family_descends (prefixWord ++ tailWord_417548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417610 : List Nat := [3, 1, 2, 1, 1, 1, 3, 6, 4]
def baseStart_417610 : Nat := 118140960795 + 417610 * 2 ^ 59
def prefixEnd_417610 : Nat := 4983230072969 + 3 ^ 40 * 417610 * 2
def baseEnd_417610 : Nat := 47652145805381407256545

theorem tailTrace_417610 : CollatzResearch.WordTrace tailWord_417610 prefixEnd_417610 47652145805381407256545 := by
  unfold tailWord_417610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3807872004269441738716571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10154325344718511303244189 3807872004269441738716571)
  ·
    refine ⟨5711808006404162608074857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3807872004269441738716571 5711808006404162608074857)
    ·
      refine ⟨4283856004803121956056143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5711808006404162608074857 4283856004803121956056143)
      ·
        refine ⟨6425784007204682934084215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4283856004803121956056143 6425784007204682934084215)
        ·
          refine ⟨9638676010807024401126323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6425784007204682934084215 9638676010807024401126323)
          ·
            refine ⟨14458014016210536601689485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9638676010807024401126323 14458014016210536601689485)
            ·
              refine ⟨5421755256078951225633557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14458014016210536601689485 5421755256078951225633557)
              ·
                refine ⟨254144777628700838701573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5421755256078951225633557 254144777628700838701573)
                ·
                  refine ⟨47652145805381407256545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254144777628700838701573 47652145805381407256545)
                  ·
                    rfl

theorem cell22_417610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 1, 3, 6, 4].length) (baseStart_417610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417610 prefixEnd_417610 := by exact prefixLift 417610
  have htrace : WordTrace (prefixWord ++ tailWord_417610) baseStart_417610 baseEnd_417610 := by
    simpa [prefixWord, tailWord_417610, baseEnd_417610] using wordTrace_append hprefix tailTrace_417610
  have hstable : (prefixWord ++ tailWord_417610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417610).length < 2 ^ (prefixWord ++ tailWord_417610).sum := by decide
  have hdescent : baseEnd_417610 < baseStart_417610 := by decide
  rcases family_descends (prefixWord ++ tailWord_417610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417640 : List Nat := [2, 1, 4, 2, 1, 1, 2, 3, 2, 4]
def baseStart_417640 : Nat := 118140960795 + 417640 * 2 ^ 59
def prefixEnd_417640 : Nat := 4983230072969 + 3 ^ 40 * 417640 * 2
def baseEnd_417640 : Nat := 142966707029234143519543

theorem tailTrace_417640 : CollatzResearch.WordTrace tailWord_417640 prefixEnd_417640 142966707029234143519543 := by
  unfold tailWord_417640
  simp only [CollatzResearch.WordTrace]
  refine ⟨7616291103484541039229187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10155054804646054718972249 7616291103484541039229187)
  ·
    refine ⟨11424436655226811558843781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7616291103484541039229187 11424436655226811558843781)
    ·
      refine ⟨2142081872855027167283209, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11424436655226811558843781 2142081872855027167283209)
      ·
        refine ⟨1606561404641270375462407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142081872855027167283209 1606561404641270375462407)
        ·
          refine ⟨2409842106961905563193611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606561404641270375462407 2409842106961905563193611)
          ·
            refine ⟨3614763160442858344790417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2409842106961905563193611 3614763160442858344790417)
            ·
              refine ⟨2711072370332143758592813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3614763160442858344790417 2711072370332143758592813)
              ·
                refine ⟨1016652138874553909472305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2711072370332143758592813 1016652138874553909472305)
                ·
                  refine ⟨762489104155915432104229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1016652138874553909472305 762489104155915432104229)
                  ·
                    refine ⟨142966707029234143519543, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762489104155915432104229 142966707029234143519543)
                    ·
                      rfl

theorem cell22_417640_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 3, 2, 4].length) (baseStart_417640 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417640 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417640 prefixEnd_417640 := by exact prefixLift 417640
  have htrace : WordTrace (prefixWord ++ tailWord_417640) baseStart_417640 baseEnd_417640 := by
    simpa [prefixWord, tailWord_417640, baseEnd_417640] using wordTrace_append hprefix tailTrace_417640
  have hstable : (prefixWord ++ tailWord_417640).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417640).length < 2 ^ (prefixWord ++ tailWord_417640).sum := by decide
  have hdescent : baseEnd_417640 < baseStart_417640 := by decide
  rcases family_descends (prefixWord ++ tailWord_417640) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417717 : List Nat := [1, 3, 3, 2, 1, 3, 2, 2, 5]
def baseStart_417717 : Nat := 118140960795 + 417717 * 2 ^ 59
def prefixEnd_417717 : Nat := 4983230072969 + 3 ^ 40 * 417717 * 2
def baseEnd_417717 : Nat := 47664355234277203114769

theorem tailTrace_417717 : CollatzResearch.WordTrace tailWord_417717 prefixEnd_417717 47664355234277203114769 := by
  unfold tailWord_417717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15235390627690124229011405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10156927085126749486007603 15235390627690124229011405)
  ·
    refine ⟨5713271485383796585879277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15235390627690124229011405 5713271485383796585879277)
    ·
      refine ⟨2142476807018923719704729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5713271485383796585879277 2142476807018923719704729)
      ·
        refine ⟨1606857605264192789778547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2142476807018923719704729 1606857605264192789778547)
        ·
          refine ⟨2410286407896289184667821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1606857605264192789778547 2410286407896289184667821)
          ·
            refine ⟨903857402961108444250433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2410286407896289184667821 903857402961108444250433)
            ·
              refine ⟨677893052220831333187825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 903857402961108444250433 677893052220831333187825)
              ·
                refine ⟨508419789165623499890869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 677893052220831333187825 508419789165623499890869)
                ·
                  refine ⟨47664355234277203114769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508419789165623499890869 47664355234277203114769)
                  ·
                    rfl

theorem cell22_417717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 3, 2, 2, 5].length) (baseStart_417717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417717 prefixEnd_417717 := by exact prefixLift 417717
  have htrace : WordTrace (prefixWord ++ tailWord_417717) baseStart_417717 baseEnd_417717 := by
    simpa [prefixWord, tailWord_417717, baseEnd_417717] using wordTrace_append hprefix tailTrace_417717
  have hstable : (prefixWord ++ tailWord_417717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417717).length < 2 ^ (prefixWord ++ tailWord_417717).sum := by decide
  have hdescent : baseEnd_417717 < baseStart_417717 := by decide
  rcases family_descends (prefixWord ++ tailWord_417717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417775 : List Nat := [1, 1, 2, 1, 4, 2, 2, 1, 4, 4]
def baseStart_417775 : Nat := 118140960795 + 417775 * 2 ^ 59
def prefixEnd_417775 : Nat := 4983230072969 + 3 ^ 40 * 417775 * 2
def baseEnd_417775 : Nat := 143012920288138791394129

theorem tailTrace_417775 : CollatzResearch.WordTrace tailWord_417775 prefixEnd_417775 143012920288138791394129 := by
  unfold tailWord_417775
  simp only [CollatzResearch.WordTrace]
  refine ⟨15237506061480000134622779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10158337374320000089748519 15237506061480000134622779)
  ·
    refine ⟨22856259092220000201934169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15237506061480000134622779 22856259092220000201934169)
    ·
      refine ⟨17142194319165000151450627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22856259092220000201934169 17142194319165000151450627)
      ·
        refine ⟨25713291478747500227175941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17142194319165000151450627 25713291478747500227175941)
        ·
          refine ⟨4821242152265156292595489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25713291478747500227175941 4821242152265156292595489)
          ·
            refine ⟨3615931614198867219446617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4821242152265156292595489 3615931614198867219446617)
            ·
              refine ⟨2711948710649150414584963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3615931614198867219446617 2711948710649150414584963)
              ·
                refine ⟨4067923065973725621877445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2711948710649150414584963 4067923065973725621877445)
                ·
                  refine ⟨762735574870073554102021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4067923065973725621877445 762735574870073554102021)
                  ·
                    refine ⟨143012920288138791394129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 762735574870073554102021 143012920288138791394129)
                    ·
                      rfl

theorem cell22_417775_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 2, 2, 1, 4, 4].length) (baseStart_417775 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417775 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417775 prefixEnd_417775 := by exact prefixLift 417775
  have htrace : WordTrace (prefixWord ++ tailWord_417775) baseStart_417775 baseEnd_417775 := by
    simpa [prefixWord, tailWord_417775, baseEnd_417775] using wordTrace_append hprefix tailTrace_417775
  have hstable : (prefixWord ++ tailWord_417775).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417775).length < 2 ^ (prefixWord ++ tailWord_417775).sum := by decide
  have hdescent : baseEnd_417775 < baseStart_417775 := by decide
  rcases family_descends (prefixWord ++ tailWord_417775) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417850 : List Nat := [3, 1, 1, 1, 3, 1, 1, 3, 1, 7]
def baseStart_417850 : Nat := 118140960795 + 417850 * 2 ^ 59
def prefixEnd_417850 : Nat := 4983230072969 + 3 ^ 40 * 417850 * 2
def baseEnd_417850 : Nat := 143038594320863595768899

theorem tailTrace_417850 : CollatzResearch.WordTrace tailWord_417850 prefixEnd_417850 143038594320863595768899 := by
  unfold tailWord_417850
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810060384052071985900751, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10160161024138858629068669 3810060384052071985900751)
  ·
    refine ⟨5715090576078107978851127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810060384052071985900751 5715090576078107978851127)
    ·
      refine ⟨8572635864117161968276691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5715090576078107978851127 8572635864117161968276691)
      ·
        refine ⟨12858953796175742952415037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8572635864117161968276691 12858953796175742952415037)
        ·
          refine ⟨4822107673565903607155639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12858953796175742952415037 4822107673565903607155639)
          ·
            refine ⟨7233161510348855410733459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4822107673565903607155639 7233161510348855410733459)
            ·
              refine ⟨10849742265523283116100189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7233161510348855410733459 10849742265523283116100189)
              ·
                refine ⟨4068653349571231168537571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10849742265523283116100189 4068653349571231168537571)
                ·
                  refine ⟨6102980024356846752806357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4068653349571231168537571 6102980024356846752806357)
                  ·
                    refine ⟨143038594320863595768899, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6102980024356846752806357 143038594320863595768899)
                    ·
                      rfl

theorem cell22_417850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 1, 3, 1, 7].length) (baseStart_417850 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417850 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417850 prefixEnd_417850 := by exact prefixLift 417850
  have htrace : WordTrace (prefixWord ++ tailWord_417850) baseStart_417850 baseEnd_417850 := by
    simpa [prefixWord, tailWord_417850, baseEnd_417850] using wordTrace_append hprefix tailTrace_417850
  have hstable : (prefixWord ++ tailWord_417850).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417850).length < 2 ^ (prefixWord ++ tailWord_417850).sum := by decide
  have hdescent : baseEnd_417850 < baseStart_417850 := by decide
  rcases family_descends (prefixWord ++ tailWord_417850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417852 : List Nat := [2, 2, 2, 2, 2, 1, 3, 3, 5]
def baseStart_417852 : Nat := 118140960795 + 417852 * 2 ^ 59
def prefixEnd_417852 : Nat := 4983230072969 + 3 ^ 40 * 417852 * 2
def baseEnd_417852 : Nat := 47679759653912085739631

theorem tailTrace_417852 : CollatzResearch.WordTrace tailWord_417852 prefixEnd_417852 47679759653912085739631 := by
  unfold tailWord_417852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7620157241100521142587905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10160209654800694856783873 7620157241100521142587905)
  ·
    refine ⟨5715117930825390856940929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7620157241100521142587905 5715117930825390856940929)
    ·
      refine ⟨4286338448119043142705697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5715117930825390856940929 4286338448119043142705697)
      ·
        refine ⟨3214753836089282357029273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4286338448119043142705697 3214753836089282357029273)
        ·
          refine ⟨2411065377066961767771955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3214753836089282357029273 2411065377066961767771955)
          ·
            refine ⟨3616598065600442651657933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2411065377066961767771955 3616598065600442651657933)
            ·
              refine ⟨1356224274600165994371725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3616598065600442651657933 1356224274600165994371725)
              ·
                refine ⟨508584102975062247889397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1356224274600165994371725 508584102975062247889397)
                ·
                  refine ⟨47679759653912085739631, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508584102975062247889397 47679759653912085739631)
                  ·
                    rfl

theorem cell22_417852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 3, 3, 5].length) (baseStart_417852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417852 prefixEnd_417852 := by exact prefixLift 417852
  have htrace : WordTrace (prefixWord ++ tailWord_417852) baseStart_417852 baseEnd_417852 := by
    simpa [prefixWord, tailWord_417852, baseEnd_417852] using wordTrace_append hprefix tailTrace_417852
  have hstable : (prefixWord ++ tailWord_417852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417852).length < 2 ^ (prefixWord ++ tailWord_417852).sum := by decide
  have hdescent : baseEnd_417852 < baseStart_417852 := by decide
  rcases family_descends (prefixWord ++ tailWord_417852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417912 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 6, 3]
def baseStart_417912 : Nat := 118140960795 + 417912 * 2 ^ 59
def prefixEnd_417912 : Nat := 4983230072969 + 3 ^ 40 * 417912 * 2
def baseEnd_417912 : Nat := 143059818187916100718709

theorem tailTrace_417912 : CollatzResearch.WordTrace tailWord_417912 prefixEnd_417912 143059818187916100718709 := by
  unfold tailWord_417912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7621251430991836266179995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10161668574655781688239993 7621251430991836266179995)
  ·
    refine ⟨11431877146487754399269993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7621251430991836266179995 11431877146487754399269993)
    ·
      refine ⟨8573907859865815799452495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11431877146487754399269993 8573907859865815799452495)
      ·
        refine ⟨12860861789798723699178743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8573907859865815799452495 12860861789798723699178743)
        ·
          refine ⟨19291292684698085548768115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12860861789798723699178743 19291292684698085548768115)
          ·
            refine ⟨28936939027047128323152173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19291292684698085548768115 28936939027047128323152173)
            ·
              refine ⟨10851352135142673121182065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28936939027047128323152173 10851352135142673121182065)
              ·
                refine ⟨8138514101357004840886549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10851352135142673121182065 8138514101357004840886549)
                ·
                  refine ⟨381492848501109601916557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8138514101357004840886549 381492848501109601916557)
                  ·
                    refine ⟨143059818187916100718709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381492848501109601916557 143059818187916100718709)
                    ·
                      rfl

theorem cell22_417912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 6, 3].length) (baseStart_417912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417912 prefixEnd_417912 := by exact prefixLift 417912
  have htrace : WordTrace (prefixWord ++ tailWord_417912) baseStart_417912 baseEnd_417912 := by
    simpa [prefixWord, tailWord_417912, baseEnd_417912] using wordTrace_append hprefix tailTrace_417912
  have hstable : (prefixWord ++ tailWord_417912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417912).length < 2 ^ (prefixWord ++ tailWord_417912).sum := by decide
  have hdescent : baseEnd_417912 < baseStart_417912 := by decide
  rcases family_descends (prefixWord ++ tailWord_417912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_417946 : List Nat := [3, 1, 1, 5, 2, 1, 1, 1, 4, 3]
def baseStart_417946 : Nat := 118140960795 + 417946 * 2 ^ 59
def prefixEnd_417946 : Nat := 4983230072969 + 3 ^ 40 * 417946 * 2
def baseEnd_417946 : Nat := 143071457082751345368605

theorem tailTrace_417946 : CollatzResearch.WordTrace tailWord_417946 prefixEnd_417946 143071457082751345368605 := by
  unfold tailWord_417946
  simp only [CollatzResearch.WordTrace]
  refine ⟨3810935735965124084774423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10162495295906997559398461 3810935735965124084774423)
  ·
    refine ⟨5716403603947686127161635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3810935735965124084774423 5716403603947686127161635)
    ·
      refine ⟨8574605405921529190742453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5716403603947686127161635 8574605405921529190742453)
      ·
        refine ⟨803869256805143361632105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8574605405921529190742453 803869256805143361632105)
        ·
          refine ⟨602901942603857521224079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 803869256805143361632105 602901942603857521224079)
          ·
            refine ⟨904352913905786281836119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 602901942603857521224079 904352913905786281836119)
            ·
              refine ⟨1356529370858679422754179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 904352913905786281836119 1356529370858679422754179)
              ·
                refine ⟨2034794056288019134131269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1356529370858679422754179 2034794056288019134131269)
                ·
                  refine ⟨381523885554003587649613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2034794056288019134131269 381523885554003587649613)
                  ·
                    refine ⟨143071457082751345368605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381523885554003587649613 143071457082751345368605)
                    ·
                      rfl

theorem cell22_417946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 1, 4, 3].length) (baseStart_417946 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_417946 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_417946 prefixEnd_417946 := by exact prefixLift 417946
  have htrace : WordTrace (prefixWord ++ tailWord_417946) baseStart_417946 baseEnd_417946 := by
    simpa [prefixWord, tailWord_417946, baseEnd_417946] using wordTrace_append hprefix tailTrace_417946
  have hstable : (prefixWord ++ tailWord_417946).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_417946).length < 2 ^ (prefixWord ++ tailWord_417946).sum := by decide
  have hdescent : baseEnd_417946 < baseStart_417946 := by decide
  rcases family_descends (prefixWord ++ tailWord_417946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418021 : List Nat := [1, 3, 1, 4, 2, 1, 4, 1, 5]
def baseStart_418021 : Nat := 118140960795 + 418021 * 2 ^ 59
def prefixEnd_418021 : Nat := 4983230072969 + 3 ^ 40 * 418021 * 2
def baseEnd_418021 : Nat := 47699043705158716581125

theorem tailTrace_418021 : CollatzResearch.WordTrace tailWord_418021 prefixEnd_418021 47699043705158716581125 := by
  unfold tailWord_418021
  simp only [CollatzResearch.WordTrace]
  refine ⟨15246478418588784148077917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10164318945725856098718611 15246478418588784148077917)
  ·
    refine ⟨5717429406970794055529219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15246478418588784148077917 5717429406970794055529219)
    ·
      refine ⟨8576144110456191083293829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5717429406970794055529219 8576144110456191083293829)
      ·
        refine ⟨1608027020710535828117593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8576144110456191083293829 1608027020710535828117593)
        ·
          refine ⟨1206020265532901871088195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1608027020710535828117593 1206020265532901871088195)
          ·
            refine ⟨1809030398299352806632293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206020265532901871088195 1809030398299352806632293)
            ·
              refine ⟨339193199681128651243555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1809030398299352806632293 339193199681128651243555)
              ·
                refine ⟨508789799521692976865333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339193199681128651243555 508789799521692976865333)
                ·
                  refine ⟨47699043705158716581125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508789799521692976865333 47699043705158716581125)
                  ·
                    rfl

theorem cell22_418021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 4, 1, 5].length) (baseStart_418021 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418021 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418021 prefixEnd_418021 := by exact prefixLift 418021
  have htrace : WordTrace (prefixWord ++ tailWord_418021) baseStart_418021 baseEnd_418021 := by
    simpa [prefixWord, tailWord_418021, baseEnd_418021] using wordTrace_append hprefix tailTrace_418021
  have hstable : (prefixWord ++ tailWord_418021).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418021).length < 2 ^ (prefixWord ++ tailWord_418021).sum := by decide
  have hdescent : baseEnd_418021 < baseStart_418021 := by decide
  rcases family_descends (prefixWord ++ tailWord_418021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418032 : List Nat := [2, 1, 1, 1, 3, 1, 1, 6, 6]
def baseStart_418032 : Nat := 118140960795 + 418032 * 2 ^ 59
def prefixEnd_418032 : Nat := 4983230072969 + 3 ^ 40 * 418032 * 2
def baseEnd_418032 : Nat := 47700298880091929239447

theorem tailTrace_418032 : CollatzResearch.WordTrace tailWord_418032 prefixEnd_418032 47700298880091929239447 := by
  unfold tailWord_418032
  simp only [CollatzResearch.WordTrace]
  refine ⟨7623439810774466513364175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10164586414365955351152233 7623439810774466513364175)
  ·
    refine ⟨11435159716161699770046263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7623439810774466513364175 11435159716161699770046263)
    ·
      refine ⟨17152739574242549655069395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11435159716161699770046263 17152739574242549655069395)
      ·
        refine ⟨25729109361363824482604093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17152739574242549655069395 25729109361363824482604093)
        ·
          refine ⟨9648416010511434180976535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25729109361363824482604093 9648416010511434180976535)
          ·
            refine ⟨14472624015767151271464803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9648416010511434180976535 14472624015767151271464803)
            ·
              refine ⟨21708936023650726907197205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14472624015767151271464803 21708936023650726907197205)
              ·
                refine ⟨1017606376108627823774869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21708936023650726907197205 1017606376108627823774869)
                ·
                  refine ⟨47700298880091929239447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1017606376108627823774869 47700298880091929239447)
                  ·
                    rfl

theorem cell22_418032_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 1, 6, 6].length) (baseStart_418032 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418032 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418032 prefixEnd_418032 := by exact prefixLift 418032
  have htrace : WordTrace (prefixWord ++ tailWord_418032) baseStart_418032 baseEnd_418032 := by
    simpa [prefixWord, tailWord_418032, baseEnd_418032] using wordTrace_append hprefix tailTrace_418032
  have hstable : (prefixWord ++ tailWord_418032).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418032).length < 2 ^ (prefixWord ++ tailWord_418032).sum := by decide
  have hdescent : baseEnd_418032 < baseStart_418032 := by decide
  rcases family_descends (prefixWord ++ tailWord_418032) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418051 : List Nat := [1, 1, 1, 3, 2, 3, 5, 1, 1, 4]
def baseStart_418051 : Nat := 118140960795 + 418051 * 2 ^ 59
def prefixEnd_418051 : Nat := 4983230072969 + 3 ^ 40 * 418051 * 2
def baseEnd_418051 : Nat := 143107400728566071493283

theorem tailTrace_418051 : CollatzResearch.WordTrace tailWord_418051 prefixEnd_418051 143107400728566071493283 := by
  unfold tailWord_418051
  simp only [CollatzResearch.WordTrace]
  refine ⟨15247572608480099271670007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10165048405653399514446671 15247572608480099271670007)
  ·
    refine ⟨22871358912720148907505011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15247572608480099271670007 22871358912720148907505011)
    ·
      refine ⟨34307038369080223361257517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22871358912720148907505011 34307038369080223361257517)
      ·
        refine ⟨12865139388405083760471569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34307038369080223361257517 12865139388405083760471569)
        ·
          refine ⟨9648854541303812820353677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12865139388405083760471569 9648854541303812820353677)
          ·
            refine ⟨3618320452988929807632629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9648854541303812820353677 3618320452988929807632629)
            ·
              refine ⟨339217542467712169465559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3618320452988929807632629 339217542467712169465559)
              ·
                refine ⟨508826313701568254198339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339217542467712169465559 508826313701568254198339)
                ·
                  refine ⟨763239470552352381297509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 508826313701568254198339 763239470552352381297509)
                  ·
                    refine ⟨143107400728566071493283, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763239470552352381297509 143107400728566071493283)
                    ·
                      rfl

theorem cell22_418051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 5, 1, 1, 4].length) (baseStart_418051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418051 prefixEnd_418051 := by exact prefixLift 418051
  have htrace : WordTrace (prefixWord ++ tailWord_418051) baseStart_418051 baseEnd_418051 := by
    simpa [prefixWord, tailWord_418051, baseEnd_418051] using wordTrace_append hprefix tailTrace_418051
  have hstable : (prefixWord ++ tailWord_418051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418051).length < 2 ^ (prefixWord ++ tailWord_418051).sum := by decide
  have hdescent : baseEnd_418051 < baseStart_418051 := by decide
  rcases family_descends (prefixWord ++ tailWord_418051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418081 : List Nat := [1, 2, 3, 2, 1, 1, 4, 3, 2, 3]
def baseStart_418081 : Nat := 118140960795 + 418081 * 2 ^ 59
def prefixEnd_418081 : Nat := 4983230072969 + 3 ^ 40 * 418081 * 2
def baseEnd_418081 : Nat := 143117670341655993243191

theorem tailTrace_418081 : CollatzResearch.WordTrace tailWord_418081 prefixEnd_418081 143117670341655993243191 := by
  unfold tailWord_418081
  simp only [CollatzResearch.WordTrace]
  refine ⟨15248666798371414395262097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10165777865580942930174731 15248666798371414395262097)
  ·
    refine ⟨11436500098778560796446573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15248666798371414395262097 11436500098778560796446573)
    ·
      refine ⟨4288687537041960298667465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11436500098778560796446573 4288687537041960298667465)
      ·
        refine ⟨3216515652781470224000599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4288687537041960298667465 3216515652781470224000599)
        ·
          refine ⟨4824773479172205336000899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3216515652781470224000599 4824773479172205336000899)
          ·
            refine ⟨7237160218758308004001349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4824773479172205336000899 7237160218758308004001349)
            ·
              refine ⟨1356967541017182750750253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7237160218758308004001349 1356967541017182750750253)
              ·
                refine ⟨508862827881443531531345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1356967541017182750750253 508862827881443531531345)
                ·
                  refine ⟨381647120911082648648509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 508862827881443531531345 381647120911082648648509)
                  ·
                    refine ⟨143117670341655993243191, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381647120911082648648509 143117670341655993243191)
                    ·
                      rfl

theorem cell22_418081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 4, 3, 2, 3].length) (baseStart_418081 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418081 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418081 prefixEnd_418081 := by exact prefixLift 418081
  have htrace : WordTrace (prefixWord ++ tailWord_418081) baseStart_418081 baseEnd_418081 := by
    simpa [prefixWord, tailWord_418081, baseEnd_418081] using wordTrace_append hprefix tailTrace_418081
  have hstable : (prefixWord ++ tailWord_418081).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418081).length < 2 ^ (prefixWord ++ tailWord_418081).sum := by decide
  have hdescent : baseEnd_418081 < baseStart_418081 := by decide
  rcases family_descends (prefixWord ++ tailWord_418081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418160 : List Nat := [2, 1, 1, 1, 4, 5, 1, 3, 1, 3]
def baseStart_418160 : Nat := 118140960795 + 418160 * 2 ^ 59
def prefixEnd_418160 : Nat := 4983230072969 + 3 ^ 40 * 418160 * 2
def baseEnd_418160 : Nat := 143144713656126120517949

theorem tailTrace_418160 : CollatzResearch.WordTrace tailWord_418160 prefixEnd_418160 143144713656126120517949 := by
  unfold tailWord_418160
  simp only [CollatzResearch.WordTrace]
  refine ⟨7625774082542605443693967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10167698776723473924925289 7625774082542605443693967)
  ·
    refine ⟨11438661123813908165540951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7625774082542605443693967 11438661123813908165540951)
    ·
      refine ⟨17157991685720862248311427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438661123813908165540951 17157991685720862248311427)
      ·
        refine ⟨25736987528581293372467141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17157991685720862248311427 25736987528581293372467141)
        ·
          refine ⟨4825685161608992507337589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25736987528581293372467141 4825685161608992507337589)
          ·
            refine ⟨452407983900843047562899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4825685161608992507337589 452407983900843047562899)
            ·
              refine ⟨678611975851264571344349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 452407983900843047562899 678611975851264571344349)
              ·
                refine ⟨254479490944224214254131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 678611975851264571344349 254479490944224214254131)
                ·
                  refine ⟨381719236416336321381197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254479490944224214254131 381719236416336321381197)
                  ·
                    refine ⟨143144713656126120517949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381719236416336321381197 143144713656126120517949)
                    ·
                      rfl

theorem cell22_418160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 5, 1, 3, 1, 3].length) (baseStart_418160 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418160 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418160 prefixEnd_418160 := by exact prefixLift 418160
  have htrace : WordTrace (prefixWord ++ tailWord_418160) baseStart_418160 baseEnd_418160 := by
    simpa [prefixWord, tailWord_418160, baseEnd_418160] using wordTrace_append hprefix tailTrace_418160
  have hstable : (prefixWord ++ tailWord_418160).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418160).length < 2 ^ (prefixWord ++ tailWord_418160).sum := by decide
  have hdescent : baseEnd_418160 < baseStart_418160 := by decide
  rcases family_descends (prefixWord ++ tailWord_418160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418169 : List Nat := [1, 2, 1, 3, 2, 1, 1, 2, 5, 4]
def baseStart_418169 : Nat := 118140960795 + 418169 * 2 ^ 59
def prefixEnd_418169 : Nat := 4983230072969 + 3 ^ 40 * 418169 * 2
def baseEnd_418169 : Nat := 143147794540053097042921

theorem tailTrace_418169 : CollatzResearch.WordTrace tailWord_418169 prefixEnd_418169 143147794540053097042921 := by
  unfold tailWord_418169
  simp only [CollatzResearch.WordTrace]
  refine ⟨15251876422052605424465561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10167917614701736949643707 15251876422052605424465561)
  ·
    refine ⟨11438907316539454068349171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15251876422052605424465561 11438907316539454068349171)
    ·
      refine ⟨17158360974809181102523757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11438907316539454068349171 17158360974809181102523757)
      ·
        refine ⟨6434385365553442913446409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17158360974809181102523757 6434385365553442913446409)
        ·
          refine ⟨4825789024165082185084807, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6434385365553442913446409 4825789024165082185084807)
          ·
            refine ⟨7238683536247623277627211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4825789024165082185084807 7238683536247623277627211)
            ·
              refine ⟨10858025304371434916440817, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7238683536247623277627211 10858025304371434916440817)
              ·
                refine ⟨8143518978278576187330613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10858025304371434916440817 8143518978278576187330613)
                ·
                  refine ⟨763454904213616517562245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 8143518978278576187330613 763454904213616517562245)
                  ·
                    refine ⟨143147794540053097042921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763454904213616517562245 143147794540053097042921)
                    ·
                      rfl

theorem cell22_418169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 1, 2, 5, 4].length) (baseStart_418169 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418169 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418169 prefixEnd_418169 := by exact prefixLift 418169
  have htrace : WordTrace (prefixWord ++ tailWord_418169) baseStart_418169 baseEnd_418169 := by
    simpa [prefixWord, tailWord_418169, baseEnd_418169] using wordTrace_append hprefix tailTrace_418169
  have hstable : (prefixWord ++ tailWord_418169).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418169).length < 2 ^ (prefixWord ++ tailWord_418169).sum := by decide
  have hdescent : baseEnd_418169 < baseStart_418169 := by decide
  rcases family_descends (prefixWord ++ tailWord_418169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418177 : List Nat := [1, 2, 4, 3, 1, 2, 3, 2, 1, 3]
def baseStart_418177 : Nat := 118140960795 + 418177 * 2 ^ 59
def prefixEnd_418177 : Nat := 4983230072969 + 3 ^ 40 * 418177 * 2
def baseEnd_418177 : Nat := 143150533103543742842897

theorem tailTrace_418177 : CollatzResearch.WordTrace tailWord_418177 prefixEnd_418177 143150533103543742842897 := by
  unfold tailWord_418177
  simp only [CollatzResearch.WordTrace]
  refine ⟨15252168206023622790756785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10168112137349081860504523 15252168206023622790756785)
  ·
    refine ⟨11439126154517717093067589, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15252168206023622790756785 11439126154517717093067589)
    ·
      refine ⟨2144836153972071954950173, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11439126154517717093067589 2144836153972071954950173)
      ·
        refine ⟨804313557739526983106315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2144836153972071954950173 804313557739526983106315)
        ·
          refine ⟨1206470336609290474659473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804313557739526983106315 1206470336609290474659473)
          ·
            refine ⟨904852752456967855994605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1206470336609290474659473 904852752456967855994605)
            ·
              refine ⟨339319782171362945997977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 904852752456967855994605 339319782171362945997977)
              ·
                refine ⟨254489836628522209498483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339319782171362945997977 254489836628522209498483)
                ·
                  refine ⟨381734754942783314247725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254489836628522209498483 381734754942783314247725)
                  ·
                    refine ⟨143150533103543742842897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381734754942783314247725 143150533103543742842897)
                    ·
                      rfl

theorem cell22_418177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 1, 2, 3, 2, 1, 3].length) (baseStart_418177 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418177 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418177 prefixEnd_418177 := by exact prefixLift 418177
  have htrace : WordTrace (prefixWord ++ tailWord_418177) baseStart_418177 baseEnd_418177 := by
    simpa [prefixWord, tailWord_418177, baseEnd_418177] using wordTrace_append hprefix tailTrace_418177
  have hstable : (prefixWord ++ tailWord_418177).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418177).length < 2 ^ (prefixWord ++ tailWord_418177).sum := by decide
  have hdescent : baseEnd_418177 < baseStart_418177 := by decide
  rcases family_descends (prefixWord ++ tailWord_418177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418190 : List Nat := [4, 1, 1, 4, 1, 3, 2, 1, 5]
def baseStart_418190 : Nat := 118140960795 + 418190 * 2 ^ 59
def prefixEnd_418190 : Nat := 4983230072969 + 3 ^ 40 * 418190 * 2
def baseEnd_418190 : Nat := 47718327756405347422619

theorem tailTrace_418190 : CollatzResearch.WordTrace tailWord_418190 prefixEnd_418190 47718327756405347422619 := by
  unfold tailWord_418190
  simp only [CollatzResearch.WordTrace]
  refine ⟨1906580294372065751372503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10168428236651017340653349 1906580294372065751372503)
  ·
    refine ⟨2859870441558098627058755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1906580294372065751372503 2859870441558098627058755)
    ·
      refine ⟨4289805662337147940588133, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2859870441558098627058755 4289805662337147940588133)
      ·
        refine ⟨804338561688215238860275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4289805662337147940588133 804338561688215238860275)
        ·
          refine ⟨1206507842532322858290413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 804338561688215238860275 1206507842532322858290413)
          ·
            refine ⟨452440440949621071858905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1206507842532322858290413 452440440949621071858905)
            ·
              refine ⟨339330330712215803894179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452440440949621071858905 339330330712215803894179)
              ·
                refine ⟨508995496068323705841269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339330330712215803894179 508995496068323705841269)
                ·
                  refine ⟨47718327756405347422619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 508995496068323705841269 47718327756405347422619)
                  ·
                    rfl

theorem cell22_418190_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_418190 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418190 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418190 prefixEnd_418190 := by exact prefixLift 418190
  have htrace : WordTrace (prefixWord ++ tailWord_418190) baseStart_418190 baseEnd_418190 := by
    simpa [prefixWord, tailWord_418190, baseEnd_418190] using wordTrace_append hprefix tailTrace_418190
  have hstable : (prefixWord ++ tailWord_418190).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418190).length < 2 ^ (prefixWord ++ tailWord_418190).sum := by decide
  have hdescent : baseEnd_418190 < baseStart_418190 := by decide
  rcases family_descends (prefixWord ++ tailWord_418190) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418228 : List Nat := [2, 5, 2, 2, 2, 1, 2, 2, 1, 3]
def baseStart_418228 : Nat := 118140960795 + 418228 * 2 ^ 59
def prefixEnd_418228 : Nat := 4983230072969 + 3 ^ 40 * 418228 * 2
def baseEnd_418228 : Nat := 143167991445796609817741

theorem tailTrace_418228 : CollatzResearch.WordTrace tailWord_418228 prefixEnd_418228 143167991445796609817741 := by
  unfold tailWord_418228
  simp only [CollatzResearch.WordTrace]
  refine ⟨7627014164419429250431669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10169352219225905667242225 7627014164419429250431669)
  ·
    refine ⟨715032577914321492227969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 7627014164419429250431669 715032577914321492227969)
    ·
      refine ⟨536274433435741119170977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 715032577914321492227969 536274433435741119170977)
      ·
        refine ⟨402205825076805839378233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 536274433435741119170977 402205825076805839378233)
        ·
          refine ⟨301654368807604379533675, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 402205825076805839378233 301654368807604379533675)
          ·
            refine ⟨452481553211406569300513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 301654368807604379533675 452481553211406569300513)
            ·
              refine ⟨339361164908554926975385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 452481553211406569300513 339361164908554926975385)
              ·
                refine ⟨254520873681416195231539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339361164908554926975385 254520873681416195231539)
                ·
                  refine ⟨381781310522124292847309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254520873681416195231539 381781310522124292847309)
                  ·
                    refine ⟨143167991445796609817741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381781310522124292847309 143167991445796609817741)
                    ·
                      rfl

theorem cell22_418228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 2, 2, 1, 2, 2, 1, 3].length) (baseStart_418228 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418228 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418228 prefixEnd_418228 := by exact prefixLift 418228
  have htrace : WordTrace (prefixWord ++ tailWord_418228) baseStart_418228 baseEnd_418228 := by
    simpa [prefixWord, tailWord_418228, baseEnd_418228] using wordTrace_append hprefix tailTrace_418228
  have hstable : (prefixWord ++ tailWord_418228).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418228).length < 2 ^ (prefixWord ++ tailWord_418228).sum := by decide
  have hdescent : baseEnd_418228 < baseStart_418228 := by decide
  rcases family_descends (prefixWord ++ tailWord_418228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418229 : List Nat := [1, 3, 3, 2, 13]
def baseStart_418229 : Nat := 118140960795 + 418229 * 2 ^ 59
def prefixEnd_418229 : Nat := 4983230072969 + 3 ^ 40 * 418229 * 2
def baseEnd_418229 : Nat := 589170097803427738859

theorem tailTrace_418229 : CollatzResearch.WordTrace tailWord_418229 prefixEnd_418229 589170097803427738859 := by
  unfold tailWord_418229
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254064801835235671649741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10169376534556823781099827 15254064801835235671649741)
  ·
    refine ⟨5720274300688213376868653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15254064801835235671649741 5720274300688213376868653)
    ·
      refine ⟨2145102862758080016325745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5720274300688213376868653 2145102862758080016325745)
      ·
        refine ⟨1608827147068560012244309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2145102862758080016325745 1608827147068560012244309)
        ·
          refine ⟨589170097803427738859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 13 1608827147068560012244309 589170097803427738859)
          ·
            rfl

theorem cell22_418229_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 13].length) (baseStart_418229 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418229 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418229 prefixEnd_418229 := by exact prefixLift 418229
  have htrace : WordTrace (prefixWord ++ tailWord_418229) baseStart_418229 baseEnd_418229 := by
    simpa [prefixWord, tailWord_418229, baseEnd_418229] using wordTrace_append hprefix tailTrace_418229
  have hstable : (prefixWord ++ tailWord_418229).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418229).length < 2 ^ (prefixWord ++ tailWord_418229).sum := by decide
  have hdescent : baseEnd_418229 < baseStart_418229 := by decide
  rcases family_descends (prefixWord ++ tailWord_418229) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418231 : List Nat := [1, 1, 3, 1, 3, 3, 2, 2, 2, 4]
def baseStart_418231 : Nat := 118140960795 + 418231 * 2 ^ 59
def prefixEnd_418231 : Nat := 4983230072969 + 3 ^ 40 * 418231 * 2
def baseEnd_418231 : Nat := 143169018407105601992731

theorem tailTrace_418231 : CollatzResearch.WordTrace tailWord_418231 prefixEnd_418231 143169018407105601992731 := by
  unfold tailWord_418231
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254137747827990013222547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10169425165218660008815031 15254137747827990013222547)
  ·
    refine ⟨22881206621741985019833821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15254137747827990013222547 22881206621741985019833821)
    ·
      refine ⟨8580452483153244382437683, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22881206621741985019833821 8580452483153244382437683)
      ·
        refine ⟨12870678724729866573656525, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8580452483153244382437683 12870678724729866573656525)
        ·
          refine ⟨4826504521773699965121197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12870678724729866573656525 4826504521773699965121197)
          ·
            refine ⟨1809939195665137486920449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4826504521773699965121197 1809939195665137486920449)
            ·
              refine ⟨1357454396748853115190337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1809939195665137486920449 1357454396748853115190337)
              ·
                refine ⟨1018090797561639836392753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1357454396748853115190337 1018090797561639836392753)
                ·
                  refine ⟨763568098171229877294565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1018090797561639836392753 763568098171229877294565)
                  ·
                    refine ⟨143169018407105601992731, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 763568098171229877294565 143169018407105601992731)
                    ·
                      rfl

theorem cell22_418231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 2, 2, 4].length) (baseStart_418231 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418231 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418231 prefixEnd_418231 := by exact prefixLift 418231
  have htrace : WordTrace (prefixWord ++ tailWord_418231) baseStart_418231 baseEnd_418231 := by
    simpa [prefixWord, tailWord_418231, baseEnd_418231] using wordTrace_append hprefix tailTrace_418231
  have hstable : (prefixWord ++ tailWord_418231).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418231).length < 2 ^ (prefixWord ++ tailWord_418231).sum := by decide
  have hdescent : baseEnd_418231 < baseStart_418231 := by decide
  rcases family_descends (prefixWord ++ tailWord_418231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418233 : List Nat := [1, 2, 1, 4, 3, 1, 1, 4, 2, 3]
def baseStart_418233 : Nat := 118140960795 + 418233 * 2 ^ 59
def prefixEnd_418233 : Nat := 4983230072969 + 3 ^ 40 * 418233 * 2
def baseEnd_418233 : Nat := 143169703047978263442725

theorem tailTrace_418233 : CollatzResearch.WordTrace tailWord_418233 prefixEnd_418233 143169703047978263442725 := by
  unfold tailWord_418233
  simp only [CollatzResearch.WordTrace]
  refine ⟨15254210693820744354795353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10169473795880496236530235 15254210693820744354795353)
  ·
    refine ⟨11440658020365558266096515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15254210693820744354795353 11440658020365558266096515)
    ·
      refine ⟨17160987030548337399144773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11440658020365558266096515 17160987030548337399144773)
      ·
        refine ⟨3217685068227813262339645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17160987030548337399144773 3217685068227813262339645)
        ·
          refine ⟨1206631900585429973377367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3217685068227813262339645 1206631900585429973377367)
          ·
            refine ⟨1809947850878144960066051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1206631900585429973377367 1809947850878144960066051)
            ·
              refine ⟨2714921776317217440099077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1809947850878144960066051 2714921776317217440099077)
              ·
                refine ⟨509047833059478270018577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2714921776317217440099077 509047833059478270018577)
                ·
                  refine ⟨381785874794608702513933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509047833059478270018577 381785874794608702513933)
                  ·
                    refine ⟨143169703047978263442725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 381785874794608702513933 143169703047978263442725)
                    ·
                      rfl

theorem cell22_418233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 1, 1, 4, 2, 3].length) (baseStart_418233 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418233 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418233 prefixEnd_418233 := by exact prefixLift 418233
  have htrace : WordTrace (prefixWord ++ tailWord_418233) baseStart_418233 baseEnd_418233 := by
    simpa [prefixWord, tailWord_418233, baseEnd_418233] using wordTrace_append hprefix tailTrace_418233
  have hstable : (prefixWord ++ tailWord_418233).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418233).length < 2 ^ (prefixWord ++ tailWord_418233).sum := by decide
  have hdescent : baseEnd_418233 < baseStart_418233 := by decide
  rcases family_descends (prefixWord ++ tailWord_418233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418353 : List Nat := [1, 2, 2, 3, 1, 1, 2, 6, 4]
def baseStart_418353 : Nat := 118140960795 + 418353 * 2 ^ 59
def prefixEnd_418353 : Nat := 4983230072969 + 3 ^ 40 * 418353 * 2
def baseEnd_418353 : Nat := 47736927166779316814119

theorem tailTrace_418353 : CollatzResearch.WordTrace tailWord_418353 prefixEnd_418353 47736927166779316814119 := by
  unfold tailWord_418353
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258587453386004849163713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10172391635590669899442475 15258587453386004849163713)
  ·
    refine ⟨11443940590039503636872785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15258587453386004849163713 11443940590039503636872785)
    ·
      refine ⟨8582955442529627727654589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11443940590039503636872785 8582955442529627727654589)
      ·
        refine ⟨3218608290948610397870471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8582955442529627727654589 3218608290948610397870471)
        ·
          refine ⟨4827912436422915596805707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3218608290948610397870471 4827912436422915596805707)
          ·
            refine ⟨7241868654634373395208561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827912436422915596805707 7241868654634373395208561)
            ·
              refine ⟨5431401490975780046406421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241868654634373395208561 5431401490975780046406421)
              ·
                refine ⟨254596944889489689675301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 5431401490975780046406421 254596944889489689675301)
                ·
                  refine ⟨47736927166779316814119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254596944889489689675301 47736927166779316814119)
                  ·
                    rfl

theorem cell22_418353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 2, 6, 4].length) (baseStart_418353 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418353 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418353 prefixEnd_418353 := by exact prefixLift 418353
  have htrace : WordTrace (prefixWord ++ tailWord_418353) baseStart_418353 baseEnd_418353 := by
    simpa [prefixWord, tailWord_418353, baseEnd_418353] using wordTrace_append hprefix tailTrace_418353
  have hstable : (prefixWord ++ tailWord_418353).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418353).length < 2 ^ (prefixWord ++ tailWord_418353).sum := by decide
  have hdescent : baseEnd_418353 < baseStart_418353 := by decide
  rcases family_descends (prefixWord ++ tailWord_418353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418434 : List Nat := [3, 4, 3, 1, 1, 1, 1, 1, 1, 6]
def baseStart_418434 : Nat := 118140960795 + 418434 * 2 ^ 59
def prefixEnd_418434 : Nat := 4983230072969 + 3 ^ 40 * 418434 * 2
def baseEnd_418434 : Nat := 143238509455680739167109

theorem tailTrace_418434 : CollatzResearch.WordTrace tailWord_418434 prefixEnd_418434 143238509455680739167109 := by
  unfold tailWord_418434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815385441523138920715589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10174361177395037121908237 3815385441523138920715589)
  ·
    refine ⟨715384770285588547634173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3815385441523138920715589 715384770285588547634173)
    ·
      refine ⟨268269288857095705362815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 715384770285588547634173 268269288857095705362815)
      ·
        refine ⟨402403933285643558044223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268269288857095705362815 402403933285643558044223)
        ·
          refine ⟨603605899928465337066335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402403933285643558044223 603605899928465337066335)
          ·
            refine ⟨905408849892698005599503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603605899928465337066335 905408849892698005599503)
            ·
              refine ⟨1358113274839047008399255, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905408849892698005599503 1358113274839047008399255)
              ·
                refine ⟨2037169912258570512598883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358113274839047008399255 2037169912258570512598883)
                ·
                  refine ⟨3055754868387855768898325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037169912258570512598883 3055754868387855768898325)
                  ·
                    refine ⟨143238509455680739167109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3055754868387855768898325 143238509455680739167109)
                    ·
                      rfl

theorem cell22_418434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 3, 1, 1, 1, 1, 1, 1, 6].length) (baseStart_418434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418434 prefixEnd_418434 := by exact prefixLift 418434
  have htrace : WordTrace (prefixWord ++ tailWord_418434) baseStart_418434 baseEnd_418434 := by
    simpa [prefixWord, tailWord_418434, baseEnd_418434] using wordTrace_append hprefix tailTrace_418434
  have hstable : (prefixWord ++ tailWord_418434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418434).length < 2 ^ (prefixWord ++ tailWord_418434).sum := by decide
  have hdescent : baseEnd_418434 < baseStart_418434 := by decide
  rcases family_descends (prefixWord ++ tailWord_418434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418441 : List Nat := [1, 2, 1, 1, 4, 1, 1, 1, 3, 7]
def baseStart_418441 : Nat := 118140960795 + 418441 * 2 ^ 59
def prefixEnd_418441 : Nat := 4983230072969 + 3 ^ 40 * 418441 * 2
def baseEnd_418441 : Nat := 143240905698735054242087

theorem tailTrace_418441 : CollatzResearch.WordTrace tailWord_418441 prefixEnd_418441 143240905698735054242087 := by
  unfold tailWord_418441
  simp only [CollatzResearch.WordTrace]
  refine ⟨15261797077067195878367177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10174531384711463918911451 15261797077067195878367177)
  ·
    refine ⟨11446347807800396908775383, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15261797077067195878367177 11446347807800396908775383)
    ·
      refine ⟨17169521711700595363163075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446347807800396908775383 17169521711700595363163075)
      ·
        refine ⟨25754282567550893044744613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17169521711700595363163075 25754282567550893044744613)
        ·
          refine ⟨4828927981415792445889615, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25754282567550893044744613 4828927981415792445889615)
          ·
            refine ⟨7243391972123688668834423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828927981415792445889615 7243391972123688668834423)
            ·
              refine ⟨10865087958185533003251635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243391972123688668834423 10865087958185533003251635)
              ·
                refine ⟨16297631937278299504877453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865087958185533003251635 16297631937278299504877453)
                ·
                  refine ⟨6111611976479362314329045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16297631937278299504877453 6111611976479362314329045)
                  ·
                    refine ⟨143240905698735054242087, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 6111611976479362314329045 143240905698735054242087)
                    ·
                      rfl

theorem cell22_418441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 1, 3, 7].length) (baseStart_418441 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418441 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418441 prefixEnd_418441 := by exact prefixLift 418441
  have htrace : WordTrace (prefixWord ++ tailWord_418441) baseStart_418441 baseEnd_418441 := by
    simpa [prefixWord, tailWord_418441, baseEnd_418441] using wordTrace_append hprefix tailTrace_418441
  have hstable : (prefixWord ++ tailWord_418441).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418441).length < 2 ^ (prefixWord ++ tailWord_418441).sum := by decide
  have hdescent : baseEnd_418441 < baseStart_418441 := by decide
  rcases family_descends (prefixWord ++ tailWord_418441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418460 : List Nat := [2, 2, 3, 2, 2, 1, 3, 2, 5]
def baseStart_418460 : Nat := 118140960795 + 418460 * 2 ^ 59
def prefixEnd_418460 : Nat := 4983230072969 + 3 ^ 40 * 418460 * 2
def baseEnd_418460 : Nat := 47749136595675112672343

theorem tailTrace_418460 : CollatzResearch.WordTrace tailWord_418460 prefixEnd_418460 47749136595675112672343 := by
  unfold tailWord_418460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7631245031999181061654417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10174993375998908082205889 7631245031999181061654417)
  ·
    refine ⟨5723433773999385796240813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7631245031999181061654417 5723433773999385796240813)
    ·
      refine ⟨2146287665249769673590305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5723433773999385796240813 2146287665249769673590305)
      ·
        refine ⟨1609715748937327255192729, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2146287665249769673590305 1609715748937327255192729)
        ·
          refine ⟨1207286811702995441394547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1609715748937327255192729 1207286811702995441394547)
          ·
            refine ⟨1810930217554493162091821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1207286811702995441394547 1810930217554493162091821)
            ·
              refine ⟨679098831582934935784433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1810930217554493162091821 679098831582934935784433)
              ·
                refine ⟨509324123687201201838325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679098831582934935784433 509324123687201201838325)
                ·
                  refine ⟨47749136595675112672343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509324123687201201838325 47749136595675112672343)
                  ·
                    rfl

theorem cell22_418460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3, 2, 5].length) (baseStart_418460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418460 prefixEnd_418460 := by exact prefixLift 418460
  have htrace : WordTrace (prefixWord ++ tailWord_418460) baseStart_418460 baseEnd_418460 := by
    simpa [prefixWord, tailWord_418460, baseEnd_418460] using wordTrace_append hprefix tailTrace_418460
  have hstable : (prefixWord ++ tailWord_418460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418460).length < 2 ^ (prefixWord ++ tailWord_418460).sum := by decide
  have hdescent : baseEnd_418460 < baseStart_418460 := by decide
  rcases family_descends (prefixWord ++ tailWord_418460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418477 : List Nat := [1, 5, 2, 1, 1, 3, 3, 1, 5]
def baseStart_418477 : Nat := 118140960795 + 418477 * 2 ^ 59
def prefixEnd_418477 : Nat := 4983230072969 + 3 ^ 40 * 418477 * 2
def baseEnd_418477 : Nat := 47751076411480986780659

theorem tailTrace_418477 : CollatzResearch.WordTrace tailWord_418477 prefixEnd_418477 47751076411480986780659 := by
  unfold tailWord_418477
  simp only [CollatzResearch.WordTrace]
  refine ⟨15263110104936774026677685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10175406736624516017785123 15263110104936774026677685)
  ·
    refine ⟨1430916572337822565001033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 15263110104936774026677685 1430916572337822565001033)
    ·
      refine ⟨1073187429253366923750775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1430916572337822565001033 1073187429253366923750775)
      ·
        refine ⟨1609781143880050385626163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1073187429253366923750775 1609781143880050385626163)
        ·
          refine ⟨2414671715820075578439245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609781143880050385626163 2414671715820075578439245)
          ·
            refine ⟨905501893432528341914717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2414671715820075578439245 905501893432528341914717)
            ·
              refine ⟨339563210037198128218019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 905501893432528341914717 339563210037198128218019)
              ·
                refine ⟨509344815055797192327029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339563210037198128218019 509344815055797192327029)
                ·
                  refine ⟨47751076411480986780659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 509344815055797192327029 47751076411480986780659)
                  ·
                    rfl

theorem cell22_418477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 3, 3, 1, 5].length) (baseStart_418477 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418477 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418477 prefixEnd_418477 := by exact prefixLift 418477
  have htrace : WordTrace (prefixWord ++ tailWord_418477) baseStart_418477 baseEnd_418477 := by
    simpa [prefixWord, tailWord_418477, baseEnd_418477] using wordTrace_append hprefix tailTrace_418477
  have hstable : (prefixWord ++ tailWord_418477).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418477).length < 2 ^ (prefixWord ++ tailWord_418477).sum := by decide
  have hdescent : baseEnd_418477 < baseStart_418477 := by decide
  rcases family_descends (prefixWord ++ tailWord_418477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418490 : List Nat := [3, 1, 1, 1, 2, 3, 4, 2, 1, 4]
def baseStart_418490 : Nat := 118140960795 + 418490 * 2 ^ 59
def prefixEnd_418490 : Nat := 4983230072969 + 3 ^ 40 * 418490 * 2
def baseEnd_418490 : Nat := 143257679400115259766937

theorem tailTrace_418490 : CollatzResearch.WordTrace tailWord_418490 prefixEnd_418490 143257679400115259766937 := by
  unfold tailWord_418490
  simp only [CollatzResearch.WordTrace]
  refine ⟨3815896063472419311725231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10175722835926451497933949 3815896063472419311725231)
  ·
    refine ⟨5723844095208628967587847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3815896063472419311725231 5723844095208628967587847)
    ·
      refine ⟨8585766142812943451381771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5723844095208628967587847 8585766142812943451381771)
      ·
        refine ⟨12878649214219415177072657, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8585766142812943451381771 12878649214219415177072657)
        ·
          refine ⟨9658986910664561382804493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12878649214219415177072657 9658986910664561382804493)
          ·
            refine ⟨3622120091499210518551685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9658986910664561382804493 3622120091499210518551685)
            ·
              refine ⟨679147517156101972228441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3622120091499210518551685 679147517156101972228441)
              ·
                refine ⟨509360637867076479171331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 679147517156101972228441 509360637867076479171331)
                ·
                  refine ⟨764040956800614718756997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509360637867076479171331 764040956800614718756997)
                  ·
                    refine ⟨143257679400115259766937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 764040956800614718756997 143257679400115259766937)
                    ·
                      rfl

theorem cell22_418490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 4, 2, 1, 4].length) (baseStart_418490 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418490 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418490 prefixEnd_418490 := by exact prefixLift 418490
  have htrace : WordTrace (prefixWord ++ tailWord_418490) baseStart_418490 baseEnd_418490 := by
    simpa [prefixWord, tailWord_418490, baseEnd_418490] using wordTrace_append hprefix tailTrace_418490
  have hstable : (prefixWord ++ tailWord_418490).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418490).length < 2 ^ (prefixWord ++ tailWord_418490).sum := by decide
  have hdescent : baseEnd_418490 < baseStart_418490 := by decide
  rcases family_descends (prefixWord ++ tailWord_418490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418520 : List Nat := [2, 1, 2, 2, 3, 2, 2, 1, 4, 3]
def baseStart_418520 : Nat := 118140960795 + 418520 * 2 ^ 59
def prefixEnd_418520 : Nat := 4983230072969 + 3 ^ 40 * 418520 * 2
def baseEnd_418520 : Nat := 143267949013205181516845

theorem tailTrace_418520 : CollatzResearch.WordTrace tailWord_418520 prefixEnd_418520 143267949013205181516845 := by
  unfold tailWord_418520
  simp only [CollatzResearch.WordTrace]
  refine ⟨7632339221890496185246507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10176452295853994913662009 7632339221890496185246507)
  ·
    refine ⟨11448508832835744277869761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7632339221890496185246507 11448508832835744277869761)
    ·
      refine ⟨8586381624626808208402321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11448508832835744277869761 8586381624626808208402321)
      ·
        refine ⟨6439786218470106156301741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8586381624626808208402321 6439786218470106156301741)
        ·
          refine ⟨2414919831926289808613153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6439786218470106156301741 2414919831926289808613153)
          ·
            refine ⟨1811189873944717356459865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414919831926289808613153 1811189873944717356459865)
            ·
              refine ⟨1358392405458538017344899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1811189873944717356459865 1358392405458538017344899)
              ·
                refine ⟨2037588608187807026017349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1358392405458538017344899 2037588608187807026017349)
                ·
                  refine ⟨382047864035213817378253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 2037588608187807026017349 382047864035213817378253)
                  ·
                    refine ⟨143267949013205181516845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382047864035213817378253 143267949013205181516845)
                    ·
                      rfl

theorem cell22_418520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 2, 2, 1, 4, 3].length) (baseStart_418520 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418520 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418520 prefixEnd_418520 := by exact prefixLift 418520
  have htrace : WordTrace (prefixWord ++ tailWord_418520) baseStart_418520 baseEnd_418520 := by
    simpa [prefixWord, tailWord_418520, baseEnd_418520] using wordTrace_append hprefix tailTrace_418520
  have hstable : (prefixWord ++ tailWord_418520).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418520).length < 2 ^ (prefixWord ++ tailWord_418520).sum := by decide
  have hdescent : baseEnd_418520 < baseStart_418520 := by decide
  rcases family_descends (prefixWord ++ tailWord_418520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418522 : List Nat := [3, 1, 1, 2, 2, 2, 5, 2, 4]
def baseStart_418522 : Nat := 118140960795 + 418522 * 2 ^ 59
def prefixEnd_418522 : Nat := 4983230072969 + 3 ^ 40 * 418522 * 2
def baseEnd_418522 : Nat := 47756211218025947655613

theorem tailTrace_418522 : CollatzResearch.WordTrace tailWord_418522 prefixEnd_418522 47756211218025947655613 := by
  unfold tailWord_418522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3816187847443436678016455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10176500926515831141377213 3816187847443436678016455)
  ·
    refine ⟨5724281771165155017024683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3816187847443436678016455 5724281771165155017024683)
    ·
      refine ⟨8586422656747732525537025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5724281771165155017024683 8586422656747732525537025)
      ·
        refine ⟨6439816992560799394152769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8586422656747732525537025 6439816992560799394152769)
        ·
          refine ⟨4829862744420599545614577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6439816992560799394152769 4829862744420599545614577)
          ·
            refine ⟨3622397058315449659210933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829862744420599545614577 3622397058315449659210933)
            ·
              refine ⟨339599724217073405551025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3622397058315449659210933 339599724217073405551025)
              ·
                refine ⟨254699793162805054163269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339599724217073405551025 254699793162805054163269)
                ·
                  refine ⟨47756211218025947655613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254699793162805054163269 47756211218025947655613)
                  ·
                    rfl

theorem cell22_418522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 5, 2, 4].length) (baseStart_418522 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418522 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418522 prefixEnd_418522 := by exact prefixLift 418522
  have htrace : WordTrace (prefixWord ++ tailWord_418522) baseStart_418522 baseEnd_418522 := by
    simpa [prefixWord, tailWord_418522, baseEnd_418522] using wordTrace_append hprefix tailTrace_418522
  have hstable : (prefixWord ++ tailWord_418522).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418522).length < 2 ^ (prefixWord ++ tailWord_418522).sum := by decide
  have hdescent : baseEnd_418522 < baseStart_418522 := by decide
  rcases family_descends (prefixWord ++ tailWord_418522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418533 : List Nat := [1, 3, 1, 4, 1, 2, 1, 9]
def baseStart_418533 : Nat := 118140960795 + 418533 * 2 ^ 59
def prefixEnd_418533 : Nat := 4983230072969 + 3 ^ 40 * 418533 * 2
def baseEnd_418533 : Nat := 15919155464319720104645

theorem tailTrace_418533 : CollatzResearch.WordTrace tailWord_418533 prefixEnd_418533 15919155464319720104645 := by
  unfold tailWord_418533
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265152592733895590716253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10176768395155930393810835 15265152592733895590716253)
  ·
    refine ⟨5724432222275210846518595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15265152592733895590716253 5724432222275210846518595)
    ·
      refine ⟨8586648333412816269777893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5724432222275210846518595 8586648333412816269777893)
      ·
        refine ⟨1609996562514903050583355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8586648333412816269777893 1609996562514903050583355)
        ·
          refine ⟨2414994843772354575875033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1609996562514903050583355 2414994843772354575875033)
          ·
            refine ⟨1811246132829265931906275, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2414994843772354575875033 1811246132829265931906275)
            ·
              refine ⟨2716869199243898897859413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1811246132829265931906275 2716869199243898897859413)
              ·
                refine ⟨15919155464319720104645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2716869199243898897859413 15919155464319720104645)
                ·
                  rfl

theorem cell22_418533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 2, 1, 9].length) (baseStart_418533 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418533 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418533 prefixEnd_418533 := by exact prefixLift 418533
  have htrace : WordTrace (prefixWord ++ tailWord_418533) baseStart_418533 baseEnd_418533 := by
    simpa [prefixWord, tailWord_418533, baseEnd_418533] using wordTrace_append hprefix tailTrace_418533
  have hstable : (prefixWord ++ tailWord_418533).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418533).length < 2 ^ (prefixWord ++ tailWord_418533).sum := by decide
  have hdescent : baseEnd_418533 < baseStart_418533 := by decide
  rcases family_descends (prefixWord ++ tailWord_418533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418537 : List Nat := [1, 2, 1, 1, 1, 2, 8, 1, 2, 3]
def baseStart_418537 : Nat := 118140960795 + 418537 * 2 ^ 59
def prefixEnd_418537 : Nat := 4983230072969 + 3 ^ 40 * 418537 * 2
def baseEnd_418537 : Nat := 143273768460622803841793

theorem tailTrace_418537 : CollatzResearch.WordTrace tailWord_418537 prefixEnd_418537 143273768460622803841793 := by
  unfold tailWord_418537
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265298484719404273861865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10176865656479602849241243 15265298484719404273861865)
  ·
    refine ⟨11448973863539553205396399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15265298484719404273861865 11448973863539553205396399)
    ·
      refine ⟨17173460795309329808094599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448973863539553205396399 17173460795309329808094599)
      ·
        refine ⟨25760191192963994712141899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17173460795309329808094599 25760191192963994712141899)
        ·
          refine ⟨38640286789445992068212849, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25760191192963994712141899 38640286789445992068212849)
          ·
            refine ⟨28980215092084494051159637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38640286789445992068212849 28980215092084494051159637)
            ·
              refine ⟨339611895610365164662027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 28980215092084494051159637 339611895610365164662027)
              ·
                refine ⟨509417843415547746993041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 339611895610365164662027 509417843415547746993041)
                ·
                  refine ⟨382063382561660810244781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509417843415547746993041 382063382561660810244781)
                  ·
                    refine ⟨143273768460622803841793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382063382561660810244781 143273768460622803841793)
                    ·
                      rfl

theorem cell22_418537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 8, 1, 2, 3].length) (baseStart_418537 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418537 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418537 prefixEnd_418537 := by exact prefixLift 418537
  have htrace : WordTrace (prefixWord ++ tailWord_418537) baseStart_418537 baseEnd_418537 := by
    simpa [prefixWord, tailWord_418537, baseEnd_418537] using wordTrace_append hprefix tailTrace_418537
  have hstable : (prefixWord ++ tailWord_418537).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418537).length < 2 ^ (prefixWord ++ tailWord_418537).sum := by decide
  have hdescent : baseEnd_418537 < baseStart_418537 := by decide
  rcases family_descends (prefixWord ++ tailWord_418537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418706 : List Nat := [3, 2, 3, 2, 2, 1, 1, 3, 2, 3]
def baseStart_418706 : Nat := 118140960795 + 418706 * 2 ^ 59
def prefixEnd_418706 : Nat := 4983230072969 + 3 ^ 40 * 418706 * 2
def baseEnd_418706 : Nat := 143331620614362696366275

theorem tailTrace_418706 : CollatzResearch.WordTrace tailWord_418706 prefixEnd_418706 143331620614362696366275 := by
  unfold tailWord_418706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3817865605276786534190993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10180974947404764091175981 3817865605276786534190993)
  ·
    refine ⟨2863399203957589900643245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3817865605276786534190993 2863399203957589900643245)
    ·
      refine ⟨1073774701484096212741217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2863399203957589900643245 1073774701484096212741217)
      ·
        refine ⟨805331026113072159555913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1073774701484096212741217 805331026113072159555913)
        ·
          refine ⟨603998269584804119666935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 805331026113072159555913 603998269584804119666935)
          ·
            refine ⟨905997404377206179500403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 603998269584804119666935 905997404377206179500403)
            ·
              refine ⟨1358996106565809269250605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 905997404377206179500403 1358996106565809269250605)
              ·
                refine ⟨509623539962178475968977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1358996106565809269250605 509623539962178475968977)
                ·
                  refine ⟨382217654971633856976733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 509623539962178475968977 382217654971633856976733)
                  ·
                    refine ⟨143331620614362696366275, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382217654971633856976733 143331620614362696366275)
                    ·
                      rfl

theorem cell22_418706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 2, 1, 1, 3, 2, 3].length) (baseStart_418706 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418706 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418706 prefixEnd_418706 := by exact prefixLift 418706
  have htrace : WordTrace (prefixWord ++ tailWord_418706) baseStart_418706 baseEnd_418706 := by
    simpa [prefixWord, tailWord_418706, baseEnd_418706] using wordTrace_append hprefix tailTrace_418706
  have hstable : (prefixWord ++ tailWord_418706).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418706).length < 2 ^ (prefixWord ++ tailWord_418706).sum := by decide
  have hdescent : baseEnd_418706 < baseStart_418706 := by decide
  rcases family_descends (prefixWord ++ tailWord_418706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418717 : List Nat := [1, 4, 2, 1, 2, 1, 2, 1, 5, 3]
def baseStart_418717 : Nat := 118140960795 + 418717 * 2 ^ 59
def prefixEnd_418717 : Nat := 4983230072969 + 3 ^ 40 * 418717 * 2
def baseEnd_418717 : Nat := 143335386139162334341241

theorem tailTrace_418717 : CollatzResearch.WordTrace tailWord_418717 prefixEnd_418717 143335386139162334341241 := by
  unfold tailWord_418717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15271863624067295015414405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10181242416044863343609603 15271863624067295015414405)
  ·
    refine ⟨2863474429512617815390201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15271863624067295015414405 2863474429512617815390201)
    ·
      refine ⟨2147605822134463361542651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2863474429512617815390201 2147605822134463361542651)
      ·
        refine ⟨3221408733201695042313977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147605822134463361542651 3221408733201695042313977)
        ·
          refine ⟨2416056549901271281735483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221408733201695042313977 2416056549901271281735483)
          ·
            refine ⟨3624084824851906922603225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416056549901271281735483 3624084824851906922603225)
            ·
              refine ⟨2718063618638930191952419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624084824851906922603225 2718063618638930191952419)
              ·
                refine ⟨4077095427958395287928629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718063618638930191952419 4077095427958395287928629)
                ·
                  refine ⟨382227696371099558243309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4077095427958395287928629 382227696371099558243309)
                  ·
                    refine ⟨143335386139162334341241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382227696371099558243309 143335386139162334341241)
                    ·
                      rfl

theorem cell22_418717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 2, 1, 5, 3].length) (baseStart_418717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418717 prefixEnd_418717 := by exact prefixLift 418717
  have htrace : WordTrace (prefixWord ++ tailWord_418717) baseStart_418717 baseEnd_418717 := by
    simpa [prefixWord, tailWord_418717, baseEnd_418717] using wordTrace_append hprefix tailTrace_418717
  have hstable : (prefixWord ++ tailWord_418717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418717).length < 2 ^ (prefixWord ++ tailWord_418717).sum := by decide
  have hdescent : baseEnd_418717 < baseStart_418717 := by decide
  rcases family_descends (prefixWord ++ tailWord_418717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418742 : List Nat := [5, 1, 4, 1, 1, 2, 2, 2, 4]
def baseStart_418742 : Nat := 118140960795 + 418742 * 2 ^ 59
def prefixEnd_418742 : Nat := 4983230072969 + 3 ^ 40 * 418742 * 2
def baseEnd_418742 : Nat := 47781314716690200822055

theorem tailTrace_418742 : CollatzResearch.WordTrace tailWord_418742 prefixEnd_418742 47781314716690200822055 := by
  unfold tailWord_418742
  simp only [CollatzResearch.WordTrace]
  refine ⟨954548465561045267817155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10181850299317816190049653 954548465561045267817155)
  ·
    refine ⟨1431822698341567901725733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 954548465561045267817155 1431822698341567901725733)
    ·
      refine ⟨268466755939043981573575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1431822698341567901725733 268466755939043981573575)
      ·
        refine ⟨402700133908565972360363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 268466755939043981573575 402700133908565972360363)
        ·
          refine ⟨604050200862848958540545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402700133908565972360363 604050200862848958540545)
          ·
            refine ⟨453037650647136718905409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 604050200862848958540545 453037650647136718905409)
            ·
              refine ⟨339778237985352539179057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453037650647136718905409 339778237985352539179057)
              ·
                refine ⟨254833678489014404384293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 339778237985352539179057 254833678489014404384293)
                ·
                  refine ⟨47781314716690200822055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 254833678489014404384293 47781314716690200822055)
                  ·
                    rfl

theorem cell22_418742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 2, 2, 2, 4].length) (baseStart_418742 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418742 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418742 prefixEnd_418742 := by exact prefixLift 418742
  have htrace : WordTrace (prefixWord ++ tailWord_418742) baseStart_418742 baseEnd_418742 := by
    simpa [prefixWord, tailWord_418742, baseEnd_418742] using wordTrace_append hprefix tailTrace_418742
  have hstable : (prefixWord ++ tailWord_418742).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418742).length < 2 ^ (prefixWord ++ tailWord_418742).sum := by decide
  have hdescent : baseEnd_418742 < baseStart_418742 := by decide
  rcases family_descends (prefixWord ++ tailWord_418742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418777 : List Nat := [1, 2, 1, 2, 5, 1, 2, 1, 3, 4]
def baseStart_418777 : Nat := 118140960795 + 418777 * 2 ^ 59
def prefixEnd_418777 : Nat := 4983230072969 + 3 ^ 40 * 418777 * 2
def baseEnd_418777 : Nat := 143355925365342177841057

theorem tailTrace_418777 : CollatzResearch.WordTrace tailWord_418777 prefixEnd_418777 143355925365342177841057 := by
  unfold tailWord_418777
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274052003849925262598585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10182701335899950175065723 15274052003849925262598585)
  ·
    refine ⟨11455539002887443946948939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15274052003849925262598585 11455539002887443946948939)
    ·
      refine ⟨17183308504331165920423409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11455539002887443946948939 17183308504331165920423409)
      ·
        refine ⟨12887481378248374440317557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17183308504331165920423409 12887481378248374440317557)
        ·
          refine ⟨1208201379210785103779771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 12887481378248374440317557 1208201379210785103779771)
          ·
            refine ⟨1812302068816177655669657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208201379210785103779771 1812302068816177655669657)
            ·
              refine ⟨1359226551612133241752243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1812302068816177655669657 1359226551612133241752243)
              ·
                refine ⟨2038839827418199862628365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1359226551612133241752243 2038839827418199862628365)
                ·
                  refine ⟨764564935281824948485637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2038839827418199862628365 764564935281824948485637)
                  ·
                    refine ⟨143355925365342177841057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 764564935281824948485637 143355925365342177841057)
                    ·
                      rfl

theorem cell22_418777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 1, 2, 1, 3, 4].length) (baseStart_418777 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418777 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418777 prefixEnd_418777 := by exact prefixLift 418777
  have htrace : WordTrace (prefixWord ++ tailWord_418777) baseStart_418777 baseEnd_418777 := by
    simpa [prefixWord, tailWord_418777, baseEnd_418777] using wordTrace_append hprefix tailTrace_418777
  have hstable : (prefixWord ++ tailWord_418777).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418777).length < 2 ^ (prefixWord ++ tailWord_418777).sum := by decide
  have hdescent : baseEnd_418777 < baseStart_418777 := by decide
  rcases family_descends (prefixWord ++ tailWord_418777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418794 : List Nat := [3, 1, 3, 1, 2, 3, 1, 3, 1, 4]
def baseStart_418794 : Nat := 118140960795 + 418794 * 2 ^ 59
def prefixEnd_418794 : Nat := 4983230072969 + 3 ^ 40 * 418794 * 2
def baseEnd_418794 : Nat := 143361744812759800166005

theorem tailTrace_418794 : CollatzResearch.WordTrace tailWord_418794 prefixEnd_418794 143361744812759800166005 := by
  unfold tailWord_418794
  simp only [CollatzResearch.WordTrace]
  refine ⟨3818668011197084291491859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10183114696525558110644957 3818668011197084291491859)
  ·
    refine ⟨5728002016795626437237789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3818668011197084291491859 5728002016795626437237789)
    ·
      refine ⟨2148000756298359913964171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5728002016795626437237789 2148000756298359913964171)
      ·
        refine ⟨3222001134447539870946257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2148000756298359913964171 3222001134447539870946257)
        ·
          refine ⟨2416500850835654903209693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222001134447539870946257 2416500850835654903209693)
          ·
            refine ⟨906187819063370588703635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2416500850835654903209693 906187819063370588703635)
            ·
              refine ⟨1359281728595055883055453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906187819063370588703635 1359281728595055883055453)
              ·
                refine ⟨509730648223145956145795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1359281728595055883055453 509730648223145956145795)
                ·
                  refine ⟨764595972334718934218693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 509730648223145956145795 764595972334718934218693)
                  ·
                    refine ⟨143361744812759800166005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 764595972334718934218693 143361744812759800166005)
                    ·
                      rfl

theorem cell22_418794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 2, 3, 1, 3, 1, 4].length) (baseStart_418794 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418794 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418794 prefixEnd_418794 := by exact prefixLift 418794
  have htrace : WordTrace (prefixWord ++ tailWord_418794) baseStart_418794 baseEnd_418794 := by
    simpa [prefixWord, tailWord_418794, baseEnd_418794] using wordTrace_append hprefix tailTrace_418794
  have hstable : (prefixWord ++ tailWord_418794).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418794).length < 2 ^ (prefixWord ++ tailWord_418794).sum := by decide
  have hdescent : baseEnd_418794 < baseStart_418794 := by decide
  rcases family_descends (prefixWord ++ tailWord_418794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418824 : List Nat := [2, 1, 3, 2, 1, 5, 1, 1, 1, 5]
def baseStart_418824 : Nat := 118140960795 + 418824 * 2 ^ 59
def prefixEnd_418824 : Nat := 4983230072969 + 3 ^ 40 * 418824 * 2
def baseEnd_418824 : Nat := 143372014425849721915913

theorem tailTrace_418824 : CollatzResearch.WordTrace tailWord_418824 prefixEnd_418824 143372014425849721915913 := by
  unfold tailWord_418824
  simp only [CollatzResearch.WordTrace]
  refine ⟨7637883117339826144779763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10183844156453101526373017 7637883117339826144779763)
  ·
    refine ⟨11456824676009739217169645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7637883117339826144779763 11456824676009739217169645)
    ·
      refine ⟨4296309253503652206438617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11456824676009739217169645 4296309253503652206438617)
      ·
        refine ⟨3222231940127739154828963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4296309253503652206438617 3222231940127739154828963)
        ·
          refine ⟨4833347910191608732243445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222231940127739154828963 4833347910191608732243445)
          ·
            refine ⟨453126366580463318647823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4833347910191608732243445 453126366580463318647823)
            ·
              refine ⟨679689549870694977971735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453126366580463318647823 679689549870694977971735)
              ·
                refine ⟨1019534324806042466957603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 679689549870694977971735 1019534324806042466957603)
                ·
                  refine ⟨1529301487209063700436405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1019534324806042466957603 1529301487209063700436405)
                  ·
                    refine ⟨143372014425849721915913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1529301487209063700436405 143372014425849721915913)
                    ·
                      rfl

theorem cell22_418824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 5, 1, 1, 1, 5].length) (baseStart_418824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418824 prefixEnd_418824 := by exact prefixLift 418824
  have htrace : WordTrace (prefixWord ++ tailWord_418824) baseStart_418824 baseEnd_418824 := by
    simpa [prefixWord, tailWord_418824, baseEnd_418824] using wordTrace_append hprefix tailTrace_418824
  have hstable : (prefixWord ++ tailWord_418824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418824).length < 2 ^ (prefixWord ++ tailWord_418824).sum := by decide
  have hdescent : baseEnd_418824 < baseStart_418824 := by decide
  rcases family_descends (prefixWord ++ tailWord_418824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418835 : List Nat := [1, 1, 1, 2, 1, 4, 1, 1, 1, 9]
def baseStart_418835 : Nat := 118140960795 + 418835 * 2 ^ 59
def prefixEnd_418835 : Nat := 4983230072969 + 3 ^ 40 * 418835 * 2
def baseEnd_418835 : Nat := 143375779950649359890879

theorem tailTrace_418835 : CollatzResearch.WordTrace tailWord_418835 prefixEnd_418835 143375779950649359890879 := by
  unfold tailWord_418835
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276167437639801168209959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10184111625093200778806639 15276167437639801168209959)
  ·
    refine ⟨22914251156459701752314939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15276167437639801168209959 22914251156459701752314939)
    ·
      refine ⟨34371376734689552628472409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22914251156459701752314939 34371376734689552628472409)
      ·
        refine ⟨25778532551017164471354307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34371376734689552628472409 25778532551017164471354307)
        ·
          refine ⟨38667798826525746707031461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25778532551017164471354307 38667798826525746707031461)
          ·
            refine ⟨7250212279973577507568399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38667798826525746707031461 7250212279973577507568399)
            ·
              refine ⟨10875318419960366261352599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250212279973577507568399 10875318419960366261352599)
              ·
                refine ⟨16312977629940549392028899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10875318419960366261352599 16312977629940549392028899)
                ·
                  refine ⟨24469466444910824088043349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16312977629940549392028899 24469466444910824088043349)
                  ·
                    refine ⟨143375779950649359890879, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 24469466444910824088043349 143375779950649359890879)
                    ·
                      rfl

theorem cell22_418835_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 1, 1, 1, 9].length) (baseStart_418835 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418835 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418835 prefixEnd_418835 := by exact prefixLift 418835
  have htrace : WordTrace (prefixWord ++ tailWord_418835) baseStart_418835 baseEnd_418835 := by
    simpa [prefixWord, tailWord_418835, baseEnd_418835] using wordTrace_append hprefix tailTrace_418835
  have hstable : (prefixWord ++ tailWord_418835).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418835).length < 2 ^ (prefixWord ++ tailWord_418835).sum := by decide
  have hdescent : baseEnd_418835 < baseStart_418835 := by decide
  rcases family_descends (prefixWord ++ tailWord_418835) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418837 : List Nat := [1, 3, 2, 1, 4, 2, 1, 8]
def baseStart_418837 : Nat := 118140960795 + 418837 * 2 ^ 59
def prefixEnd_418837 : Nat := 4983230072969 + 3 ^ 40 * 418837 * 2
def baseEnd_418837 : Nat := 15930718287946891260097

theorem tailTrace_418837 : CollatzResearch.WordTrace tailWord_418837 prefixEnd_418837 15930718287946891260097 := by
  unfold tailWord_418837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15276240383632555509782765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10184160255755037006521843 15276240383632555509782765)
  ·
    refine ⟨5728590143862208316168537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15276240383632555509782765 5728590143862208316168537)
    ·
      refine ⟨4296442607896656237126403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5728590143862208316168537 4296442607896656237126403)
      ·
        refine ⟨6444663911844984355689605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4296442607896656237126403 6444663911844984355689605)
        ·
          refine ⟨1208374483470934566691801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 6444663911844984355689605 1208374483470934566691801)
          ·
            refine ⟨906280862603200925018851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1208374483470934566691801 906280862603200925018851)
            ·
              refine ⟨1359421293904801387528277, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906280862603200925018851 1359421293904801387528277)
              ·
                refine ⟨15930718287946891260097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1359421293904801387528277 15930718287946891260097)
                ·
                  rfl

theorem cell22_418837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 4, 2, 1, 8].length) (baseStart_418837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418837 prefixEnd_418837 := by exact prefixLift 418837
  have htrace : WordTrace (prefixWord ++ tailWord_418837) baseStart_418837 baseEnd_418837 := by
    simpa [prefixWord, tailWord_418837, baseEnd_418837] using wordTrace_append hprefix tailTrace_418837
  have hstable : (prefixWord ++ tailWord_418837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418837).length < 2 ^ (prefixWord ++ tailWord_418837).sum := by decide
  have hdescent : baseEnd_418837 < baseStart_418837 := by decide
  rcases family_descends (prefixWord ++ tailWord_418837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418920 : List Nat := [2, 1, 4, 4, 1, 1, 1, 4, 1, 3]
def baseStart_418920 : Nat := 118140960795 + 418920 * 2 ^ 59
def prefixEnd_418920 : Nat := 4983230072969 + 3 ^ 40 * 418920 * 2
def baseEnd_418920 : Nat := 143404877187737471515619

theorem tailTrace_418920 : CollatzResearch.WordTrace tailWord_418920 prefixEnd_418920 143404877187737471515619 := by
  unfold tailWord_418920
  simp only [CollatzResearch.WordTrace]
  refine ⟨7639633821165930342527107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10186178428221240456702809 7639633821165930342527107)
  ·
    refine ⟨11459450731748895513790661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7639633821165930342527107 11459450731748895513790661)
    ·
      refine ⟨2148647012202917908835749, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11459450731748895513790661 2148647012202917908835749)
      ·
        refine ⟨402871314788047107906703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 2148647012202917908835749 402871314788047107906703)
        ·
          refine ⟨604306972182070661860055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 402871314788047107906703 604306972182070661860055)
          ·
            refine ⟨906460458273105992790083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 604306972182070661860055 906460458273105992790083)
            ·
              refine ⟨1359690687409658989185125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 906460458273105992790083 1359690687409658989185125)
              ·
                refine ⟨254942003889311060472211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1359690687409658989185125 254942003889311060472211)
                ·
                  refine ⟨382413005833966590708317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 254942003889311060472211 382413005833966590708317)
                  ·
                    refine ⟨143404877187737471515619, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382413005833966590708317 143404877187737471515619)
                    ·
                      rfl

theorem cell22_418920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 4, 1, 1, 1, 4, 1, 3].length) (baseStart_418920 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418920 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418920 prefixEnd_418920 := by exact prefixLift 418920
  have htrace : WordTrace (prefixWord ++ tailWord_418920) baseStart_418920 baseEnd_418920 := by
    simpa [prefixWord, tailWord_418920, baseEnd_418920] using wordTrace_append hprefix tailTrace_418920
  have hstable : (prefixWord ++ tailWord_418920).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418920).length < 2 ^ (prefixWord ++ tailWord_418920).sum := by decide
  have hdescent : baseEnd_418920 < baseStart_418920 := by decide
  rcases family_descends (prefixWord ++ tailWord_418920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_418927 : List Nat := [1, 1, 2, 1, 3, 3, 2, 3, 6]
def baseStart_418927 : Nat := 118140960795 + 418927 * 2 ^ 59
def prefixEnd_418927 : Nat := 4983230072969 + 3 ^ 40 * 418927 * 2
def baseEnd_418927 : Nat := 47802424476930595530199

theorem tailTrace_418927 : CollatzResearch.WordTrace tailWord_418927 prefixEnd_418927 47802424476930595530199 := by
  unfold tailWord_418927
  simp only [CollatzResearch.WordTrace]
  refine ⟨15279522953306500880559035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10186348635537667253706023 15279522953306500880559035)
  ·
    refine ⟨22919284429959751320838553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15279522953306500880559035 22919284429959751320838553)
    ·
      refine ⟨17189463322469813490628915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22919284429959751320838553 17189463322469813490628915)
      ·
        refine ⟨25784194983704720235943373, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189463322469813490628915 25784194983704720235943373)
        ·
          refine ⟨9669073118889270088478765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25784194983704720235943373 9669073118889270088478765)
          ·
            refine ⟨3625902419583476283179537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9669073118889270088478765 3625902419583476283179537)
            ·
              refine ⟨2719426814687607212384653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625902419583476283179537 2719426814687607212384653)
              ·
                refine ⟨1019785055507852704644245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2719426814687607212384653 1019785055507852704644245)
                ·
                  refine ⟨47802424476930595530199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1019785055507852704644245 47802424476930595530199)
                  ·
                    rfl

theorem cell22_418927_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 3, 2, 3, 6].length) (baseStart_418927 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_418927 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_418927 prefixEnd_418927 := by exact prefixLift 418927
  have htrace : WordTrace (prefixWord ++ tailWord_418927) baseStart_418927 baseEnd_418927 := by
    simpa [prefixWord, tailWord_418927, baseEnd_418927] using wordTrace_append hprefix tailTrace_418927
  have hstable : (prefixWord ++ tailWord_418927).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_418927).length < 2 ^ (prefixWord ++ tailWord_418927).sum := by decide
  have hdescent : baseEnd_418927 < baseStart_418927 := by decide
  rcases family_descends (prefixWord ++ tailWord_418927) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419006 : List Nat := [4, 2, 1, 1, 3, 1, 4, 6]
def baseStart_419006 : Nat := 118140960795 + 419006 * 2 ^ 59
def prefixEnd_419006 : Nat := 4983230072969 + 3 ^ 40 * 419006 * 2
def baseEnd_419006 : Nat := 15937146305029101540595

theorem tailTrace_419006 : CollatzResearch.WordTrace tailWord_419006 prefixEnd_419006 15937146305029101540595 := by
  unfold tailWord_419006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1910300540002537171585609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10188269546680198248456581 1910300540002537171585609)
  ·
    refine ⟨1432725405001902878689207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1910300540002537171585609 1432725405001902878689207)
    ·
      refine ⟨2149088107502854318033811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1432725405001902878689207 2149088107502854318033811)
      ·
        refine ⟨3223632161254281477050717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149088107502854318033811 3223632161254281477050717)
        ·
          refine ⟨1208862060470355553894019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 3223632161254281477050717 1208862060470355553894019)
          ·
            refine ⟨1813293090705533330841029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1208862060470355553894019 1813293090705533330841029)
            ·
              refine ⟨339992454507287499532693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1813293090705533330841029 339992454507287499532693)
              ·
                refine ⟨15937146305029101540595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 339992454507287499532693 15937146305029101540595)
                ·
                  rfl

theorem cell22_419006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 3, 1, 4, 6].length) (baseStart_419006 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419006 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419006 prefixEnd_419006 := by exact prefixLift 419006
  have htrace : WordTrace (prefixWord ++ tailWord_419006) baseStart_419006 baseEnd_419006 := by
    simpa [prefixWord, tailWord_419006, baseEnd_419006] using wordTrace_append hprefix tailTrace_419006
  have hstable : (prefixWord ++ tailWord_419006).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419006).length < 2 ^ (prefixWord ++ tailWord_419006).sum := by decide
  have hdescent : baseEnd_419006 < baseStart_419006 := by decide
  rcases family_descends (prefixWord ++ tailWord_419006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419034 : List Nat := [3, 1, 1, 2, 2, 1, 1, 6, 5]
def baseStart_419034 : Nat := 118140960795 + 419034 * 2 ^ 59
def prefixEnd_419034 : Nat := 4983230072969 + 3 ^ 40 * 419034 * 2
def baseEnd_419034 : Nat := 47814633905826391388423

theorem tailTrace_419034 : CollatzResearch.WordTrace tailWord_419034 prefixEnd_419034 47814633905826391388423 := by
  unfold tailWord_419034
  simp only [CollatzResearch.WordTrace]
  refine ⟨3820856390979714538676039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10188950375945905436469437 3820856390979714538676039)
  ·
    refine ⟨5731284586469571808014059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3820856390979714538676039 5731284586469571808014059)
    ·
      refine ⟨8596926879704357712021089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5731284586469571808014059 8596926879704357712021089)
      ·
        refine ⟨6447695159778268284015817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8596926879704357712021089 6447695159778268284015817)
        ·
          refine ⟨4835771369833701213011863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6447695159778268284015817 4835771369833701213011863)
          ·
            refine ⟨7253657054750551819517795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4835771369833701213011863 7253657054750551819517795)
            ·
              refine ⟨10880485582125827729276693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7253657054750551819517795 10880485582125827729276693)
              ·
                refine ⟨510022761662148174809845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 10880485582125827729276693 510022761662148174809845)
                ·
                  refine ⟨47814633905826391388423, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510022761662148174809845 47814633905826391388423)
                  ·
                    rfl

theorem cell22_419034_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 1, 6, 5].length) (baseStart_419034 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419034 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419034 prefixEnd_419034 := by exact prefixLift 419034
  have htrace : WordTrace (prefixWord ++ tailWord_419034) baseStart_419034 baseEnd_419034 := by
    simpa [prefixWord, tailWord_419034, baseEnd_419034] using wordTrace_append hprefix tailTrace_419034
  have hstable : (prefixWord ++ tailWord_419034).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419034).length < 2 ^ (prefixWord ++ tailWord_419034).sum := by decide
  have hdescent : baseEnd_419034 < baseStart_419034 := by decide
  rcases family_descends (prefixWord ++ tailWord_419034) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419051 : List Nat := [1, 1, 1, 1, 2, 6, 4, 1, 5]
def baseStart_419051 : Nat := 118140960795 + 419051 * 2 ^ 59
def prefixEnd_419051 : Nat := 4983230072969 + 3 ^ 40 * 419051 * 2
def baseEnd_419051 : Nat := 47816573721632265496739

theorem tailTrace_419051 : CollatzResearch.WordTrace tailWord_419051 prefixEnd_419051 47816573721632265496739 := by
  unfold tailWord_419051
  simp only [CollatzResearch.WordTrace]
  refine ⟨15284045604857270058073007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10189363736571513372048671 15284045604857270058073007)
  ·
    refine ⟨22926068407285905087109511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15284045604857270058073007 22926068407285905087109511)
    ·
      refine ⟨34389102610928857630664267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22926068407285905087109511 34389102610928857630664267)
      ·
        refine ⟨51583653916393286445996401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34389102610928857630664267 51583653916393286445996401)
        ·
          refine ⟨38687740437294964834497301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51583653916393286445996401 38687740437294964834497301)
          ·
            refine ⟨1813487832998201476617061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 38687740437294964834497301 1813487832998201476617061)
            ·
              refine ⟨340028968687162776865699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1813487832998201476617061 340028968687162776865699)
              ·
                refine ⟨510043453030744165298549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340028968687162776865699 510043453030744165298549)
                ·
                  refine ⟨47816573721632265496739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510043453030744165298549 47816573721632265496739)
                  ·
                    rfl

theorem cell22_419051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 4, 1, 5].length) (baseStart_419051 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419051 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419051 prefixEnd_419051 := by exact prefixLift 419051
  have htrace : WordTrace (prefixWord ++ tailWord_419051) baseStart_419051 baseEnd_419051 := by
    simpa [prefixWord, tailWord_419051, baseEnd_419051] using wordTrace_append hprefix tailTrace_419051
  have hstable : (prefixWord ++ tailWord_419051).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419051).length < 2 ^ (prefixWord ++ tailWord_419051).sum := by decide
  have hdescent : baseEnd_419051 < baseStart_419051 := by decide
  rcases family_descends (prefixWord ++ tailWord_419051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419175 : List Nat := [1, 1, 5, 1, 5, 1, 2, 6]
def baseStart_419175 : Nat := 118140960795 + 419175 * 2 ^ 59
def prefixEnd_419175 : Nat := 4983230072969 + 3 ^ 40 * 419175 * 2
def baseEnd_419175 : Nat := 15943574322111311821093

theorem tailTrace_419175 : CollatzResearch.WordTrace tailWord_419175 prefixEnd_419175 15943574322111311821093 := by
  unfold tailWord_419175
  simp only [CollatzResearch.WordTrace]
  refine ⟨15288568256408039235586979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10192378837605359490391319 15288568256408039235586979)
  ·
    refine ⟨22932852384612058853380469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15288568256408039235586979 22932852384612058853380469)
    ·
      refine ⟨2149954911057380517504419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 22932852384612058853380469 2149954911057380517504419)
      ·
        refine ⟨3224932366586070776256629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2149954911057380517504419 3224932366586070776256629)
        ·
          refine ⟨302337409367444135274059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 3224932366586070776256629 302337409367444135274059)
          ·
            refine ⟨453506114051166202911089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302337409367444135274059 453506114051166202911089)
            ·
              refine ⟨340129585538374652183317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453506114051166202911089 340129585538374652183317)
              ·
                refine ⟨15943574322111311821093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 340129585538374652183317 15943574322111311821093)
                ·
                  rfl

theorem cell22_419175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 5, 1, 2, 6].length) (baseStart_419175 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419175 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419175 prefixEnd_419175 := by exact prefixLift 419175
  have htrace : WordTrace (prefixWord ++ tailWord_419175) baseStart_419175 baseEnd_419175 := by
    simpa [prefixWord, tailWord_419175, baseEnd_419175] using wordTrace_append hprefix tailTrace_419175
  have hstable : (prefixWord ++ tailWord_419175).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419175).length < 2 ^ (prefixWord ++ tailWord_419175).sum := by decide
  have hdescent : baseEnd_419175 < baseStart_419175 := by decide
  rcases family_descends (prefixWord ++ tailWord_419175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419207 : List Nat := [1, 1, 4, 2, 2, 3, 3, 2, 1, 3]
def baseStart_419207 : Nat := 118140960795 + 419207 * 2 ^ 59
def prefixEnd_419207 : Nat := 4983230072969 + 3 ^ 40 * 419207 * 2
def baseEnd_419207 : Nat := 143503123152964389589739

theorem tailTrace_419207 : CollatzResearch.WordTrace tailWord_419207 prefixEnd_419207 143503123152964389589739 := by
  unfold tailWord_419207
  simp only [CollatzResearch.WordTrace]
  refine ⟨15289735392292108700751875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10193156928194739133834583 15289735392292108700751875)
  ·
    refine ⟨22934603088438163051127813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15289735392292108700751875 22934603088438163051127813)
    ·
      refine ⟨4300238079082155572086465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22934603088438163051127813 4300238079082155572086465)
      ·
        refine ⟨3225178559311616679064849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4300238079082155572086465 3225178559311616679064849)
        ·
          refine ⟨2418883919483712509298637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3225178559311616679064849 2418883919483712509298637)
          ·
            refine ⟨907081469806392190986989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2418883919483712509298637 907081469806392190986989)
            ·
              refine ⟨340155551177397071620121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 907081469806392190986989 340155551177397071620121)
              ·
                refine ⟨255116663383047803715091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340155551177397071620121 255116663383047803715091)
                ·
                  refine ⟨382674995074571705572637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255116663383047803715091 382674995074571705572637)
                  ·
                    refine ⟨143503123152964389589739, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382674995074571705572637 143503123152964389589739)
                    ·
                      rfl

theorem cell22_419207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 3, 3, 2, 1, 3].length) (baseStart_419207 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419207 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419207 prefixEnd_419207 := by exact prefixLift 419207
  have htrace : WordTrace (prefixWord ++ tailWord_419207) baseStart_419207 baseEnd_419207 := by
    simpa [prefixWord, tailWord_419207, baseEnd_419207] using wordTrace_append hprefix tailTrace_419207
  have hstable : (prefixWord ++ tailWord_419207).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419207).length < 2 ^ (prefixWord ++ tailWord_419207).sum := by decide
  have hdescent : baseEnd_419207 < baseStart_419207 := by decide
  rcases family_descends (prefixWord ++ tailWord_419207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419220 : List Nat := [2, 4, 2, 1, 2, 1, 4, 1, 5]
def baseStart_419220 : Nat := 118140960795 + 419220 * 2 ^ 59
def prefixEnd_419220 : Nat := 4983230072969 + 3 ^ 40 * 419220 * 2
def baseEnd_419220 : Nat := 47835857772878896338233

theorem tailTrace_419220 : CollatzResearch.WordTrace tailWord_419220 prefixEnd_419220 47835857772878896338233 := by
  unfold tailWord_419220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7645104770622505960487557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10193473027496674613983409 7645104770622505960487557)
  ·
    refine ⟨1433457144491719867591417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7645104770622505960487557 1433457144491719867591417)
    ·
      refine ⟨1075092858368789900693563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1433457144491719867591417 1075092858368789900693563)
      ·
        refine ⟨1612639287553184851040345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1075092858368789900693563 1612639287553184851040345)
        ·
          refine ⟨1209479465664888638280259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1612639287553184851040345 1209479465664888638280259)
          ·
            refine ⟨1814219198497332957420389, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1209479465664888638280259 1814219198497332957420389)
            ·
              refine ⟨340166099718249929516323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1814219198497332957420389 340166099718249929516323)
              ·
                refine ⟨510249149577374894274485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340166099718249929516323 510249149577374894274485)
                ·
                  refine ⟨47835857772878896338233, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510249149577374894274485 47835857772878896338233)
                  ·
                    rfl

theorem cell22_419220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 4, 1, 5].length) (baseStart_419220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419220 prefixEnd_419220 := by exact prefixLift 419220
  have htrace : WordTrace (prefixWord ++ tailWord_419220) baseStart_419220 baseEnd_419220 := by
    simpa [prefixWord, tailWord_419220, baseEnd_419220] using wordTrace_append hprefix tailTrace_419220
  have hstable : (prefixWord ++ tailWord_419220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419220).length < 2 ^ (prefixWord ++ tailWord_419220).sum := by decide
  have hdescent : baseEnd_419220 < baseStart_419220 := by decide
  rcases family_descends (prefixWord ++ tailWord_419220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419325 : List Nat := [1, 4, 1, 1, 1, 5, 2, 1, 3, 3]
def baseStart_419325 : Nat := 118140960795 + 419325 * 2 ^ 59
def prefixEnd_419325 : Nat := 4983230072969 + 3 ^ 40 * 419325 * 2
def baseEnd_419325 : Nat := 143543516964451415139377

theorem tailTrace_419325 : CollatzResearch.WordTrace tailWord_419325 prefixEnd_419325 143543516964451415139377 := by
  unfold tailWord_419325
  simp only [CollatzResearch.WordTrace]
  refine ⟨15294039205864614853547429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10196026137243076569031619 15294039205864614853547429)
  ·
    refine ⟨2867632351099615285040143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15294039205864614853547429 2867632351099615285040143)
    ·
      refine ⟨4301448526649422927560215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2867632351099615285040143 4301448526649422927560215)
      ·
        refine ⟨6452172789974134391340323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4301448526649422927560215 6452172789974134391340323)
        ·
          refine ⟨9678259184961201587010485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6452172789974134391340323 9678259184961201587010485)
          ·
            refine ⟨907336798590112648782233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9678259184961201587010485 907336798590112648782233)
            ·
              refine ⟨680502598942584486586675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 907336798590112648782233 680502598942584486586675)
              ·
                refine ⟨1020753898413876729880013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680502598942584486586675 1020753898413876729880013)
                ·
                  refine ⟨382782711905203773705005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1020753898413876729880013 382782711905203773705005)
                  ·
                    refine ⟨143543516964451415139377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382782711905203773705005 143543516964451415139377)
                    ·
                      rfl

theorem cell22_419325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 2, 1, 3, 3].length) (baseStart_419325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419325 prefixEnd_419325 := by exact prefixLift 419325
  have htrace : WordTrace (prefixWord ++ tailWord_419325) baseStart_419325 baseEnd_419325 := by
    simpa [prefixWord, tailWord_419325, baseEnd_419325] using wordTrace_append hprefix tailTrace_419325
  have hstable : (prefixWord ++ tailWord_419325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419325).length < 2 ^ (prefixWord ++ tailWord_419325).sum := by decide
  have hdescent : baseEnd_419325 < baseStart_419325 := by decide
  rcases family_descends (prefixWord ++ tailWord_419325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419383 : List Nat := [1, 1, 3, 1, 2, 4, 3, 1, 6]
def baseStart_419383 : Nat := 118140960795 + 419383 * 2 ^ 59
def prefixEnd_419383 : Nat := 4983230072969 + 3 ^ 40 * 419383 * 2
def baseEnd_419383 : Nat := 47854457183252865729733

theorem tailTrace_419383 : CollatzResearch.WordTrace tailWord_419383 prefixEnd_419383 47854457183252865729733 := by
  unfold tailWord_419383
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296154639654490759158803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10197436426436327172772535 15296154639654490759158803)
  ·
    refine ⟨22944231959481736138738205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15296154639654490759158803 22944231959481736138738205)
    ·
      refine ⟨8604086984805651052026827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22944231959481736138738205 8604086984805651052026827)
      ·
        refine ⟨12906130477208476578040241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8604086984805651052026827 12906130477208476578040241)
        ·
          refine ⟨9679597857906357433530181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12906130477208476578040241 9679597857906357433530181)
          ·
            refine ⟨1814924598357442018786909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9679597857906357433530181 1814924598357442018786909)
            ·
              refine ⟨680596724384040757045091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1814924598357442018786909 680596724384040757045091)
              ·
                refine ⟨1020895086576061135567637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680596724384040757045091 1020895086576061135567637)
                ·
                  refine ⟨47854457183252865729733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1020895086576061135567637 47854457183252865729733)
                  ·
                    rfl

theorem cell22_419383_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 3, 1, 6].length) (baseStart_419383 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419383 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419383 prefixEnd_419383 := by exact prefixLift 419383
  have htrace : WordTrace (prefixWord ++ tailWord_419383) baseStart_419383 baseEnd_419383 := by
    simpa [prefixWord, tailWord_419383, baseEnd_419383] using wordTrace_append hprefix tailTrace_419383
  have hstable : (prefixWord ++ tailWord_419383).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419383).length < 2 ^ (prefixWord ++ tailWord_419383).sum := by decide
  have hdescent : baseEnd_419383 < baseStart_419383 := by decide
  rcases family_descends (prefixWord ++ tailWord_419383) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419389 : List Nat := [1, 4, 1, 3, 4, 1, 2, 1, 5]
def baseStart_419389 : Nat := 118140960795 + 419389 * 2 ^ 59
def prefixEnd_419389 : Nat := 4983230072969 + 3 ^ 40 * 419389 * 2
def baseEnd_419389 : Nat := 47855141824125527179727

theorem tailTrace_419389 : CollatzResearch.WordTrace tailWord_419389 prefixEnd_419389 47855141824125527179727 := by
  unfold tailWord_419389
  simp only [CollatzResearch.WordTrace]
  refine ⟨15296373477632753783877221, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10197582318421835855918147 15296373477632753783877221)
  ·
    refine ⟨2868070027056141334476979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15296373477632753783877221 2868070027056141334476979)
    ·
      refine ⟨4302105040584212001715469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2868070027056141334476979 4302105040584212001715469)
      ·
        refine ⟨1613289390219079500643301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4302105040584212001715469 1613289390219079500643301)
        ·
          refine ⟨302491760666077406370619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1613289390219079500643301 302491760666077406370619)
          ·
            refine ⟨453737640999116109555929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302491760666077406370619 453737640999116109555929)
            ·
              refine ⟨340303230749337082166947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453737640999116109555929 340303230749337082166947)
              ·
                refine ⟨510454846124005623250421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340303230749337082166947 510454846124005623250421)
                ·
                  refine ⟨47855141824125527179727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510454846124005623250421 47855141824125527179727)
                  ·
                    rfl

theorem cell22_419389_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 4, 1, 2, 1, 5].length) (baseStart_419389 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419389 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419389 prefixEnd_419389 := by exact prefixLift 419389
  have htrace : WordTrace (prefixWord ++ tailWord_419389) baseStart_419389 baseEnd_419389 := by
    simpa [prefixWord, tailWord_419389, baseEnd_419389] using wordTrace_append hprefix tailTrace_419389
  have hstable : (prefixWord ++ tailWord_419389).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419389).length < 2 ^ (prefixWord ++ tailWord_419389).sum := by decide
  have hdescent : baseEnd_419389 < baseStart_419389 := by decide
  rcases family_descends (prefixWord ++ tailWord_419389) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419432 : List Nat := [2, 1, 4, 3, 1, 1, 1, 4, 2, 3]
def baseStart_419432 : Nat := 118140960795 + 419432 * 2 ^ 59
def prefixEnd_419432 : Nat := 4983230072969 + 3 ^ 40 * 419432 * 2
def baseEnd_419432 : Nat := 143580145251138802714049

theorem tailTrace_419432 : CollatzResearch.WordTrace tailWord_419432 prefixEnd_419432 143580145251138802714049 := by
  unfold tailWord_419432
  simp only [CollatzResearch.WordTrace]
  refine ⟨7648970908238486063846275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10198627877651314751795033 7648970908238486063846275)
  ·
    refine ⟨11473456362357729095769413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7648970908238486063846275 11473456362357729095769413)
    ·
      refine ⟨2151273067942074205456765, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11473456362357729095769413 2151273067942074205456765)
      ·
        refine ⟨806727400478277827046287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 2151273067942074205456765 806727400478277827046287)
        ·
          refine ⟨1210091100717416740569431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806727400478277827046287 1210091100717416740569431)
          ·
            refine ⟨1815136651076125110854147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210091100717416740569431 1815136651076125110854147)
            ·
              refine ⟨2722704976614187666281221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815136651076125110854147 2722704976614187666281221)
              ·
                refine ⟨510507183115160187427729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2722704976614187666281221 510507183115160187427729)
                ·
                  refine ⟨382880387336370140570797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510507183115160187427729 382880387336370140570797)
                  ·
                    refine ⟨143580145251138802714049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 382880387336370140570797 143580145251138802714049)
                    ·
                      rfl

theorem cell22_419432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 1, 1, 4, 2, 3].length) (baseStart_419432 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419432 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419432 prefixEnd_419432 := by exact prefixLift 419432
  have htrace : WordTrace (prefixWord ++ tailWord_419432) baseStart_419432 baseEnd_419432 := by
    simpa [prefixWord, tailWord_419432, baseEnd_419432] using wordTrace_append hprefix tailTrace_419432
  have hstable : (prefixWord ++ tailWord_419432).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419432).length < 2 ^ (prefixWord ++ tailWord_419432).sum := by decide
  have hdescent : baseEnd_419432 < baseStart_419432 := by decide
  rcases family_descends (prefixWord ++ tailWord_419432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419434 : List Nat := [3, 1, 3, 2, 1, 4, 2, 2, 4]
def baseStart_419434 : Nat := 118140960795 + 419434 * 2 ^ 59
def prefixEnd_419434 : Nat := 4983230072969 + 3 ^ 40 * 419434 * 2
def baseEnd_419434 : Nat := 47860276630670488054681

theorem tailTrace_419434 : CollatzResearch.WordTrace tailWord_419434 prefixEnd_419434 47860276630670488054681 := by
  unfold tailWord_419434
  simp only [CollatzResearch.WordTrace]
  refine ⟨3824503690617431617316339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10198676508313150979510237 3824503690617431617316339)
  ·
    refine ⟨5736755535926147425974509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3824503690617431617316339 5736755535926147425974509)
    ·
      refine ⟨2151283325972305284740441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5736755535926147425974509 2151283325972305284740441)
      ·
        refine ⟨1613462494479228963555331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2151283325972305284740441 1613462494479228963555331)
        ·
          refine ⟨2420193741718843445332997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1613462494479228963555331 2420193741718843445332997)
          ·
            refine ⟨453786326572283145999937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2420193741718843445332997 453786326572283145999937)
            ·
              refine ⟨340339744929212359499953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 453786326572283145999937 340339744929212359499953)
              ·
                refine ⟨255254808696909269624965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 340339744929212359499953 255254808696909269624965)
                ·
                  refine ⟨47860276630670488054681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255254808696909269624965 47860276630670488054681)
                  ·
                    rfl

theorem cell22_419434_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 4, 2, 2, 4].length) (baseStart_419434 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419434 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419434 prefixEnd_419434 := by exact prefixLift 419434
  have htrace : WordTrace (prefixWord ++ tailWord_419434) baseStart_419434 baseEnd_419434 := by
    simpa [prefixWord, tailWord_419434, baseEnd_419434] using wordTrace_append hprefix tailTrace_419434
  have hstable : (prefixWord ++ tailWord_419434).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419434).length < 2 ^ (prefixWord ++ tailWord_419434).sum := by decide
  have hdescent : baseEnd_419434 < baseStart_419434 := by decide
  rcases family_descends (prefixWord ++ tailWord_419434) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419445 : List Nat := [1, 3, 4, 2, 1, 1, 3, 7]
def baseStart_419445 : Nat := 118140960795 + 419445 * 2 ^ 59
def prefixEnd_419445 : Nat := 4983230072969 + 3 ^ 40 * 419445 * 2
def baseEnd_419445 : Nat := 15953843935201233571001

theorem tailTrace_419445 : CollatzResearch.WordTrace tailWord_419445 prefixEnd_419445 15953843935201233571001 := by
  unfold tailWord_419445
  simp only [CollatzResearch.WordTrace]
  refine ⟨15298415965429875347915789, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10198943976953250231943859 15298415965429875347915789)
  ·
    refine ⟨5736905987036203255468421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15298415965429875347915789 5736905987036203255468421)
    ·
      refine ⟨1075669872569288110400329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5736905987036203255468421 1075669872569288110400329)
      ·
        refine ⟨806752404426966082800247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1075669872569288110400329 806752404426966082800247)
        ·
          refine ⟨1210128606640449124200371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 806752404426966082800247 1210128606640449124200371)
          ·
            refine ⟨1815192909960673686300557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210128606640449124200371 1815192909960673686300557)
            ·
              refine ⟨680697341235252632362709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1815192909960673686300557 680697341235252632362709)
              ·
                refine ⟨15953843935201233571001, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 680697341235252632362709 15953843935201233571001)
                ·
                  rfl

theorem cell22_419445_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 1, 3, 7].length) (baseStart_419445 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419445 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419445 prefixEnd_419445 := by exact prefixLift 419445
  have htrace : WordTrace (prefixWord ++ tailWord_419445) baseStart_419445 baseEnd_419445 := by
    simpa [prefixWord, tailWord_419445, baseEnd_419445] using wordTrace_append hprefix tailTrace_419445
  have hstable : (prefixWord ++ tailWord_419445).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419445).length < 2 ^ (prefixWord ++ tailWord_419445).sum := by decide
  have hdescent : baseEnd_419445 < baseStart_419445 := by decide
  rcases family_descends (prefixWord ++ tailWord_419445) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419464 : List Nat := [2, 1, 3, 5, 1, 2, 1, 1, 2, 4]
def baseStart_419464 : Nat := 118140960795 + 419464 * 2 ^ 59
def prefixEnd_419464 : Nat := 4983230072969 + 3 ^ 40 * 419464 * 2
def baseEnd_419464 : Nat := 143591099505101385913951

theorem tailTrace_419464 : CollatzResearch.WordTrace tailWord_419464 prefixEnd_419464 143591099505101385913951 := by
  unfold tailWord_419464
  simp only [CollatzResearch.WordTrace]
  refine ⟨7649554476180520796428723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10199405968240694395238297 7649554476180520796428723)
  ·
    refine ⟨11474331714270781194643085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7649554476180520796428723 11474331714270781194643085)
    ·
      refine ⟨4302874392851542947991157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11474331714270781194643085 4302874392851542947991157)
      ·
        refine ⟨403394474329832151374171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 4302874392851542947991157 403394474329832151374171)
        ·
          refine ⟨605091711494748227061257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 403394474329832151374171 605091711494748227061257)
          ·
            refine ⟨453818783621061170295943, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605091711494748227061257 453818783621061170295943)
            ·
              refine ⟨680728175431591755443915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 453818783621061170295943 680728175431591755443915)
              ·
                refine ⟨1021092263147387633165873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 680728175431591755443915 1021092263147387633165873)
                ·
                  refine ⟨765819197360540724874405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021092263147387633165873 765819197360540724874405)
                  ·
                    refine ⟨143591099505101385913951, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 765819197360540724874405 143591099505101385913951)
                    ·
                      rfl

theorem cell22_419464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 2, 1, 1, 2, 4].length) (baseStart_419464 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419464 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419464 prefixEnd_419464 := by exact prefixLift 419464
  have htrace : WordTrace (prefixWord ++ tailWord_419464) baseStart_419464 baseEnd_419464 := by
    simpa [prefixWord, tailWord_419464, baseEnd_419464] using wordTrace_append hprefix tailTrace_419464
  have hstable : (prefixWord ++ tailWord_419464).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419464).length < 2 ^ (prefixWord ++ tailWord_419464).sum := by decide
  have hdescent : baseEnd_419464 < baseStart_419464 := by decide
  rcases family_descends (prefixWord ++ tailWord_419464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419563 : List Nat := [1, 1, 1, 1, 2, 4, 3, 9]
def baseStart_419563 : Nat := 118140960795 + 419563 * 2 ^ 59
def prefixEnd_419563 : Nat := 4983230072969 + 3 ^ 40 * 419563 * 2
def baseEnd_419563 : Nat := 15958332136477569743183

theorem tailTrace_419563 : CollatzResearch.WordTrace tailWord_419563 prefixEnd_419563 15958332136477569743183 := by
  unfold tailWord_419563
  simp only [CollatzResearch.WordTrace]
  refine ⟨15302719779002381500711343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10201813186001587667140895 15302719779002381500711343)
  ·
    refine ⟨22954079668503572251067015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15302719779002381500711343 22954079668503572251067015)
    ·
      refine ⟨34431119502755358376600523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22954079668503572251067015 34431119502755358376600523)
      ·
        refine ⟨51646679254133037564900785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34431119502755358376600523 51646679254133037564900785)
        ·
          refine ⟨38735009440599778173675589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51646679254133037564900785 38735009440599778173675589)
          ·
            refine ⟨7262814270112458407564173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38735009440599778173675589 7262814270112458407564173)
            ·
              refine ⟨2723555351292171902836565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7262814270112458407564173 2723555351292171902836565)
              ·
                refine ⟨15958332136477569743183, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2723555351292171902836565 15958332136477569743183)
                ·
                  rfl

theorem cell22_419563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 3, 9].length) (baseStart_419563 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419563 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419563 prefixEnd_419563 := by exact prefixLift 419563
  have htrace : WordTrace (prefixWord ++ tailWord_419563) baseStart_419563 baseEnd_419563 := by
    simpa [prefixWord, tailWord_419563, baseEnd_419563] using wordTrace_append hprefix tailTrace_419563
  have hstable : (prefixWord ++ tailWord_419563).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419563).length < 2 ^ (prefixWord ++ tailWord_419563).sum := by decide
  have hdescent : baseEnd_419563 < baseStart_419563 := by decide
  rcases family_descends (prefixWord ++ tailWord_419563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419567 : List Nat := [1, 1, 2, 1, 5, 1, 3, 3, 2, 3]
def baseStart_419567 : Nat := 118140960795 + 419567 * 2 ^ 59
def prefixEnd_419567 : Nat := 4983230072969 + 3 ^ 40 * 419567 * 2
def baseEnd_419567 : Nat := 143626358510043450588635

theorem tailTrace_419567 : CollatzResearch.WordTrace tailWord_419567 prefixEnd_419567 143626358510043450588635 := by
  unfold tailWord_419567
  simp only [CollatzResearch.WordTrace]
  refine ⟨15302865670987890183856955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10201910447325260122571303 15302865670987890183856955)
  ·
    refine ⟨22954298506481835275785433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15302865670987890183856955 22954298506481835275785433)
    ·
      refine ⟨17215723879861376456839075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22954298506481835275785433 17215723879861376456839075)
      ·
        refine ⟨25823585819792064685258613, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17215723879861376456839075 25823585819792064685258613)
        ·
          refine ⟨2420961170605506064242995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25823585819792064685258613 2420961170605506064242995)
          ·
            refine ⟨3631441755908259096364493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2420961170605506064242995 3631441755908259096364493)
            ·
              refine ⟨1361790658465597161136685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3631441755908259096364493 1361790658465597161136685)
              ·
                refine ⟨510671496924598935426257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1361790658465597161136685 510671496924598935426257)
                ·
                  refine ⟨383003622693449201569693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 510671496924598935426257 383003622693449201569693)
                  ·
                    refine ⟨143626358510043450588635, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383003622693449201569693 143626358510043450588635)
                    ·
                      rfl

theorem cell22_419567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 3, 3, 2, 3].length) (baseStart_419567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419567 prefixEnd_419567 := by exact prefixLift 419567
  have htrace : WordTrace (prefixWord ++ tailWord_419567) baseStart_419567 baseEnd_419567 := by
    simpa [prefixWord, tailWord_419567, baseEnd_419567] using wordTrace_append hprefix tailTrace_419567
  have hstable : (prefixWord ++ tailWord_419567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419567).length < 2 ^ (prefixWord ++ tailWord_419567).sum := by decide
  have hdescent : baseEnd_419567 < baseStart_419567 := by decide
  rcases family_descends (prefixWord ++ tailWord_419567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419610 : List Nat := [3, 1, 1, 3, 2, 2, 1, 1, 2, 6]
def baseStart_419610 : Nat := 118140960795 + 419610 * 2 ^ 59
def prefixEnd_419610 : Nat := 4983230072969 + 3 ^ 40 * 419610 * 2
def baseEnd_419610 : Nat := 143641078288805671763503

theorem tailTrace_419610 : CollatzResearch.WordTrace tailWord_419610 prefixEnd_419610 143641078288805671763503 := by
  unfold tailWord_419610
  simp only [CollatzResearch.WordTrace]
  refine ⟨3826108502458027131918071, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10202956006554739018448189 3826108502458027131918071)
  ·
    refine ⟨5739162753687040697877107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3826108502458027131918071 5739162753687040697877107)
    ·
      refine ⟨8608744130530561046815661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5739162753687040697877107 8608744130530561046815661)
      ·
        refine ⟨3228279048948960392555873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8608744130530561046815661 3228279048948960392555873)
        ·
          refine ⟨2421209286711720294416905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3228279048948960392555873 2421209286711720294416905)
          ·
            refine ⟨1815906965033790220812679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2421209286711720294416905 1815906965033790220812679)
            ·
              refine ⟨2723860447550685331219019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1815906965033790220812679 2723860447550685331219019)
              ·
                refine ⟨4085790671326027996828529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2723860447550685331219019 4085790671326027996828529)
                ·
                  refine ⟨3064343003494520997621397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4085790671326027996828529 3064343003494520997621397)
                  ·
                    refine ⟨143641078288805671763503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3064343003494520997621397 143641078288805671763503)
                    ·
                      rfl

theorem cell22_419610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 2, 1, 1, 2, 6].length) (baseStart_419610 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419610 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419610 prefixEnd_419610 := by exact prefixLift 419610
  have htrace : WordTrace (prefixWord ++ tailWord_419610) baseStart_419610 baseEnd_419610 := by
    simpa [prefixWord, tailWord_419610, baseEnd_419610] using wordTrace_append hprefix tailTrace_419610
  have hstable : (prefixWord ++ tailWord_419610).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419610).length < 2 ^ (prefixWord ++ tailWord_419610).sum := by decide
  have hdescent : baseEnd_419610 < baseStart_419610 := by decide
  rcases family_descends (prefixWord ++ tailWord_419610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419612 : List Nat := [2, 2, 3, 1, 1, 2, 2, 3, 3, 3]
def baseStart_419612 : Nat := 118140960795 + 419612 * 2 ^ 59
def prefixEnd_419612 : Nat := 4983230072969 + 3 ^ 40 * 419612 * 2
def baseEnd_419612 : Nat := 143641762929678333213497

theorem tailTrace_419612 : CollatzResearch.WordTrace tailWord_419612 prefixEnd_419612 143641762929678333213497 := by
  unfold tailWord_419612
  simp only [CollatzResearch.WordTrace]
  refine ⟨7652253477912431434622545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10203004637216575246163393 7652253477912431434622545)
  ·
    refine ⟨5739190108434323575966909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7652253477912431434622545 5739190108434323575966909)
    ·
      refine ⟨2152196290662871340987591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 5739190108434323575966909 2152196290662871340987591)
      ·
        refine ⟨3228294435994307011481387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2152196290662871340987591 3228294435994307011481387)
        ·
          refine ⟨4842441653991460517222081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3228294435994307011481387 4842441653991460517222081)
          ·
            refine ⟨3631831240493595387916561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4842441653991460517222081 3631831240493595387916561)
            ·
              refine ⟨2723873430370196540937421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3631831240493595387916561 2723873430370196540937421)
              ·
                refine ⟨1021452536388823702851533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2723873430370196540937421 1021452536388823702851533)
                ·
                  refine ⟨383044701145808888569325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021452536388823702851533 383044701145808888569325)
                  ·
                    refine ⟨143641762929678333213497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383044701145808888569325 143641762929678333213497)
                    ·
                      rfl

theorem cell22_419612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 3, 3, 3].length) (baseStart_419612 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419612 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419612 prefixEnd_419612 := by exact prefixLift 419612
  have htrace : WordTrace (prefixWord ++ tailWord_419612) baseStart_419612 baseEnd_419612 := by
    simpa [prefixWord, tailWord_419612, baseEnd_419612] using wordTrace_append hprefix tailTrace_419612
  have hstable : (prefixWord ++ tailWord_419612).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419612).length < 2 ^ (prefixWord ++ tailWord_419612).sum := by decide
  have hdescent : baseEnd_419612 < baseStart_419612 := by decide
  rcases family_descends (prefixWord ++ tailWord_419612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419646 : List Nat := [4, 2, 1, 2, 2, 1, 1, 5, 1, 3]
def baseStart_419646 : Nat := 118140960795 + 419646 * 2 ^ 59
def prefixEnd_419646 : Nat := 4983230072969 + 3 ^ 40 * 419646 * 2
def baseEnd_419646 : Nat := 143653401824513577863393

theorem tailTrace_419646 : CollatzResearch.WordTrace tailWord_419646 prefixEnd_419646 143653401824513577863393 := by
  unfold tailWord_419646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1913218379712710834497849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10203831358467791117321861 1913218379712710834497849)
  ·
    refine ⟨1434913784784533125873387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1913218379712710834497849 1434913784784533125873387)
    ·
      refine ⟨2152370677176799688810081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1434913784784533125873387 2152370677176799688810081)
      ·
        refine ⟨1614278007882599766607561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2152370677176799688810081 1614278007882599766607561)
        ·
          refine ⟨1210708505911949824955671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1614278007882599766607561 1210708505911949824955671)
          ·
            refine ⟨1816062758867924737433507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1210708505911949824955671 1816062758867924737433507)
            ·
              refine ⟨2724094138301887106150261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816062758867924737433507 2724094138301887106150261)
              ·
                refine ⟨255383825465801916201587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2724094138301887106150261 255383825465801916201587)
                ·
                  refine ⟨383075738198702874302381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255383825465801916201587 383075738198702874302381)
                  ·
                    refine ⟨143653401824513577863393, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383075738198702874302381 143653401824513577863393)
                    ·
                      rfl

theorem cell22_419646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 1, 1, 5, 1, 3].length) (baseStart_419646 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419646 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419646 prefixEnd_419646 := by exact prefixLift 419646
  have htrace : WordTrace (prefixWord ++ tailWord_419646) baseStart_419646 baseEnd_419646 := by
    simpa [prefixWord, tailWord_419646, baseEnd_419646] using wordTrace_append hprefix tailTrace_419646
  have hstable : (prefixWord ++ tailWord_419646).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419646).length < 2 ^ (prefixWord ++ tailWord_419646).sum := by decide
  have hdescent : baseEnd_419646 < baseStart_419646 := by decide
  rcases family_descends (prefixWord ++ tailWord_419646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419676 : List Nat := [2, 2, 4, 2, 2, 1, 3, 1, 5]
def baseStart_419676 : Nat := 118140960795 + 419676 * 2 ^ 59
def prefixEnd_419676 : Nat := 4983230072969 + 3 ^ 40 * 419676 * 2
def baseEnd_419676 : Nat := 47887890479201166537767

theorem tailTrace_419676 : CollatzResearch.WordTrace tailWord_419676 prefixEnd_419676 47887890479201166537767 := by
  unfold tailWord_419676
  simp only [CollatzResearch.WordTrace]
  refine ⟨7653420613796500899787441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10204560818395334533049921 7653420613796500899787441)
  ·
    refine ⟨5740065460347375674840581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7653420613796500899787441 5740065460347375674840581)
    ·
      refine ⟨1076262273815132939032609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 5740065460347375674840581 1076262273815132939032609)
      ·
        refine ⟨807196705361349704274457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1076262273815132939032609 807196705361349704274457)
        ·
          refine ⟨605397529021012278205843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 807196705361349704274457 605397529021012278205843)
          ·
            refine ⟨908096293531518417308765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605397529021012278205843 908096293531518417308765)
            ·
              refine ⟨340536110074319406490787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 908096293531518417308765 340536110074319406490787)
              ·
                refine ⟨510804165111479109736181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340536110074319406490787 510804165111479109736181)
                ·
                  refine ⟨47887890479201166537767, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 510804165111479109736181 47887890479201166537767)
                  ·
                    rfl

theorem cell22_419676_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 2, 2, 1, 3, 1, 5].length) (baseStart_419676 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419676 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419676 prefixEnd_419676 := by exact prefixLift 419676
  have htrace : WordTrace (prefixWord ++ tailWord_419676) baseStart_419676 baseEnd_419676 := by
    simpa [prefixWord, tailWord_419676, baseEnd_419676] using wordTrace_append hprefix tailTrace_419676
  have hstable : (prefixWord ++ tailWord_419676).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419676).length < 2 ^ (prefixWord ++ tailWord_419676).sum := by decide
  have hdescent : baseEnd_419676 < baseStart_419676 := by decide
  rcases family_descends (prefixWord ++ tailWord_419676) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419715 : List Nat := [1, 1, 1, 3, 4, 2, 10]
def baseStart_419715 : Nat := 118140960795 + 419715 * 2 ^ 59
def prefixEnd_419715 : Nat := 4983230072969 + 3 ^ 40 * 419715 * 2
def baseEnd_419715 : Nat := 5321371182763718440303

theorem tailTrace_419715 : CollatzResearch.WordTrace tailWord_419715 prefixEnd_419715 5321371182763718440303 := by
  unfold tailWord_419715
  simp only [CollatzResearch.WordTrace]
  refine ⟨15308263674451711460244599, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10205509116301140973496399 15308263674451711460244599)
  ·
    refine ⟨22962395511677567190366899, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15308263674451711460244599 22962395511677567190366899)
    ·
      refine ⟨34443593267516350785550349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22962395511677567190366899 34443593267516350785550349)
      ·
        refine ⟨12916347475318631544581381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34443593267516350785550349 12916347475318631544581381)
        ·
          refine ⟨2421815151622243414609009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12916347475318631544581381 2421815151622243414609009)
          ·
            refine ⟨1816361363716682560956757, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2421815151622243414609009 1816361363716682560956757)
            ·
              refine ⟨5321371182763718440303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 1816361363716682560956757 5321371182763718440303)
              ·
                rfl

theorem cell22_419715_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 2, 10].length) (baseStart_419715 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419715 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419715 prefixEnd_419715 := by exact prefixLift 419715
  have htrace : WordTrace (prefixWord ++ tailWord_419715) baseStart_419715 baseEnd_419715 := by
    simpa [prefixWord, tailWord_419715, baseEnd_419715] using wordTrace_append hprefix tailTrace_419715
  have hstable : (prefixWord ++ tailWord_419715).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419715).length < 2 ^ (prefixWord ++ tailWord_419715).sum := by decide
  have hdescent : baseEnd_419715 < baseStart_419715 := by decide
  rcases family_descends (prefixWord ++ tailWord_419715) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419717 : List Nat := [1, 3, 1, 1, 3, 2, 3, 2, 2, 4]
def baseStart_419717 : Nat := 118140960795 + 419717 * 2 ^ 59
def prefixEnd_419717 : Nat := 4983230072969 + 3 ^ 40 * 419717 * 2
def baseEnd_419717 : Nat := 143677706575493059338175

theorem tailTrace_419717 : CollatzResearch.WordTrace tailWord_419717 prefixEnd_419717 143677706575493059338175 := by
  unfold tailWord_419717
  simp only [CollatzResearch.WordTrace]
  refine ⟨15308336620444465801817405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10205557746962977201211603 15308336620444465801817405)
  ·
    refine ⟨5740626232666674675681527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15308336620444465801817405 5740626232666674675681527)
    ·
      refine ⟨8610939349000012013522291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5740626232666674675681527 8610939349000012013522291)
      ·
        refine ⟨12916409023500018020283437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8610939349000012013522291 12916409023500018020283437)
        ·
          refine ⟨4843653383812506757606289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12916409023500018020283437 4843653383812506757606289)
          ·
            refine ⟨3632740037859380068204717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4843653383812506757606289 3632740037859380068204717)
            ·
              refine ⟨1362277514197267525576769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3632740037859380068204717 1362277514197267525576769)
              ·
                refine ⟨1021708135647950644182577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362277514197267525576769 1021708135647950644182577)
                ·
                  refine ⟨766281101735962983136933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1021708135647950644182577 766281101735962983136933)
                  ·
                    refine ⟨143677706575493059338175, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 766281101735962983136933 143677706575493059338175)
                    ·
                      rfl

theorem cell22_419717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 2, 3, 2, 2, 4].length) (baseStart_419717 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419717 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419717 prefixEnd_419717 := by exact prefixLift 419717
  have htrace : WordTrace (prefixWord ++ tailWord_419717) baseStart_419717 baseEnd_419717 := by
    simpa [prefixWord, tailWord_419717, baseEnd_419717] using wordTrace_append hprefix tailTrace_419717
  have hstable : (prefixWord ++ tailWord_419717).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419717).length < 2 ^ (prefixWord ++ tailWord_419717).sum := by decide
  have hdescent : baseEnd_419717 < baseStart_419717 := by decide
  rcases family_descends (prefixWord ++ tailWord_419717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419732 : List Nat := [2, 4, 2, 1, 1, 2, 1, 9]
def baseStart_419732 : Nat := 118140960795 + 419732 * 2 ^ 59
def prefixEnd_419732 : Nat := 4983230072969 + 3 ^ 40 * 419732 * 2
def baseEnd_419732 : Nat := 15964760153559780023681

theorem tailTrace_419732 : CollatzResearch.WordTrace tailWord_419732 prefixEnd_419732 15964760153559780023681 := by
  unfold tailWord_419732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7654441857695061681806725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10205922476926748909075633 7654441857695061681806725)
  ·
    refine ⟨1435207848317824065338761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 7654441857695061681806725 1435207848317824065338761)
    ·
      refine ⟨1076405886238368049004071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1435207848317824065338761 1076405886238368049004071)
      ·
        refine ⟨1614608829357552073506107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076405886238368049004071 1614608829357552073506107)
        ·
          refine ⟨2421913244036328110259161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1614608829357552073506107 2421913244036328110259161)
          ·
            refine ⟨1816434933027246082694371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2421913244036328110259161 1816434933027246082694371)
            ·
              refine ⟨2724652399540869124041557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1816434933027246082694371 2724652399540869124041557)
              ·
                refine ⟨15964760153559780023681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 2724652399540869124041557 15964760153559780023681)
                ·
                  rfl

theorem cell22_419732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 1, 9].length) (baseStart_419732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419732 prefixEnd_419732 := by exact prefixLift 419732
  have htrace : WordTrace (prefixWord ++ tailWord_419732) baseStart_419732 baseEnd_419732 := by
    simpa [prefixWord, tailWord_419732, baseEnd_419732] using wordTrace_append hprefix tailTrace_419732
  have hstable : (prefixWord ++ tailWord_419732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419732).length < 2 ^ (prefixWord ++ tailWord_419732).sum := by decide
  have hdescent : baseEnd_419732 < baseStart_419732 := by decide
  rcases family_descends (prefixWord ++ tailWord_419732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419747 : List Nat := [1, 1, 1, 4, 1, 2, 1, 3, 5, 3]
def baseStart_419747 : Nat := 118140960795 + 419747 * 2 ^ 59
def prefixEnd_419747 : Nat := 4983230072969 + 3 ^ 40 * 419747 * 2
def baseEnd_419747 : Nat := 143687976188582981088083

theorem tailTrace_419747 : CollatzResearch.WordTrace tailWord_419747 prefixEnd_419747 143687976188582981088083 := by
  unfold tailWord_419747
  simp only [CollatzResearch.WordTrace]
  refine ⟨15309430810335780925409495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10206287206890520616939663 15309430810335780925409495)
  ·
    refine ⟨22964146215503671388114243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15309430810335780925409495 22964146215503671388114243)
    ·
      refine ⟨34446219323255507082171365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22964146215503671388114243 34446219323255507082171365)
      ·
        refine ⟨6458666123110407577907131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34446219323255507082171365 6458666123110407577907131)
        ·
          refine ⟨9687999184665611366860697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6458666123110407577907131 9687999184665611366860697)
          ·
            refine ⟨7265999388499208525145523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9687999184665611366860697 7265999388499208525145523)
            ·
              refine ⟨10898999082748812787718285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7265999388499208525145523 10898999082748812787718285)
              ·
                refine ⟨4087124656030804795394357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10898999082748812787718285 4087124656030804795394357)
                ·
                  refine ⟨383167936502887949568221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4087124656030804795394357 383167936502887949568221)
                  ·
                    refine ⟨143687976188582981088083, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383167936502887949568221 143687976188582981088083)
                    ·
                      rfl

theorem cell22_419747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 1, 3, 5, 3].length) (baseStart_419747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419747 prefixEnd_419747 := by exact prefixLift 419747
  have htrace : WordTrace (prefixWord ++ tailWord_419747) baseStart_419747 baseEnd_419747 := by
    simpa [prefixWord, tailWord_419747, baseEnd_419747] using wordTrace_append hprefix tailTrace_419747
  have hstable : (prefixWord ++ tailWord_419747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419747).length < 2 ^ (prefixWord ++ tailWord_419747).sum := by decide
  have hdescent : baseEnd_419747 < baseStart_419747 := by decide
  rcases family_descends (prefixWord ++ tailWord_419747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419798 : List Nat := [5, 2, 1, 1, 3, 1, 1, 2, 3, 3]
def baseStart_419798 : Nat := 118140960795 + 419798 * 2 ^ 59
def prefixEnd_419798 : Nat := 4983230072969 + 3 ^ 40 * 419798 * 2
def baseEnd_419798 : Nat := 143705434530835848062927

theorem tailTrace_419798 : CollatzResearch.WordTrace tailWord_419798 prefixEnd_419798 143705434530835848062927 := by
  unfold tailWord_419798
  simp only [CollatzResearch.WordTrace]
  refine ⟨956955683321938539719753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 10207527288767344423677365 956955683321938539719753)
  ·
    refine ⟨717716762491453904789815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 956955683321938539719753 717716762491453904789815)
    ·
      refine ⟨1076575143737180857184723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 717716762491453904789815 1076575143737180857184723)
      ·
        refine ⟨1614862715605771285777085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076575143737180857184723 1614862715605771285777085)
        ·
          refine ⟨605573518352164232166407, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1614862715605771285777085 605573518352164232166407)
          ·
            refine ⟨908360277528246348249611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 605573518352164232166407 908360277528246348249611)
            ·
              refine ⟨1362540416292369522374417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908360277528246348249611 1362540416292369522374417)
              ·
                refine ⟨1021905312219277141780813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362540416292369522374417 1021905312219277141780813)
                ·
                  refine ⟨383214492082228928167805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1021905312219277141780813 383214492082228928167805)
                  ·
                    refine ⟨143705434530835848062927, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383214492082228928167805 143705434530835848062927)
                    ·
                      rfl

theorem cell22_419798_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_419798 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419798 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419798 prefixEnd_419798 := by exact prefixLift 419798
  have htrace : WordTrace (prefixWord ++ tailWord_419798) baseStart_419798 baseEnd_419798 := by
    simpa [prefixWord, tailWord_419798, baseEnd_419798] using wordTrace_append hprefix tailTrace_419798
  have hstable : (prefixWord ++ tailWord_419798).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419798).length < 2 ^ (prefixWord ++ tailWord_419798).sum := by decide
  have hdescent : baseEnd_419798 < baseStart_419798 := by decide
  rcases family_descends (prefixWord ++ tailWord_419798) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419837 : List Nat := [1, 4, 1, 1, 1, 2, 2, 2, 3, 5]
def baseStart_419837 : Nat := 118140960795 + 419837 * 2 ^ 59
def prefixEnd_419837 : Nat := 4983230072969 + 3 ^ 40 * 419837 * 2
def baseEnd_419837 : Nat := 143718785027852746337807

theorem tailTrace_419837 : CollatzResearch.WordTrace tailWord_419837 prefixEnd_419837 143718785027852746337807 := by
  unfold tailWord_419837
  simp only [CollatzResearch.WordTrace]
  refine ⟨15312713380009726296185765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10208475586673150864123843 15312713380009726296185765)
  ·
    refine ⟨2871133758751823680534831, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15312713380009726296185765 2871133758751823680534831)
    ·
      refine ⟨4306700638127735520802247, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2871133758751823680534831 4306700638127735520802247)
      ·
        refine ⟨6460050957191603281203371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4306700638127735520802247 6460050957191603281203371)
        ·
          refine ⟨9690076435787404921805057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6460050957191603281203371 9690076435787404921805057)
          ·
            refine ⟨7267557326840553691353793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9690076435787404921805057 7267557326840553691353793)
            ·
              refine ⟨5450667995130415268515345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7267557326840553691353793 5450667995130415268515345)
              ·
                refine ⟨4088000996347811451386509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5450667995130415268515345 4088000996347811451386509)
                ·
                  refine ⟨1533000373630429294269941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 4088000996347811451386509 1533000373630429294269941)
                  ·
                    refine ⟨143718785027852746337807, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1533000373630429294269941 143718785027852746337807)
                    ·
                      rfl

theorem cell22_419837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_419837 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419837 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419837 prefixEnd_419837 := by exact prefixLift 419837
  have htrace : WordTrace (prefixWord ++ tailWord_419837) baseStart_419837 baseEnd_419837 := by
    simpa [prefixWord, tailWord_419837, baseEnd_419837] using wordTrace_append hprefix tailTrace_419837
  have hstable : (prefixWord ++ tailWord_419837).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419837).length < 2 ^ (prefixWord ++ tailWord_419837).sum := by decide
  have hdescent : baseEnd_419837 < baseStart_419837 := by decide
  rcases family_descends (prefixWord ++ tailWord_419837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419852 : List Nat := [2, 2, 1, 2, 3, 1, 1, 1, 3, 6]
def baseStart_419852 : Nat := 118140960795 + 419852 * 2 ^ 59
def prefixEnd_419852 : Nat := 4983230072969 + 3 ^ 40 * 419852 * 2
def baseEnd_419852 : Nat := 143723919834397707212761

theorem tailTrace_419852 : CollatzResearch.WordTrace tailWord_419852 prefixEnd_419852 143723919834397707212761 := by
  unfold tailWord_419852
  simp only [CollatzResearch.WordTrace]
  refine ⟨7656630237477691928990905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10208840316636922571987873 7656630237477691928990905)
  ·
    refine ⟨5742472678108268946743179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7656630237477691928990905 5742472678108268946743179)
    ·
      refine ⟨8613709017162403420114769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5742472678108268946743179 8613709017162403420114769)
      ·
        refine ⟨6460281762871802565086077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8613709017162403420114769 6460281762871802565086077)
        ·
          refine ⟨2422605661076925961907279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6460281762871802565086077 2422605661076925961907279)
          ·
            refine ⟨3633908491615388942860919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2422605661076925961907279 3633908491615388942860919)
            ·
              refine ⟨5450862737423083414291379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3633908491615388942860919 5450862737423083414291379)
              ·
                refine ⟨8176294106134625121437069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5450862737423083414291379 8176294106134625121437069)
                ·
                  refine ⟨3066110289800484420538901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8176294106134625121437069 3066110289800484420538901)
                  ·
                    refine ⟨143723919834397707212761, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3066110289800484420538901 143723919834397707212761)
                    ·
                      rfl

theorem cell22_419852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 1, 1, 1, 3, 6].length) (baseStart_419852 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419852 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419852 prefixEnd_419852 := by exact prefixLift 419852
  have htrace : WordTrace (prefixWord ++ tailWord_419852) baseStart_419852 baseEnd_419852 := by
    simpa [prefixWord, tailWord_419852, baseEnd_419852] using wordTrace_append hprefix tailTrace_419852
  have hstable : (prefixWord ++ tailWord_419852).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419852).length < 2 ^ (prefixWord ++ tailWord_419852).sum := by decide
  have hdescent : baseEnd_419852 < baseStart_419852 := by decide
  rcases family_descends (prefixWord ++ tailWord_419852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419869 : List Nat := [1, 4, 2, 2, 2, 1, 2, 1, 1, 6]
def baseStart_419869 : Nat := 118140960795 + 419869 * 2 ^ 59
def prefixEnd_419869 : Nat := 4983230072969 + 3 ^ 40 * 419869 * 2
def baseEnd_419869 : Nat := 143729739281815329537709

theorem tailTrace_419869 : CollatzResearch.WordTrace tailWord_419869 prefixEnd_419869 143729739281815329537709 := by
  unfold tailWord_419869
  simp only [CollatzResearch.WordTrace]
  refine ⟨15313880515893795761350661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10209253677262530507567107 15313880515893795761350661)
  ·
    refine ⟨2871352596730086705253249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 15313880515893795761350661 2871352596730086705253249)
    ·
      refine ⟨2153514447547565028939937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2871352596730086705253249 2153514447547565028939937)
      ·
        refine ⟨1615135835660673771704953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2153514447547565028939937 1615135835660673771704953)
        ·
          refine ⟨1211351876745505328778715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615135835660673771704953 1211351876745505328778715)
          ·
            refine ⟨1817027815118257993168073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211351876745505328778715 1817027815118257993168073)
            ·
              refine ⟨1362770861338693494876055, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817027815118257993168073 1362770861338693494876055)
              ·
                refine ⟨2044156292008040242314083, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1362770861338693494876055 2044156292008040242314083)
                ·
                  refine ⟨3066234438012060363471125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2044156292008040242314083 3066234438012060363471125)
                  ·
                    refine ⟨143729739281815329537709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3066234438012060363471125 143729739281815329537709)
                    ·
                      rfl

theorem cell22_419869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 2, 1, 2, 1, 1, 6].length) (baseStart_419869 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419869 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419869 prefixEnd_419869 := by exact prefixLift 419869
  have htrace : WordTrace (prefixWord ++ tailWord_419869) baseStart_419869 baseEnd_419869 := by
    simpa [prefixWord, tailWord_419869, baseEnd_419869] using wordTrace_append hprefix tailTrace_419869
  have hstable : (prefixWord ++ tailWord_419869).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419869).length < 2 ^ (prefixWord ++ tailWord_419869).sum := by decide
  have hdescent : baseEnd_419869 < baseStart_419869 := by decide
  rcases family_descends (prefixWord ++ tailWord_419869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419873 : List Nat := [1, 2, 3, 2, 4, 2, 1, 3, 4]
def baseStart_419873 : Nat := 118140960795 + 419873 * 2 ^ 59
def prefixEnd_419873 : Nat := 4983230072969 + 3 ^ 40 * 419873 * 2
def baseEnd_419873 : Nat := 47910369521186884145899

theorem tailTrace_419873 : CollatzResearch.WordTrace tailWord_419873 prefixEnd_419873 47910369521186884145899 := by
  unfold tailWord_419873
  simp only [CollatzResearch.WordTrace]
  refine ⟨15314026407879304444496273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10209350938586202962997515 15314026407879304444496273)
  ·
    refine ⟨11485519805909478333372205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15314026407879304444496273 11485519805909478333372205)
    ·
      refine ⟨4307069927216054375014577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11485519805909478333372205 4307069927216054375014577)
      ·
        refine ⟨3230302445412040781260933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4307069927216054375014577 3230302445412040781260933)
        ·
          refine ⟨605681708514757646486425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 3230302445412040781260933 605681708514757646486425)
          ·
            refine ⟨454261281386068234864819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 605681708514757646486425 454261281386068234864819)
            ·
              refine ⟨681391922079102352297229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 454261281386068234864819 681391922079102352297229)
              ·
                refine ⟨255521970779663382111461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 681391922079102352297229 255521970779663382111461)
                ·
                  refine ⟨47910369521186884145899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255521970779663382111461 47910369521186884145899)
                  ·
                    rfl

theorem cell22_419873_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 2, 1, 3, 4].length) (baseStart_419873 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419873 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419873 prefixEnd_419873 := by exact prefixLift 419873
  have htrace : WordTrace (prefixWord ++ tailWord_419873) baseStart_419873 baseEnd_419873 := by
    simpa [prefixWord, tailWord_419873, baseEnd_419873] using wordTrace_append hprefix tailTrace_419873
  have hstable : (prefixWord ++ tailWord_419873).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419873).length < 2 ^ (prefixWord ++ tailWord_419873).sum := by decide
  have hdescent : baseEnd_419873 < baseStart_419873 := by decide
  rcases family_descends (prefixWord ++ tailWord_419873) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419886 : List Nat := [4, 1, 3, 1, 1, 3, 1, 2, 2, 4]
def baseStart_419886 : Nat := 118140960795 + 419886 * 2 ^ 59
def prefixEnd_419886 : Nat := 4983230072969 + 3 ^ 40 * 419886 * 2
def baseEnd_419886 : Nat := 143735558729232951862657

theorem tailTrace_419886 : CollatzResearch.WordTrace tailWord_419886 prefixEnd_419886 143735558729232951862657 := by
  unfold tailWord_419886
  simp only [CollatzResearch.WordTrace]
  refine ⟨1914312569604025958089939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10209667037888138443146341 1914312569604025958089939)
  ·
    refine ⟨2871468854406038937134909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1914312569604025958089939 2871468854406038937134909)
    ·
      refine ⟨1076800820402264601425591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2871468854406038937134909 1076800820402264601425591)
      ·
        refine ⟨1615201230603396902138387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076800820402264601425591 1615201230603396902138387)
        ·
          refine ⟨2422801845905095353207581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1615201230603396902138387 2422801845905095353207581)
          ·
            refine ⟨908550692214410757452843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2422801845905095353207581 908550692214410757452843)
            ·
              refine ⟨1362826038321616136179265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908550692214410757452843 1362826038321616136179265)
              ·
                refine ⟨1022119528741212102134449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1362826038321616136179265 1022119528741212102134449)
                ·
                  refine ⟨766589646555909076600837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1022119528741212102134449 766589646555909076600837)
                  ·
                    refine ⟨143735558729232951862657, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 766589646555909076600837 143735558729232951862657)
                    ·
                      rfl

theorem cell22_419886_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 1, 3, 1, 2, 2, 4].length) (baseStart_419886 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419886 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419886 prefixEnd_419886 := by exact prefixLift 419886
  have htrace : WordTrace (prefixWord ++ tailWord_419886) baseStart_419886 baseEnd_419886 := by
    simpa [prefixWord, tailWord_419886, baseEnd_419886] using wordTrace_append hprefix tailTrace_419886
  have hstable : (prefixWord ++ tailWord_419886).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419886).length < 2 ^ (prefixWord ++ tailWord_419886).sum := by decide
  have hdescent : baseEnd_419886 < baseStart_419886 := by decide
  rcases family_descends (prefixWord ++ tailWord_419886) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419905 : List Nat := [1, 2, 5, 1, 2, 3, 2, 1, 2, 3]
def baseStart_419905 : Nat := 118140960795 + 419905 * 2 ^ 59
def prefixEnd_419905 : Nat := 4983230072969 + 3 ^ 40 * 419905 * 2
def baseEnd_419905 : Nat := 143742062817523235637599

theorem tailTrace_419905 : CollatzResearch.WordTrace tailWord_419905 prefixEnd_419905 143742062817523235637599 := by
  unfold tailWord_419905
  simp only [CollatzResearch.WordTrace]
  refine ⟨15315193543763373909661169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10210129029175582606440779 15315193543763373909661169)
  ·
    refine ⟨11486395157822530432245877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15315193543763373909661169 11486395157822530432245877)
    ·
      refine ⟨1076849546045862228023051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 11486395157822530432245877 1076849546045862228023051)
      ·
        refine ⟨1615274319068793342034577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1076849546045862228023051 1615274319068793342034577)
        ·
          refine ⟨1211455739301595006525933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615274319068793342034577 1211455739301595006525933)
          ·
            refine ⟨454295902238098127447225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1211455739301595006525933 454295902238098127447225)
            ·
              refine ⟨340721926678573595585419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 454295902238098127447225 340721926678573595585419)
              ·
                refine ⟨511082890017860393378129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340721926678573595585419 511082890017860393378129)
                ·
                  refine ⟨383312167513395295033597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511082890017860393378129 383312167513395295033597)
                  ·
                    refine ⟨143742062817523235637599, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383312167513395295033597 143742062817523235637599)
                    ·
                      rfl

theorem cell22_419905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 3, 2, 1, 2, 3].length) (baseStart_419905 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419905 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419905 prefixEnd_419905 := by exact prefixLift 419905
  have htrace : WordTrace (prefixWord ++ tailWord_419905) baseStart_419905 baseEnd_419905 := by
    simpa [prefixWord, tailWord_419905, baseEnd_419905] using wordTrace_append hprefix tailTrace_419905
  have hstable : (prefixWord ++ tailWord_419905).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419905).length < 2 ^ (prefixWord ++ tailWord_419905).sum := by decide
  have hdescent : baseEnd_419905 < baseStart_419905 := by decide
  rcases family_descends (prefixWord ++ tailWord_419905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419912 : List Nat := [2, 1, 3, 1, 1, 1, 2, 2, 9]
def baseStart_419912 : Nat := 118140960795 + 419912 * 2 ^ 59
def prefixEnd_419912 : Nat := 4983230072969 + 3 ^ 40 * 419912 * 2
def baseEnd_419912 : Nat := 47914819686859183570859

theorem tailTrace_419912 : CollatzResearch.WordTrace tailWord_419912 prefixEnd_419912 47914819686859183570859 := by
  unfold tailWord_419912
  simp only [CollatzResearch.WordTrace]
  refine ⟨7657724427369007052582995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10210299236492009403443993 7657724427369007052582995)
  ·
    refine ⟨11486586641053510578874493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7657724427369007052582995 11486586641053510578874493)
    ·
      refine ⟨4307469990395066467077935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11486586641053510578874493 4307469990395066467077935)
      ·
        refine ⟨6461204985592599700616903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4307469990395066467077935 6461204985592599700616903)
        ·
          refine ⟨9691807478388899550925355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6461204985592599700616903 9691807478388899550925355)
          ·
            refine ⟨14537711217583349326388033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9691807478388899550925355 14537711217583349326388033)
            ·
              refine ⟨10903283413187511994791025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14537711217583349326388033 10903283413187511994791025)
              ·
                refine ⟨8177462559890633996093269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10903283413187511994791025 8177462559890633996093269)
                ·
                  refine ⟨47914819686859183570859, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 8177462559890633996093269 47914819686859183570859)
                  ·
                    rfl

theorem cell22_419912_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 2, 2, 9].length) (baseStart_419912 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419912 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419912 prefixEnd_419912 := by exact prefixLift 419912
  have htrace : WordTrace (prefixWord ++ tailWord_419912) baseStart_419912 baseEnd_419912 := by
    simpa [prefixWord, tailWord_419912, baseEnd_419912] using wordTrace_append hprefix tailTrace_419912
  have hstable : (prefixWord ++ tailWord_419912).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419912).length < 2 ^ (prefixWord ++ tailWord_419912).sum := by decide
  have hdescent : baseEnd_419912 < baseStart_419912 := by decide
  rcases family_descends (prefixWord ++ tailWord_419912) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419959 : List Nat := [1, 1, 3, 1, 1, 5, 1, 2, 3, 4]
def baseStart_419959 : Nat := 118140960795 + 419959 * 2 ^ 59
def prefixEnd_419959 : Nat := 4983230072969 + 3 ^ 40 * 419959 * 2
def baseEnd_419959 : Nat := 143760548121085094787433

theorem tailTrace_419959 : CollatzResearch.WordTrace tailWord_419959 prefixEnd_419959 143760548121085094787433 := by
  unfold tailWord_419959
  simp only [CollatzResearch.WordTrace]
  refine ⟨15317163085567741132126931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10211442057045160754751287 15317163085567741132126931)
  ·
    refine ⟨22975744628351611698190397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15317163085567741132126931 22975744628351611698190397)
    ·
      refine ⟨8615904235631854386821399, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22975744628351611698190397 8615904235631854386821399)
      ·
        refine ⟨12923856353447781580232099, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8615904235631854386821399 12923856353447781580232099)
        ·
          refine ⟨19385784530171672370348149, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12923856353447781580232099 19385784530171672370348149)
          ·
            refine ⟨1817417299703594284720139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 19385784530171672370348149 1817417299703594284720139)
            ·
              refine ⟨2726125949555391427080209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1817417299703594284720139 2726125949555391427080209)
              ·
                refine ⟨2044594462166543570310157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2726125949555391427080209 2044594462166543570310157)
                ·
                  refine ⟨766722923312453838866309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2044594462166543570310157 766722923312453838866309)
                  ·
                    refine ⟨143760548121085094787433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 766722923312453838866309 143760548121085094787433)
                    ·
                      rfl

theorem cell22_419959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 5, 1, 2, 3, 4].length) (baseStart_419959 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419959 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419959 prefixEnd_419959 := by exact prefixLift 419959
  have htrace : WordTrace (prefixWord ++ tailWord_419959) baseStart_419959 baseEnd_419959 := by
    simpa [prefixWord, tailWord_419959, baseEnd_419959] using wordTrace_append hprefix tailTrace_419959
  have hstable : (prefixWord ++ tailWord_419959).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419959).length < 2 ^ (prefixWord ++ tailWord_419959).sum := by decide
  have hdescent : baseEnd_419959 < baseStart_419959 := by decide
  rcases family_descends (prefixWord ++ tailWord_419959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419976 : List Nat := [2, 1, 3, 4, 1, 1, 2, 1, 3, 4]
def baseStart_419976 : Nat := 118140960795 + 419976 * 2 ^ 59
def prefixEnd_419976 : Nat := 4983230072969 + 3 ^ 40 * 419976 * 2
def baseEnd_419976 : Nat := 143766367568502717112381

theorem tailTrace_419976 : CollatzResearch.WordTrace tailWord_419976 prefixEnd_419976 143766367568502717112381 := by
  unfold tailWord_419976
  simp only [CollatzResearch.WordTrace]
  refine ⟨7658891563253076517747891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10211855417670768690330521 7658891563253076517747891)
  ·
    refine ⟨11488337344879614776621837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7658891563253076517747891 11488337344879614776621837)
    ·
      refine ⟨4308126504329855541233189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11488337344879614776621837 4308126504329855541233189)
      ·
        refine ⟨807773719561847913981223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4308126504329855541233189 807773719561847913981223)
        ·
          refine ⟨1211660579342771870971835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 807773719561847913981223 1211660579342771870971835)
          ·
            refine ⟨1817490869014157806457753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1211660579342771870971835 1817490869014157806457753)
            ·
              refine ⟨1363118151760618354843315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1817490869014157806457753 1363118151760618354843315)
              ·
                refine ⟨2044677227640927532264973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363118151760618354843315 2044677227640927532264973)
                ·
                  refine ⟨766753960365347824599365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 2044677227640927532264973 766753960365347824599365)
                  ·
                    refine ⟨143766367568502717112381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 766753960365347824599365 143766367568502717112381)
                    ·
                      rfl

theorem cell22_419976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 1, 2, 1, 3, 4].length) (baseStart_419976 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419976 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419976 prefixEnd_419976 := by exact prefixLift 419976
  have htrace : WordTrace (prefixWord ++ tailWord_419976) baseStart_419976 baseEnd_419976 := by
    simpa [prefixWord, tailWord_419976, baseEnd_419976] using wordTrace_append hprefix tailTrace_419976
  have hstable : (prefixWord ++ tailWord_419976).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419976).length < 2 ^ (prefixWord ++ tailWord_419976).sum := by decide
  have hdescent : baseEnd_419976 < baseStart_419976 := by decide
  rcases family_descends (prefixWord ++ tailWord_419976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_419989 : List Nat := [1, 3, 2, 1, 1, 1, 3, 4, 1, 5]
def baseStart_419989 : Nat := 118140960795 + 419989 * 2 ^ 59
def prefixEnd_419989 : Nat := 4983230072969 + 3 ^ 40 * 419989 * 2
def baseEnd_419989 : Nat := 143770817734175016537341

theorem tailTrace_419989 : CollatzResearch.WordTrace tailWord_419989 prefixEnd_419989 143770817734175016537341 := by
  unfold tailWord_419989
  simp only [CollatzResearch.WordTrace]
  refine ⟨15318257275459056255719021, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10212171516972704170479347 15318257275459056255719021)
  ·
    refine ⟨5744346478297146095894633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15318257275459056255719021 5744346478297146095894633)
    ·
      refine ⟨4308259858722859571920975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5744346478297146095894633 4308259858722859571920975)
      ·
        refine ⟨6462389788084289357881463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4308259858722859571920975 6462389788084289357881463)
        ·
          refine ⟨9693584682126434036822195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6462389788084289357881463 9693584682126434036822195)
          ·
            refine ⟨14540377023189651055233293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9693584682126434036822195 14540377023189651055233293)
            ·
              refine ⟨5452641383696119145712485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14540377023189651055233293 5452641383696119145712485)
              ·
                refine ⟨1022370259443022339821091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 5452641383696119145712485 1022370259443022339821091)
                ·
                  refine ⟨1533555389164533509731637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022370259443022339821091 1533555389164533509731637)
                  ·
                    refine ⟨143770817734175016537341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1533555389164533509731637 143770817734175016537341)
                    ·
                      rfl

theorem cell22_419989_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 3, 4, 1, 5].length) (baseStart_419989 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_419989 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_419989 prefixEnd_419989 := by exact prefixLift 419989
  have htrace : WordTrace (prefixWord ++ tailWord_419989) baseStart_419989 baseEnd_419989 := by
    simpa [prefixWord, tailWord_419989, baseEnd_419989] using wordTrace_append hprefix tailTrace_419989
  have hstable : (prefixWord ++ tailWord_419989).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_419989).length < 2 ^ (prefixWord ++ tailWord_419989).sum := by decide
  have hdescent : baseEnd_419989 < baseStart_419989 := by decide
  rcases family_descends (prefixWord ++ tailWord_419989) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420036 : List Nat := [2, 3, 3, 1, 2, 2, 1, 8]
def baseStart_420036 : Nat := 118140960795 + 420036 * 2 ^ 59
def prefixEnd_420036 : Nat := 4983230072969 + 3 ^ 40 * 420036 * 2
def baseEnd_420036 : Nat := 15976322977186951179133

theorem tailTrace_420036 : CollatzResearch.WordTrace tailWord_420036 prefixEnd_420036 15976322977186951179133 := by
  unfold tailWord_420036
  simp only [CollatzResearch.WordTrace]
  refine ⟨7659985753144391641339981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10213314337525855521786641 7659985753144391641339981)
  ·
    refine ⟨2872494657429146865502493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7659985753144391641339981 2872494657429146865502493)
    ·
      refine ⟨1077185496535930074563435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2872494657429146865502493 1077185496535930074563435)
      ·
        refine ⟨1615778244803895111845153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1077185496535930074563435 1615778244803895111845153)
        ·
          refine ⟨1211833683602921333883865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1615778244803895111845153 1211833683602921333883865)
          ·
            refine ⟨908875262702191000412899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1211833683602921333883865 908875262702191000412899)
            ·
              refine ⟨1363312894053286500619349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 908875262702191000412899 1363312894053286500619349)
              ·
                refine ⟨15976322977186951179133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 1363312894053286500619349 15976322977186951179133)
                ·
                  rfl

theorem cell22_420036_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 2, 2, 1, 8].length) (baseStart_420036 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420036 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420036 prefixEnd_420036 := by exact prefixLift 420036
  have htrace : WordTrace (prefixWord ++ tailWord_420036) baseStart_420036 baseEnd_420036 := by
    simpa [prefixWord, tailWord_420036, baseEnd_420036] using wordTrace_append hprefix tailTrace_420036
  have hstable : (prefixWord ++ tailWord_420036).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420036).length < 2 ^ (prefixWord ++ tailWord_420036).sum := by decide
  have hdescent : baseEnd_420036 < baseStart_420036 := by decide
  rcases family_descends (prefixWord ++ tailWord_420036) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420053 : List Nat := [1, 3, 2, 4, 3, 1, 8]
def baseStart_420053 : Nat := 118140960795 + 420053 * 2 ^ 59
def prefixEnd_420053 : Nat := 4983230072969 + 3 ^ 40 * 420053 * 2
def baseEnd_420053 : Nat := 5325656527485191960635

theorem tailTrace_420053 : CollatzResearch.WordTrace tailWord_420053 prefixEnd_420053 5325656527485191960635 := by
  unfold tailWord_420053
  simp only [CollatzResearch.WordTrace]
  refine ⟨15320591547227195186048813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10213727698151463457365875 15320591547227195186048813)
  ·
    refine ⟨5745221830210198194768305, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15320591547227195186048813 5745221830210198194768305)
    ·
      refine ⟨4308916372657648646076229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5745221830210198194768305 4308916372657648646076229)
      ·
        refine ⟨807921819873309121139293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 4308916372657648646076229 807921819873309121139293)
        ·
          refine ⟨302970682452490920427235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 807921819873309121139293 302970682452490920427235)
          ·
            refine ⟨454456023678736380640853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 302970682452490920427235 454456023678736380640853)
            ·
              refine ⟨5325656527485191960635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 454456023678736380640853 5325656527485191960635)
              ·
                rfl

theorem cell22_420053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 3, 1, 8].length) (baseStart_420053 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420053 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420053 prefixEnd_420053 := by exact prefixLift 420053
  have htrace : WordTrace (prefixWord ++ tailWord_420053) baseStart_420053 baseEnd_420053 := by
    simpa [prefixWord, tailWord_420053, baseEnd_420053] using wordTrace_append hprefix tailTrace_420053
  have hstable : (prefixWord ++ tailWord_420053).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420053).length < 2 ^ (prefixWord ++ tailWord_420053).sum := by decide
  have hdescent : baseEnd_420053 < baseStart_420053 := by decide
  rcases family_descends (prefixWord ++ tailWord_420053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420064 : List Nat := [2, 1, 1, 3, 1, 3, 1, 3, 7]
def baseStart_420064 : Nat := 118140960795 + 420064 * 2 ^ 59
def prefixEnd_420064 : Nat := 4983230072969 + 3 ^ 40 * 420064 * 2
def baseEnd_420064 : Nat := 47932163922299940304037

theorem tailTrace_420064 : CollatzResearch.WordTrace tailWord_420064 prefixEnd_420064 47932163922299940304037 := by
  unfold tailWord_420064
  simp only [CollatzResearch.WordTrace]
  refine ⟨7660496375093672032349623, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10213995166791562709799497 7660496375093672032349623)
  ·
    refine ⟨11490744562640508048524435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7660496375093672032349623 11490744562640508048524435)
    ·
      refine ⟨17236116843960762072786653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11490744562640508048524435 17236116843960762072786653)
      ·
        refine ⟨6463543816485285777294995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17236116843960762072786653 6463543816485285777294995)
        ·
          refine ⟨9695315724727928665942493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6463543816485285777294995 9695315724727928665942493)
          ·
            refine ⟨3635743396772973249728435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9695315724727928665942493 3635743396772973249728435)
            ·
              refine ⟨5453615095159459874592653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3635743396772973249728435 5453615095159459874592653)
              ·
                refine ⟨2045105660684797452972245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5453615095159459874592653 2045105660684797452972245)
                ·
                  refine ⟨47932163922299940304037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2045105660684797452972245 47932163922299940304037)
                  ·
                    rfl

theorem cell22_420064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 3, 1, 3, 7].length) (baseStart_420064 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420064 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420064 prefixEnd_420064 := by exact prefixLift 420064
  have htrace : WordTrace (prefixWord ++ tailWord_420064) baseStart_420064 baseEnd_420064 := by
    simpa [prefixWord, tailWord_420064, baseEnd_420064] using wordTrace_append hprefix tailTrace_420064
  have hstable : (prefixWord ++ tailWord_420064).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420064).length < 2 ^ (prefixWord ++ tailWord_420064).sum := by decide
  have hdescent : baseEnd_420064 < baseStart_420064 := by decide
  rcases family_descends (prefixWord ++ tailWord_420064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420111 : List Nat := [1, 1, 2, 1, 1, 1, 3, 7, 1, 4]
def baseStart_420111 : Nat := 118140960795 + 420111 * 2 ^ 59
def prefixEnd_420111 : Nat := 4983230072969 + 3 ^ 40 * 420111 * 2
def baseEnd_420111 : Nat := 143812580827407364986967

theorem tailTrace_420111 : CollatzResearch.WordTrace tailWord_420111 prefixEnd_420111 143812580827407364986967 := by
  unfold tailWord_420111
  simp only [CollatzResearch.WordTrace]
  refine ⟨15322706981017071091660187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10215137987344714061106791 15322706981017071091660187)
  ·
    refine ⟨22984060471525606637490281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15322706981017071091660187 22984060471525606637490281)
    ·
      refine ⟨17238045353644204978117711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22984060471525606637490281 17238045353644204978117711)
      ·
        refine ⟨25857068030466307467176567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17238045353644204978117711 25857068030466307467176567)
        ·
          refine ⟨38785602045699461200764851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25857068030466307467176567 38785602045699461200764851)
          ·
            refine ⟨58178403068549191801147277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38785602045699461200764851 58178403068549191801147277)
            ·
              refine ⟨21816901150705946925430229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 58178403068549191801147277 21816901150705946925430229)
              ·
                refine ⟨511333620719670631064771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 21816901150705946925430229 511333620719670631064771)
                ·
                  refine ⟨767000431079505946597157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511333620719670631064771 767000431079505946597157)
                  ·
                    refine ⟨143812580827407364986967, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767000431079505946597157 143812580827407364986967)
                    ·
                      rfl

theorem cell22_420111_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 3, 7, 1, 4].length) (baseStart_420111 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420111 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420111 prefixEnd_420111 := by exact prefixLift 420111
  have htrace : WordTrace (prefixWord ++ tailWord_420111) baseStart_420111 baseEnd_420111 := by
    simpa [prefixWord, tailWord_420111, baseEnd_420111] using wordTrace_append hprefix tailTrace_420111
  have hstable : (prefixWord ++ tailWord_420111).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420111).length < 2 ^ (prefixWord ++ tailWord_420111).sum := by decide
  have hdescent : baseEnd_420111 < baseStart_420111 := by decide
  rcases family_descends (prefixWord ++ tailWord_420111) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420156 : List Nat := [2, 2, 2, 2, 1, 2, 3, 1, 1, 6]
def baseStart_420156 : Nat := 118140960795 + 420156 * 2 ^ 59
def prefixEnd_420156 : Nat := 4983230072969 + 3 ^ 40 * 420156 * 2
def baseEnd_420156 : Nat := 143827985247042247611829

theorem tailTrace_420156 : CollatzResearch.WordTrace tailWord_420156 prefixEnd_420156 143827985247042247611829 := by
  unfold tailWord_420156
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662174132927021888524161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10216232177236029184698881 7662174132927021888524161)
  ·
    refine ⟨5746630599695266416393121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7662174132927021888524161 5746630599695266416393121)
    ·
      refine ⟨4309972949771449812294841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5746630599695266416393121 4309972949771449812294841)
      ·
        refine ⟨3232479712328587359221131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4309972949771449812294841 3232479712328587359221131)
        ·
          refine ⟨4848719568492881038831697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3232479712328587359221131 4848719568492881038831697)
          ·
            refine ⟨3636539676369660779123773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4848719568492881038831697 3636539676369660779123773)
            ·
              refine ⟨1363702378638622792171415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3636539676369660779123773 1363702378638622792171415)
              ·
                refine ⟨2045553567957934188257123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1363702378638622792171415 2045553567957934188257123)
                ·
                  refine ⟨3068330351936901282385685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2045553567957934188257123 3068330351936901282385685)
                  ·
                    refine ⟨143827985247042247611829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3068330351936901282385685 143827985247042247611829)
                    ·
                      rfl

theorem cell22_420156_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 2, 3, 1, 1, 6].length) (baseStart_420156 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420156 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420156 prefixEnd_420156 := by exact prefixLift 420156
  have htrace : WordTrace (prefixWord ++ tailWord_420156) baseStart_420156 baseEnd_420156 := by
    simpa [prefixWord, tailWord_420156, baseEnd_420156] using wordTrace_append hprefix tailTrace_420156
  have hstable : (prefixWord ++ tailWord_420156).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420156).length < 2 ^ (prefixWord ++ tailWord_420156).sum := by decide
  have hdescent : baseEnd_420156 < baseStart_420156 := by decide
  rcases family_descends (prefixWord ++ tailWord_420156) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420158 : List Nat := [4, 2, 1, 2, 1, 2, 2, 2, 1, 5]
def baseStart_420158 : Nat := 118140960795 + 420158 * 2 ^ 59
def prefixEnd_420158 : Nat := 4983230072969 + 3 ^ 40 * 420158 * 2
def baseEnd_420158 : Nat := 143828669887914909061823

theorem tailTrace_420158 : CollatzResearch.WordTrace tailWord_420158 prefixEnd_420158 143828669887914909061823 := by
  unfold tailWord_420158
  simp only [CollatzResearch.WordTrace]
  refine ⟨1915552651480849764827641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 10216280807897865412414085 1915552651480849764827641)
  ·
    refine ⟨1436664488610637323620731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1915552651480849764827641 1436664488610637323620731)
    ·
      refine ⟨2154996732915955985431097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1436664488610637323620731 2154996732915955985431097)
      ·
        refine ⟨1616247549686966989073323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 2154996732915955985431097 1616247549686966989073323)
        ·
          refine ⟨2424371324530450483609985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616247549686966989073323 2424371324530450483609985)
          ·
            refine ⟨1818278493397837862707489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424371324530450483609985 1818278493397837862707489)
            ·
              refine ⟨1363708870048378397030617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1818278493397837862707489 1363708870048378397030617)
              ·
                refine ⟨1022781652536283797772963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1363708870048378397030617 1022781652536283797772963)
                ·
                  refine ⟨1534172478804425696659445, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1022781652536283797772963 1534172478804425696659445)
                  ·
                    refine ⟨143828669887914909061823, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1534172478804425696659445 143828669887914909061823)
                    ·
                      rfl

theorem cell22_420158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 2, 2, 2, 1, 5].length) (baseStart_420158 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420158 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420158 prefixEnd_420158 := by exact prefixLift 420158
  have htrace : WordTrace (prefixWord ++ tailWord_420158) baseStart_420158 baseEnd_420158 := by
    simpa [prefixWord, tailWord_420158, baseEnd_420158] using wordTrace_append hprefix tailTrace_420158
  have hstable : (prefixWord ++ tailWord_420158).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420158).length < 2 ^ (prefixWord ++ tailWord_420158).sum := by decide
  have hdescent : baseEnd_420158 < baseStart_420158 := by decide
  rcases family_descends (prefixWord ++ tailWord_420158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420192 : List Nat := [2, 1, 1, 3, 5, 1, 3, 1, 2, 3]
def baseStart_420192 : Nat := 118140960795 + 420192 * 2 ^ 59
def prefixEnd_420192 : Nat := 4983230072969 + 3 ^ 40 * 420192 * 2
def baseEnd_420192 : Nat := 143840308782750153711719

theorem tailTrace_420192 : CollatzResearch.WordTrace tailWord_420192 prefixEnd_420192 143840308782750153711719 := by
  unfold tailWord_420192
  simp only [CollatzResearch.WordTrace]
  refine ⟨7662830646861810962679415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10217107529149081283572553 7662830646861810962679415)
  ·
    refine ⟨11494245970292716444019123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7662830646861810962679415 11494245970292716444019123)
    ·
      refine ⟨17241368955439074666028685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11494245970292716444019123 17241368955439074666028685)
      ·
        refine ⟨6465513358289652999760757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17241368955439074666028685 6465513358289652999760757)
        ·
          refine ⟨606141877339654968727571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 6465513358289652999760757 606141877339654968727571)
          ·
            refine ⟨909212816009482453091357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606141877339654968727571 909212816009482453091357)
            ·
              refine ⟨340954806003555919909259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 909212816009482453091357 340954806003555919909259)
              ·
                refine ⟨511432209005333879863889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 340954806003555919909259 511432209005333879863889)
                ·
                  refine ⟨383574156754000409897917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511432209005333879863889 383574156754000409897917)
                  ·
                    refine ⟨143840308782750153711719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383574156754000409897917 143840308782750153711719)
                    ·
                      rfl

theorem cell22_420192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 1, 3, 1, 2, 3].length) (baseStart_420192 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420192 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420192 prefixEnd_420192 := by exact prefixLift 420192
  have htrace : WordTrace (prefixWord ++ tailWord_420192) baseStart_420192 baseEnd_420192 := by
    simpa [prefixWord, tailWord_420192, baseEnd_420192] using wordTrace_append hprefix tailTrace_420192
  have hstable : (prefixWord ++ tailWord_420192).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420192).length < 2 ^ (prefixWord ++ tailWord_420192).sum := by decide
  have hdescent : baseEnd_420192 < baseStart_420192 := by decide
  rcases family_descends (prefixWord ++ tailWord_420192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420220 : List Nat := [2, 2, 2, 1, 1, 1, 2, 7, 1, 3]
def baseStart_420220 : Nat := 118140960795 + 420220 * 2 ^ 59
def prefixEnd_420220 : Nat := 4983230072969 + 3 ^ 40 * 420220 * 2
def baseEnd_420220 : Nat := 143849893754967414011633

theorem tailTrace_420220 : CollatzResearch.WordTrace tailWord_420220 prefixEnd_420220 143849893754967414011633 := by
  unfold tailWord_420220
  simp only [CollatzResearch.WordTrace]
  refine ⟨7663341268811091353689057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10217788358414788471585409 7663341268811091353689057)
  ·
    refine ⟨5747505951608318515266793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7663341268811091353689057 5747505951608318515266793)
    ·
      refine ⟨4310629463706238886450095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5747505951608318515266793 4310629463706238886450095)
      ·
        refine ⟨6465944195559358329675143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4310629463706238886450095 6465944195559358329675143)
        ·
          refine ⟨9698916293339037494512715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6465944195559358329675143 9698916293339037494512715)
          ·
            refine ⟨14548374440008556241769073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9698916293339037494512715 14548374440008556241769073)
            ·
              refine ⟨10911280830006417181326805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14548374440008556241769073 10911280830006417181326805)
              ·
                refine ⟨255733144453275402687347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 10911280830006417181326805 255733144453275402687347)
                ·
                  refine ⟨383599716679913104031021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 255733144453275402687347 383599716679913104031021)
                  ·
                    refine ⟨143849893754967414011633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383599716679913104031021 143849893754967414011633)
                    ·
                      rfl

theorem cell22_420220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 2, 7, 1, 3].length) (baseStart_420220 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420220 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420220 prefixEnd_420220 := by exact prefixLift 420220
  have htrace : WordTrace (prefixWord ++ tailWord_420220) baseStart_420220 baseEnd_420220 := by
    simpa [prefixWord, tailWord_420220, baseEnd_420220] using wordTrace_append hprefix tailTrace_420220
  have hstable : (prefixWord ++ tailWord_420220).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420220).length < 2 ^ (prefixWord ++ tailWord_420220).sum := by decide
  have hdescent : baseEnd_420220 < baseStart_420220 := by decide
  rcases family_descends (prefixWord ++ tailWord_420220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420250 : List Nat := [3, 1, 1, 4, 1, 2, 4, 1, 5]
def baseStart_420250 : Nat := 118140960795 + 420250 * 2 ^ 59
def prefixEnd_420250 : Nat := 4983230072969 + 3 ^ 40 * 420250 * 2
def baseEnd_420250 : Nat := 47953387789352445253847

theorem tailTrace_420250 : CollatzResearch.WordTrace tailWord_420250 prefixEnd_420250 47953387789352445253847 := by
  unfold tailWord_420250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3831944181878374457742551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 10218517818342331887313469 3831944181878374457742551)
  ·
    refine ⟨5747916272817561686613827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3831944181878374457742551 5747916272817561686613827)
    ·
      refine ⟨8621874409226342529920741, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5747916272817561686613827 8621874409226342529920741)
      ·
        refine ⟨1616601451729939224360139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8621874409226342529920741 1616601451729939224360139)
        ·
          refine ⟨2424902177594908836540209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1616601451729939224360139 2424902177594908836540209)
          ·
            refine ⟨1818676633196181627405157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2424902177594908836540209 1818676633196181627405157)
            ·
              refine ⟨341001868724284055138467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1818676633196181627405157 341001868724284055138467)
              ·
                refine ⟨511502803086426082707701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 341001868724284055138467 511502803086426082707701)
                ·
                  refine ⟨47953387789352445253847, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 511502803086426082707701 47953387789352445253847)
                  ·
                    rfl

theorem cell22_420250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 4, 1, 5].length) (baseStart_420250 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420250 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420250 prefixEnd_420250 := by exact prefixLift 420250
  have htrace : WordTrace (prefixWord ++ tailWord_420250) baseStart_420250 baseEnd_420250 := by
    simpa [prefixWord, tailWord_420250, baseEnd_420250] using wordTrace_append hprefix tailTrace_420250
  have hstable : (prefixWord ++ tailWord_420250).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420250).length < 2 ^ (prefixWord ++ tailWord_420250).sum := by decide
  have hdescent : baseEnd_420250 < baseStart_420250 := by decide
  rcases family_descends (prefixWord ++ tailWord_420250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420261 : List Nat := [1, 3, 1, 2, 1, 1, 4, 1, 8]
def baseStart_420261 : Nat := 118140960795 + 420261 * 2 ^ 59
def prefixEnd_420261 : Nat := 4983230072969 + 3 ^ 40 * 420261 * 2
def baseEnd_420261 : Nat := 47954642964285657912169

theorem tailTrace_420261 : CollatzResearch.WordTrace tailWord_420261 prefixEnd_420261 47954642964285657912169 := by
  unfold tailWord_420261
  simp only [CollatzResearch.WordTrace]
  refine ⟨15328177930473646709620637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10218785286982431139747091 15328177930473646709620637)
  ·
    refine ⟨5748066723927617516107739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15328177930473646709620637 5748066723927617516107739)
    ·
      refine ⟨8622100085891426274161609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5748066723927617516107739 8622100085891426274161609)
      ·
        refine ⟨6466575064418569705621207, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8622100085891426274161609 6466575064418569705621207)
        ·
          refine ⟨9699862596627854558431811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6466575064418569705621207 9699862596627854558431811)
          ·
            refine ⟨14549793894941781837647717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9699862596627854558431811 14549793894941781837647717)
            ·
              refine ⟨2728086355301584094558947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14549793894941781837647717 2728086355301584094558947)
              ·
                refine ⟨4092129532952376141838421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2728086355301584094558947 4092129532952376141838421)
                ·
                  refine ⟨47954642964285657912169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 4092129532952376141838421 47954642964285657912169)
                  ·
                    rfl

theorem cell22_420261_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 4, 1, 8].length) (baseStart_420261 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420261 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420261 prefixEnd_420261 := by exact prefixLift 420261
  have htrace : WordTrace (prefixWord ++ tailWord_420261) baseStart_420261 baseEnd_420261 := by
    simpa [prefixWord, tailWord_420261, baseEnd_420261] using wordTrace_append hprefix tailTrace_420261
  have hstable : (prefixWord ++ tailWord_420261).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420261).length < 2 ^ (prefixWord ++ tailWord_420261).sum := by decide
  have hdescent : baseEnd_420261 < baseStart_420261 := by decide
  rcases family_descends (prefixWord ++ tailWord_420261) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420291 : List Nat := [1, 1, 1, 3, 1, 1, 3, 2, 3, 6]
def baseStart_420291 : Nat := 118140960795 + 420291 * 2 ^ 59
def prefixEnd_420291 : Nat := 4983230072969 + 3 ^ 40 * 420291 * 2
def baseEnd_420291 : Nat := 143874198505946895486415

theorem tailTrace_420291 : CollatzResearch.WordTrace tailWord_420291 prefixEnd_420291 143874198505946895486415 := by
  unfold tailWord_420291
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329272120364961833212727, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10219514746909974555475151 15329272120364961833212727)
  ·
    refine ⟨22993908180547442749819091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15329272120364961833212727 22993908180547442749819091)
    ·
      refine ⟨34490862270821164124728637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22993908180547442749819091 34490862270821164124728637)
      ·
        refine ⟨12934073351557936546773239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34490862270821164124728637 12934073351557936546773239)
        ·
          refine ⟨19401110027336904820159859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12934073351557936546773239 19401110027336904820159859)
          ·
            refine ⟨29101665041005357230239789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19401110027336904820159859 29101665041005357230239789)
            ·
              refine ⟨10913124390377008961339921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29101665041005357230239789 10913124390377008961339921)
              ·
                refine ⟨8184843292782756721004941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10913124390377008961339921 8184843292782756721004941)
                ·
                  refine ⟨3069316234793533770376853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8184843292782756721004941 3069316234793533770376853)
                  ·
                    refine ⟨143874198505946895486415, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3069316234793533770376853 143874198505946895486415)
                    ·
                      rfl

theorem cell22_420291_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 2, 3, 6].length) (baseStart_420291 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420291 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420291 prefixEnd_420291 := by exact prefixLift 420291
  have htrace : WordTrace (prefixWord ++ tailWord_420291) baseStart_420291 baseEnd_420291 := by
    simpa [prefixWord, tailWord_420291, baseEnd_420291] using wordTrace_append hprefix tailTrace_420291
  have hstable : (prefixWord ++ tailWord_420291).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420291).length < 2 ^ (prefixWord ++ tailWord_420291).sum := by decide
  have hdescent : baseEnd_420291 < baseStart_420291 := by decide
  rcases family_descends (prefixWord ++ tailWord_420291) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420295 : List Nat := [1, 1, 4, 1, 1, 5, 1, 4, 4]
def baseStart_420295 : Nat := 118140960795 + 420295 * 2 ^ 59
def prefixEnd_420295 : Nat := 4983230072969 + 3 ^ 40 * 420295 * 2
def baseEnd_420295 : Nat := 47958522595897406128801

theorem tailTrace_420295 : CollatzResearch.WordTrace tailWord_420295 prefixEnd_420295 47958522595897406128801 := by
  unfold tailWord_420295
  simp only [CollatzResearch.WordTrace]
  refine ⟨15329418012350470516358339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10219612008233647010905559 15329418012350470516358339)
  ·
    refine ⟨22994127018525705774537509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15329418012350470516358339 22994127018525705774537509)
    ·
      refine ⟨4311398815973569832725783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22994127018525705774537509 4311398815973569832725783)
      ·
        refine ⟨6467098223960354749088675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4311398815973569832725783 6467098223960354749088675)
        ·
          refine ⟨9700647335940532123633013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6467098223960354749088675 9700647335940532123633013)
          ·
            refine ⟨909435687744424886590595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 9700647335940532123633013 909435687744424886590595)
            ·
              refine ⟨1364153531616637329885893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909435687744424886590595 1364153531616637329885893)
              ·
                refine ⟨255778787178119499353605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1364153531616637329885893 255778787178119499353605)
                ·
                  refine ⟨47958522595897406128801, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 255778787178119499353605 47958522595897406128801)
                  ·
                    rfl

theorem cell22_420295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 5, 1, 4, 4].length) (baseStart_420295 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420295 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420295 prefixEnd_420295 := by exact prefixLift 420295
  have htrace : WordTrace (prefixWord ++ tailWord_420295) baseStart_420295 baseEnd_420295 := by
    simpa [prefixWord, tailWord_420295, baseEnd_420295] using wordTrace_append hprefix tailTrace_420295
  have hstable : (prefixWord ++ tailWord_420295).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420295).length < 2 ^ (prefixWord ++ tailWord_420295).sum := by decide
  have hdescent : baseEnd_420295 < baseStart_420295 := by decide
  rcases family_descends (prefixWord ++ tailWord_420295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420325 : List Nat := [1, 3, 1, 5, 2, 1, 1, 1, 1, 6]
def baseStart_420325 : Nat := 118140960795 + 420325 * 2 ^ 59
def prefixEnd_420325 : Nat := 4983230072969 + 3 ^ 40 * 420325 * 2
def baseEnd_420325 : Nat := 143885837400782140136311

theorem tailTrace_420325 : CollatzResearch.WordTrace tailWord_420325 prefixEnd_420325 143885837400782140136311 := by
  unfold tailWord_420325
  simp only [CollatzResearch.WordTrace]
  refine ⟨15330512202241785639950429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10220341468161190426633619 15330512202241785639950429)
  ·
    refine ⟨5748942075840669614981411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15330512202241785639950429 5748942075840669614981411)
    ·
      refine ⟨8623413113761004422472117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5748942075840669614981411 8623413113761004422472117)
      ·
        refine ⟨808444979415094164606761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 8623413113761004422472117 808444979415094164606761)
        ·
          refine ⟨606333734561320623455071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 808444979415094164606761 606333734561320623455071)
          ·
            refine ⟨909500601841980935182607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606333734561320623455071 909500601841980935182607)
            ·
              refine ⟨1364250902762971402773911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 909500601841980935182607 1364250902762971402773911)
              ·
                refine ⟨2046376354144457104160867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1364250902762971402773911 2046376354144457104160867)
                ·
                  refine ⟨3069564531216685656241301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2046376354144457104160867 3069564531216685656241301)
                  ·
                    refine ⟨143885837400782140136311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 3069564531216685656241301 143885837400782140136311)
                    ·
                      rfl

theorem cell22_420325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 5, 2, 1, 1, 1, 1, 6].length) (baseStart_420325 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420325 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420325 prefixEnd_420325 := by exact prefixLift 420325
  have htrace : WordTrace (prefixWord ++ tailWord_420325) baseStart_420325 baseEnd_420325 := by
    simpa [prefixWord, tailWord_420325, baseEnd_420325] using wordTrace_append hprefix tailTrace_420325
  have hstable : (prefixWord ++ tailWord_420325).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420325).length < 2 ^ (prefixWord ++ tailWord_420325).sum := by decide
  have hdescent : baseEnd_420325 < baseStart_420325 := by decide
  rcases family_descends (prefixWord ++ tailWord_420325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420355 : List Nat := [1, 1, 1, 3, 2, 1, 6, 1, 3, 3]
def baseStart_420355 : Nat := 118140960795 + 420355 * 2 ^ 59
def prefixEnd_420355 : Nat := 4983230072969 + 3 ^ 40 * 420355 * 2
def baseEnd_420355 : Nat := 143896107013872061886219

theorem tailTrace_420355 : CollatzResearch.WordTrace tailWord_420355 prefixEnd_420355 143896107013872061886219 := by
  unfold tailWord_420355
  simp only [CollatzResearch.WordTrace]
  refine ⟨15331606392133100763542519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10221070928088733842361679 15331606392133100763542519)
  ·
    refine ⟨22997409588199651145313779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15331606392133100763542519 22997409588199651145313779)
    ·
      refine ⟨34496114382299476717970669, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22997409588199651145313779 34496114382299476717970669)
      ·
        refine ⟨12936042893362303769239001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34496114382299476717970669 12936042893362303769239001)
        ·
          refine ⟨9702032170021727826929251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12936042893362303769239001 9702032170021727826929251)
          ·
            refine ⟨14553048255032591740393877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9702032170021727826929251 14553048255032591740393877)
            ·
              refine ⟨682174136954652737830963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 14553048255032591740393877 682174136954652737830963)
              ·
                refine ⟨1023261205431979106746445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 682174136954652737830963 1023261205431979106746445)
                ·
                  refine ⟨383722952036992165029917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1023261205431979106746445 383722952036992165029917)
                  ·
                    refine ⟨143896107013872061886219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383722952036992165029917 143896107013872061886219)
                    ·
                      rfl

theorem cell22_420355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 1, 6, 1, 3, 3].length) (baseStart_420355 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420355 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420355 prefixEnd_420355 := by exact prefixLift 420355
  have htrace : WordTrace (prefixWord ++ tailWord_420355) baseStart_420355 baseEnd_420355 := by
    simpa [prefixWord, tailWord_420355, baseEnd_420355] using wordTrace_append hprefix tailTrace_420355
  have hstable : (prefixWord ++ tailWord_420355).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420355).length < 2 ^ (prefixWord ++ tailWord_420355).sum := by decide
  have hdescent : baseEnd_420355 < baseStart_420355 := by decide
  rcases family_descends (prefixWord ++ tailWord_420355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420460 : List Nat := [2, 2, 1, 1, 3, 1, 4, 2, 2, 4]
def baseStart_420460 : Nat := 118140960795 + 420460 * 2 ^ 59
def prefixEnd_420460 : Nat := 4983230072969 + 3 ^ 40 * 420460 * 2
def baseEnd_420460 : Nat := 143932050659686788010897

theorem tailTrace_420460 : CollatzResearch.WordTrace tailWord_420460 prefixEnd_420460 143932050659686788010897 := by
  unfold tailWord_420460
  simp only [CollatzResearch.WordTrace]
  refine ⟨7667718028376351848057417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10223624037835135797409889 7667718028376351848057417)
  ·
    refine ⟨5750788521282263886043063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7667718028376351848057417 5750788521282263886043063)
    ·
      refine ⟨8626182781923395829064595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5750788521282263886043063 8626182781923395829064595)
      ·
        refine ⟨12939274172885093743596893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8626182781923395829064595 12939274172885093743596893)
        ·
          refine ⟨4852227814831910153848835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12939274172885093743596893 4852227814831910153848835)
          ·
            refine ⟨7278341722247865230773253, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4852227814831910153848835 7278341722247865230773253)
            ·
              refine ⟨1364689072921474730769985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 7278341722247865230773253 1364689072921474730769985)
              ·
                refine ⟨1023516804691106048077489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1364689072921474730769985 1023516804691106048077489)
                ·
                  refine ⟨767637603518329536058117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1023516804691106048077489 767637603518329536058117)
                  ·
                    refine ⟨143932050659686788010897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767637603518329536058117 143932050659686788010897)
                    ·
                      rfl

theorem cell22_420460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 4].length) (baseStart_420460 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420460 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420460 prefixEnd_420460 := by exact prefixLift 420460
  have htrace : WordTrace (prefixWord ++ tailWord_420460) baseStart_420460 baseEnd_420460 := by
    simpa [prefixWord, tailWord_420460, baseEnd_420460] using wordTrace_append hprefix tailTrace_420460
  have hstable : (prefixWord ++ tailWord_420460).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420460).length < 2 ^ (prefixWord ++ tailWord_420460).sum := by decide
  have hdescent : baseEnd_420460 < baseStart_420460 := by decide
  rcases family_descends (prefixWord ++ tailWord_420460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420567 : List Nat := [1, 1, 3, 2, 1, 4, 2, 3, 1, 4]
def baseStart_420567 : Nat := 118140960795 + 420567 * 2 ^ 59
def prefixEnd_420567 : Nat := 4983230072969 + 3 ^ 40 * 420567 * 2
def baseEnd_420567 : Nat := 143968678946374175585569

theorem tailTrace_420567 : CollatzResearch.WordTrace tailWord_420567 prefixEnd_420567 143968678946374175585569 := by
  unfold tailWord_420567
  simp only [CollatzResearch.WordTrace]
  refine ⟨15339338667365060970259955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10226225778243373980173303 15339338667365060970259955)
  ·
    refine ⟨23009008001047591455389933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15339338667365060970259955 23009008001047591455389933)
    ·
      refine ⟨8628378000392846795771225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23009008001047591455389933 8628378000392846795771225)
      ·
        refine ⟨6471283500294635096828419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8628378000392846795771225 6471283500294635096828419)
        ·
          refine ⟨9706925250441952645242629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6471283500294635096828419 9706925250441952645242629)
          ·
            refine ⟨1820048484457866120982993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 9706925250441952645242629 1820048484457866120982993)
            ·
              refine ⟨1365036363343399590737245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1820048484457866120982993 1365036363343399590737245)
              ·
                refine ⟨511888636253774846526467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365036363343399590737245 511888636253774846526467)
                ·
                  refine ⟨767832954380662269789701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 511888636253774846526467 767832954380662269789701)
                  ·
                    refine ⟨143968678946374175585569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767832954380662269789701 143968678946374175585569)
                    ·
                      rfl

theorem cell22_420567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 4, 2, 3, 1, 4].length) (baseStart_420567 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420567 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420567 prefixEnd_420567 := by exact prefixLift 420567
  have htrace : WordTrace (prefixWord ++ tailWord_420567) baseStart_420567 baseEnd_420567 := by
    simpa [prefixWord, tailWord_420567, baseEnd_420567] using wordTrace_append hprefix tailTrace_420567
  have hstable : (prefixWord ++ tailWord_420567).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420567).length < 2 ^ (prefixWord ++ tailWord_420567).sum := by decide
  have hdescent : baseEnd_420567 < baseStart_420567 := by decide
  rcases family_descends (prefixWord ++ tailWord_420567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420595 : List Nat := [1, 1, 1, 2, 2, 3, 1, 1, 6, 4]
def baseStart_420595 : Nat := 118140960795 + 420595 * 2 ^ 59
def prefixEnd_420595 : Nat := 4983230072969 + 3 ^ 40 * 420595 * 2
def baseEnd_420595 : Nat := 143978263918591435885483

theorem tailTrace_420595 : CollatzResearch.WordTrace tailWord_420595 prefixEnd_420595 143978263918591435885483 := by
  unfold tailWord_420595
  simp only [CollatzResearch.WordTrace]
  refine ⟨15340359911263621752279239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10226906607509081168186159 15340359911263621752279239)
  ·
    refine ⟨23010539866895432628418859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15340359911263621752279239 23010539866895432628418859)
    ·
      refine ⟨34515809800343148942628289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23010539866895432628418859 34515809800343148942628289)
      ·
        refine ⟨25886857350257361706971217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34515809800343148942628289 25886857350257361706971217)
        ·
          refine ⟨19415143012693021280228413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25886857350257361706971217 19415143012693021280228413)
          ·
            refine ⟨7280678629759882980085655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19415143012693021280228413 7280678629759882980085655)
            ·
              refine ⟨10921017944639824470128483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7280678629759882980085655 10921017944639824470128483)
              ·
                refine ⟨16381526916959736705192725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10921017944639824470128483 16381526916959736705192725)
                ·
                  refine ⟨767884074232487658055909, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 16381526916959736705192725 767884074232487658055909)
                  ·
                    refine ⟨143978263918591435885483, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 767884074232487658055909 143978263918591435885483)
                    ·
                      rfl

theorem cell22_420595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 1, 6, 4].length) (baseStart_420595 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420595 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420595 prefixEnd_420595 := by exact prefixLift 420595
  have htrace : WordTrace (prefixWord ++ tailWord_420595) baseStart_420595 baseEnd_420595 := by
    simpa [prefixWord, tailWord_420595, baseEnd_420595] using wordTrace_append hprefix tailTrace_420595
  have hstable : (prefixWord ++ tailWord_420595).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420595).length < 2 ^ (prefixWord ++ tailWord_420595).sum := by decide
  have hdescent : baseEnd_420595 < baseStart_420595 := by decide
  rcases family_descends (prefixWord ++ tailWord_420595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420631 : List Nat := [1, 1, 3, 4, 3, 1, 2, 2, 2, 3]
def baseStart_420631 : Nat := 118140960795 + 420631 * 2 ^ 59
def prefixEnd_420631 : Nat := 4983230072969 + 3 ^ 40 * 420631 * 2
def baseEnd_420631 : Nat := 143990587454299341985373

theorem tailTrace_420631 : CollatzResearch.WordTrace tailWord_420631 prefixEnd_420631 143990587454299341985373 := by
  unfold tailWord_420631
  simp only [CollatzResearch.WordTrace]
  refine ⟨15341672939133199900589747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10227781959422133267059831 15341672939133199900589747)
  ·
    refine ⟨23012509408699799850884621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15341672939133199900589747 23012509408699799850884621)
    ·
      refine ⟨8629691028262424944081733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23012509408699799850884621 8629691028262424944081733)
      ·
        refine ⟨1618067067799204677015325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 8629691028262424944081733 1618067067799204677015325)
        ·
          refine ⟨606775150424701753880747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1618067067799204677015325 606775150424701753880747)
          ·
            refine ⟨910162725637052630821121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 606775150424701753880747 910162725637052630821121)
            ·
              refine ⟨682622044227789473115841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 910162725637052630821121 682622044227789473115841)
              ·
                refine ⟨511966533170842104836881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 682622044227789473115841 511966533170842104836881)
                ·
                  refine ⟨383974899878131578627661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 511966533170842104836881 383974899878131578627661)
                  ·
                    refine ⟨143990587454299341985373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 383974899878131578627661 143990587454299341985373)
                    ·
                      rfl

theorem cell22_420631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 3, 1, 2, 2, 2, 3].length) (baseStart_420631 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420631 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420631 prefixEnd_420631 := by exact prefixLift 420631
  have htrace : WordTrace (prefixWord ++ tailWord_420631) baseStart_420631 baseEnd_420631 := by
    simpa [prefixWord, tailWord_420631, baseEnd_420631] using wordTrace_append hprefix tailTrace_420631
  have hstable : (prefixWord ++ tailWord_420631).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420631).length < 2 ^ (prefixWord ++ tailWord_420631).sum := by decide
  have hdescent : baseEnd_420631 < baseStart_420631 := by decide
  rcases family_descends (prefixWord ++ tailWord_420631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420644 : List Nat := [2, 3, 1, 3, 3, 2, 1, 7]
def baseStart_420644 : Nat := 118140960795 + 420644 * 2 ^ 59
def prefixEnd_420644 : Nat := 4983230072969 + 3 ^ 40 * 420644 * 2
def baseEnd_420644 : Nat := 15999448624441293490037

theorem tailTrace_420644 : CollatzResearch.WordTrace tailWord_420644 prefixEnd_420644 15999448624441293490037 := by
  unfold tailWord_420644
  simp only [CollatzResearch.WordTrace]
  refine ⟨7671073544043051560406493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10228098058724068747208657 7671073544043051560406493)
  ·
    refine ⟨2876652579016144335152435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 7671073544043051560406493 2876652579016144335152435)
    ·
      refine ⟨4314978868524216502728653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2876652579016144335152435 4314978868524216502728653)
      ·
        refine ⟨1618117075696581188523245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 4314978868524216502728653 1618117075696581188523245)
        ·
          refine ⟨606793903386217945696217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1618117075696581188523245 606793903386217945696217)
          ·
            refine ⟨455095427539663459272163, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 606793903386217945696217 455095427539663459272163)
            ·
              refine ⟨682643141309495188908245, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 455095427539663459272163 682643141309495188908245)
              ·
                refine ⟨15999448624441293490037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 682643141309495188908245 15999448624441293490037)
                ·
                  rfl

theorem cell22_420644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 3, 2, 1, 7].length) (baseStart_420644 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420644 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420644 prefixEnd_420644 := by exact prefixLift 420644
  have htrace : WordTrace (prefixWord ++ tailWord_420644) baseStart_420644 baseEnd_420644 := by
    simpa [prefixWord, tailWord_420644, baseEnd_420644] using wordTrace_append hprefix tailTrace_420644
  have hstable : (prefixWord ++ tailWord_420644).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420644).length < 2 ^ (prefixWord ++ tailWord_420644).sum := by decide
  have hdescent : baseEnd_420644 < baseStart_420644 := by decide
  rcases family_descends (prefixWord ++ tailWord_420644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420659 : List Nat := [1, 1, 1, 2, 6, 2, 1, 2, 3, 3]
def baseStart_420659 : Nat := 118140960795 + 420659 * 2 ^ 59
def prefixEnd_420659 : Nat := 4983230072969 + 3 ^ 40 * 420659 * 2
def baseEnd_420659 : Nat := 144000172426516602285287

theorem tailTrace_420659 : CollatzResearch.WordTrace tailWord_420659 prefixEnd_420659 144000172426516602285287 := by
  unfold tailWord_420659
  simp only [CollatzResearch.WordTrace]
  refine ⟨15342694183031760682609031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10228462788687840455072687 15342694183031760682609031)
  ·
    refine ⟨23014041274547641023913547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15342694183031760682609031 23014041274547641023913547)
    ·
      refine ⟨34521061911821461535870321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23014041274547641023913547 34521061911821461535870321)
      ·
        refine ⟨25890796433866096151902741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34521061911821461535870321 25890796433866096151902741)
        ·
          refine ⟨1213631082837473257120441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 25890796433866096151902741 1213631082837473257120441)
          ·
            refine ⟨910223312128104942840331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1213631082837473257120441 910223312128104942840331)
            ·
              refine ⟨1365334968192157414260497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 910223312128104942840331 1365334968192157414260497)
              ·
                refine ⟨1024001226144118060695373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1365334968192157414260497 1024001226144118060695373)
                ·
                  refine ⟨384000459804044272760765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 1024001226144118060695373 384000459804044272760765)
                  ·
                    refine ⟨144000172426516602285287, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 384000459804044272760765 144000172426516602285287)
                    ·
                      rfl

theorem cell22_420659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 2, 1, 2, 3, 3].length) (baseStart_420659 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420659 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420659 prefixEnd_420659 := by exact prefixLift 420659
  have htrace : WordTrace (prefixWord ++ tailWord_420659) baseStart_420659 baseEnd_420659 := by
    simpa [prefixWord, tailWord_420659, baseEnd_420659] using wordTrace_append hprefix tailTrace_420659
  have hstable : (prefixWord ++ tailWord_420659).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420659).length < 2 ^ (prefixWord ++ tailWord_420659).sum := by decide
  have hdescent : baseEnd_420659 < baseStart_420659 := by decide
  rcases family_descends (prefixWord ++ tailWord_420659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420732 : List Nat := [2, 2, 2, 1, 1, 1, 1, 6, 1, 5]
def baseStart_420732 : Nat := 118140960795 + 420732 * 2 ^ 59
def prefixEnd_420732 : Nat := 4983230072969 + 3 ^ 40 * 420732 * 2
def baseEnd_420732 : Nat := 144025161818368745210063

theorem tailTrace_420732 : CollatzResearch.WordTrace tailWord_420732 prefixEnd_420732 144025161818368745210063 := by
  unfold tailWord_420732
  simp only [CollatzResearch.WordTrace]
  refine ⟨7672678355883647075008225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10230237807844862766677633 7672678355883647075008225)
  ·
    refine ⟨5754508766912735306256169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7672678355883647075008225 5754508766912735306256169)
    ·
      refine ⟨4315881575184551479692127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 5754508766912735306256169 4315881575184551479692127)
      ·
        refine ⟨6473822362776827219538191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4315881575184551479692127 6473822362776827219538191)
        ·
          refine ⟨9710733544165240829307287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6473822362776827219538191 9710733544165240829307287)
          ·
            refine ⟨14566100316247861243960931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9710733544165240829307287 14566100316247861243960931)
            ·
              refine ⟨21849150474371791865941397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14566100316247861243960931 21849150474371791865941397)
              ·
                refine ⟨1024178928486177743716003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 21849150474371791865941397 1024178928486177743716003)
                ·
                  refine ⟨1536268392729266615574005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1024178928486177743716003 1536268392729266615574005)
                  ·
                    refine ⟨144025161818368745210063, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 1536268392729266615574005 144025161818368745210063)
                    ·
                      rfl

theorem cell22_420732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 1, 1, 6, 1, 5].length) (baseStart_420732 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420732 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420732 prefixEnd_420732 := by exact prefixLift 420732
  have htrace : WordTrace (prefixWord ++ tailWord_420732) baseStart_420732 baseEnd_420732 := by
    simpa [prefixWord, tailWord_420732, baseEnd_420732] using wordTrace_append hprefix tailTrace_420732
  have hstable : (prefixWord ++ tailWord_420732).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420732).length < 2 ^ (prefixWord ++ tailWord_420732).sum := by decide
  have hdescent : baseEnd_420732 < baseStart_420732 := by decide
  rcases family_descends (prefixWord ++ tailWord_420732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420747 : List Nat := [1, 1, 1, 1, 4, 2, 3, 1, 4, 4]
def baseStart_420747 : Nat := 118140960795 + 420747 * 2 ^ 59
def prefixEnd_420747 : Nat := 4983230072969 + 3 ^ 40 * 420747 * 2
def baseEnd_420747 : Nat := 144030296624913706085017

theorem tailTrace_420747 : CollatzResearch.WordTrace tailWord_420747 prefixEnd_420747 144030296624913706085017 := by
  unfold tailWord_420747
  simp only [CollatzResearch.WordTrace]
  refine ⟨15345903806712951711812495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10230602537808634474541663 15345903806712951711812495)
  ·
    refine ⟨23018855710069427567718743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15345903806712951711812495 23018855710069427567718743)
    ·
      refine ⟨34528283565104141351578115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23018855710069427567718743 34528283565104141351578115)
      ·
        refine ⟨51792425347656212027367173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34528283565104141351578115 51792425347656212027367173)
        ·
          refine ⟨9711079752685539755131345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51792425347656212027367173 9711079752685539755131345)
          ·
            refine ⟨7283309814514154816348509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9711079752685539755131345 7283309814514154816348509)
            ·
              refine ⟨2731241180442808056130691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7283309814514154816348509 2731241180442808056130691)
              ·
                refine ⟨4096861770664212084196037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2731241180442808056130691 4096861770664212084196037)
                ·
                  refine ⟨768161581999539765786757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 4096861770664212084196037 768161581999539765786757)
                  ·
                    refine ⟨144030296624913706085017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 768161581999539765786757 144030296624913706085017)
                    ·
                      rfl

theorem cell22_420747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 3, 1, 4, 4].length) (baseStart_420747 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420747 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420747 prefixEnd_420747 := by exact prefixLift 420747
  have htrace : WordTrace (prefixWord ++ tailWord_420747) baseStart_420747 baseEnd_420747 := by
    simpa [prefixWord, tailWord_420747, baseEnd_420747] using wordTrace_append hprefix tailTrace_420747
  have hstable : (prefixWord ++ tailWord_420747).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420747).length < 2 ^ (prefixWord ++ tailWord_420747).sum := by decide
  have hdescent : baseEnd_420747 < baseStart_420747 := by decide
  rcases family_descends (prefixWord ++ tailWord_420747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420807 : List Nat := [1, 1, 4, 1, 1, 2, 2, 3, 7]
def baseStart_420807 : Nat := 118140960795 + 420807 * 2 ^ 59
def prefixEnd_420807 : Nat := 4983230072969 + 3 ^ 40 * 420807 * 2
def baseEnd_420807 : Nat := 48016945283697849861611

theorem tailTrace_420807 : CollatzResearch.WordTrace tailWord_420807 prefixEnd_420807 48016945283697849861611 := by
  unfold tailWord_420807
  simp only [CollatzResearch.WordTrace]
  refine ⟨15348092186495581958996675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 10232061457663721305997783 15348092186495581958996675)
  ·
    refine ⟨23022138279743372938495013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15348092186495581958996675 23022138279743372938495013)
    ·
      refine ⟨4316650927451882425967815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23022138279743372938495013 4316650927451882425967815)
      ·
        refine ⟨6474976391177823638951723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4316650927451882425967815 6474976391177823638951723)
        ·
          refine ⟨9712464586766735458427585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6474976391177823638951723 9712464586766735458427585)
          ·
            refine ⟨7284348440075051593820689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9712464586766735458427585 7284348440075051593820689)
            ·
              refine ⟨5463261330056288695365517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7284348440075051593820689 5463261330056288695365517)
              ·
                refine ⟨2048722998771108260762069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5463261330056288695365517 2048722998771108260762069)
                ·
                  refine ⟨48016945283697849861611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 2048722998771108260762069 48016945283697849861611)
                  ·
                    rfl

theorem cell22_420807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 2, 2, 3, 7].length) (baseStart_420807 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420807 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420807 prefixEnd_420807 := by exact prefixLift 420807
  have htrace : WordTrace (prefixWord ++ tailWord_420807) baseStart_420807 baseEnd_420807 := by
    simpa [prefixWord, tailWord_420807, baseEnd_420807] using wordTrace_append hprefix tailTrace_420807
  have hstable : (prefixWord ++ tailWord_420807).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420807).length < 2 ^ (prefixWord ++ tailWord_420807).sum := by decide
  have hdescent : baseEnd_420807 < baseStart_420807 := by decide
  rcases family_descends (prefixWord ++ tailWord_420807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_420824 : List Nat := [2, 1, 2, 2, 2, 3, 2, 3, 5]
def baseStart_420824 : Nat := 118140960795 + 420824 * 2 ^ 59
def prefixEnd_420824 : Nat := 4983230072969 + 3 ^ 40 * 420824 * 2
def baseEnd_420824 : Nat := 48018885099503723969927

theorem tailTrace_420824 : CollatzResearch.WordTrace tailWord_420824 prefixEnd_420824 48018885099503723969927 := by
  unfold tailWord_420824
  simp only [CollatzResearch.WordTrace]
  refine ⟨7674356113716996931182763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 10232474818289329241577017 7674356113716996931182763)
  ·
    refine ⟨11511534170575495396774145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7674356113716996931182763 11511534170575495396774145)
    ·
      refine ⟨8633650627931621547580609, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11511534170575495396774145 8633650627931621547580609)
      ·
        refine ⟨6475237970948716160685457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8633650627931621547580609 6475237970948716160685457)
        ·
          refine ⟨4856428478211537120514093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6475237970948716160685457 4856428478211537120514093)
          ·
            refine ⟨1821160679329326420192785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4856428478211537120514093 1821160679329326420192785)
            ·
              refine ⟨1365870509496994815144589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1821160679329326420192785 1365870509496994815144589)
              ·
                refine ⟨512201441061373055679221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1365870509496994815144589 512201441061373055679221)
                ·
                  refine ⟨48018885099503723969927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 512201441061373055679221 48018885099503723969927)
                  ·
                    rfl

theorem cell22_420824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 3, 2, 3, 5].length) (baseStart_420824 + u * 2 ^ 81) = endpoint ∧
      endpoint < baseStart_420824 + u * 2 ^ 81 := by
  have hprefix : WordTrace prefixWord baseStart_420824 prefixEnd_420824 := by exact prefixLift 420824
  have htrace : WordTrace (prefixWord ++ tailWord_420824) baseStart_420824 baseEnd_420824 := by
    simpa [prefixWord, tailWord_420824, baseEnd_420824] using wordTrace_append hprefix tailTrace_420824
  have hstable : (prefixWord ++ tailWord_420824).sum < 81 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_420824).length < 2 ^ (prefixWord ++ tailWord_420824).sum := by decide
  have hdescent : baseEnd_420824 < baseStart_420824 := by decide
  rcases family_descends (prefixWord ++ tailWord_420824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan22Incremental
