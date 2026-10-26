import V185TrunkScan23Chunk0210

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_1247806 : List Nat := [4, 2, 1, 4, 1, 1, 1, 2, 2, 1, 4]
def baseStart_1247806 : Nat := 118140960795 + 1247806 * 2 ^ 59
def prefixEnd_1247806 : Nat := 4983230072969 + 3 ^ 40 * 1247806 * 2
def baseEnd_1247806 : Nat := 640724241564250186986451

theorem tailTrace_1247806 : CollatzResearch.WordTrace tailWord_1247806 prefixEnd_1247806 640724241564250186986451 := by
  unfold tailWord_1247806
  simp only [CollatzResearch.WordTrace]
  refine ⟨5688902964677430642936409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30340815811612963428994181 5688902964677430642936409)
  ·
    refine ⟨4266677223508072982202307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5688902964677430642936409 4266677223508072982202307)
    ·
      refine ⟨6400015835262109473303461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4266677223508072982202307 6400015835262109473303461)
      ·
        refine ⟨1200002969111645526244399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6400015835262109473303461 1200002969111645526244399)
        ·
          refine ⟨1800004453667468289366599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200002969111645526244399 1800004453667468289366599)
          ·
            refine ⟨2700006680501202434049899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800004453667468289366599 2700006680501202434049899)
            ·
              refine ⟨4050010020751803651074849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700006680501202434049899 4050010020751803651074849)
              ·
                refine ⟨3037507515563852738306137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050010020751803651074849 3037507515563852738306137)
                ·
                  refine ⟨2278130636672889553729603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037507515563852738306137 2278130636672889553729603)
                  ·
                    refine ⟨3417195955009334330594405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2278130636672889553729603 3417195955009334330594405)
                    ·
                      refine ⟨640724241564250186986451, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3417195955009334330594405 640724241564250186986451)
                      ·
                        rfl

theorem cell23_1247806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 1, 1, 2, 2, 1, 4].length) (baseStart_1247806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247806 prefixEnd_1247806 := by exact prefixLift 1247806
  have htrace : WordTrace (prefixWord ++ tailWord_1247806) baseStart_1247806 baseEnd_1247806 := by
    simpa [prefixWord, tailWord_1247806, baseEnd_1247806] using wordTrace_append hprefix tailTrace_1247806
  have hstable : (prefixWord ++ tailWord_1247806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247806).length < 2 ^ (prefixWord ++ tailWord_1247806).sum := by decide
  have hdescent : baseEnd_1247806 < baseStart_1247806 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247809 : List Nat := [1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 3]
def baseStart_1247809 : Nat := 118140960795 + 1247809 * 2 ^ 59
def prefixEnd_1247809 : Nat := 4983230072969 + 3 ^ 40 * 1247809 * 2
def baseEnd_1247809 : Nat := 640725782006213675248937

theorem tailTrace_1247809 : CollatzResearch.WordTrace tailWord_1247809 prefixEnd_1247809 640725782006213675248937 := by
  unfold tailWord_1247809
  simp only [CollatzResearch.WordTrace]
  refine ⟨45511333136408576655850481, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30340888757605717770566987 45511333136408576655850481)
  ·
    refine ⟨34133499852306432491887861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45511333136408576655850481 34133499852306432491887861)
    ·
      refine ⟨3200015611153728046114487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34133499852306432491887861 3200015611153728046114487)
      ·
        refine ⟨4800023416730592069171731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3200015611153728046114487 4800023416730592069171731)
        ·
          refine ⟨7200035125095888103757597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800023416730592069171731 7200035125095888103757597)
          ·
            refine ⟨2700013171910958038909099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7200035125095888103757597 2700013171910958038909099)
            ·
              refine ⟨4050019757866437058363649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700013171910958038909099 4050019757866437058363649)
              ·
                refine ⟨3037514818399827793772737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050019757866437058363649 3037514818399827793772737)
                ·
                  refine ⟨2278136113799870845329553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3037514818399827793772737 2278136113799870845329553)
                  ·
                    refine ⟨1708602085349903133997165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278136113799870845329553 1708602085349903133997165)
                    ·
                      refine ⟨640725782006213675248937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708602085349903133997165 640725782006213675248937)
                      ·
                        rfl

theorem cell23_1247809_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2, 3].length) (baseStart_1247809 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247809 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247809 prefixEnd_1247809 := by exact prefixLift 1247809
  have htrace : WordTrace (prefixWord ++ tailWord_1247809) baseStart_1247809 baseEnd_1247809 := by
    simpa [prefixWord, tailWord_1247809, baseEnd_1247809] using wordTrace_append hprefix tailTrace_1247809
  have hstable : (prefixWord ++ tailWord_1247809).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247809).length < 2 ^ (prefixWord ++ tailWord_1247809).sum := by decide
  have hdescent : baseEnd_1247809 < baseStart_1247809 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247809) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247832 : List Nat := [2, 1, 2, 2, 1, 2, 2, 1, 3, 5, 2]
def baseStart_1247832 : Nat := 118140960795 + 1247832 * 2 ^ 59
def prefixEnd_1247832 : Nat := 4983230072969 + 3 ^ 40 * 1247832 * 2
def baseEnd_1247832 : Nat := 640737592061267085261331

theorem tailTrace_1247832 : CollatzResearch.WordTrace tailWord_1247832 prefixEnd_1247832 640737592061267085261331 := by
  unfold tailWord_1247832
  simp only [CollatzResearch.WordTrace]
  refine ⟨22756086007662625791968875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30341448010216834389291833 22756086007662625791968875)
  ·
    refine ⟨34134129011493938687953313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22756086007662625791968875 34134129011493938687953313)
    ·
      refine ⟨25600596758620454015964985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34134129011493938687953313 25600596758620454015964985)
      ·
        refine ⟨19200447568965340511973739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25600596758620454015964985 19200447568965340511973739)
        ·
          refine ⟨28800671353448010767960609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19200447568965340511973739 28800671353448010767960609)
          ·
            refine ⟨21600503515086008075970457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28800671353448010767960609 21600503515086008075970457)
            ·
              refine ⟨16200377636314506056977843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21600503515086008075970457 16200377636314506056977843)
              ·
                refine ⟨24300566454471759085466765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16200377636314506056977843 24300566454471759085466765)
                ·
                  refine ⟨9112712420426909657050037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24300566454471759085466765 9112712420426909657050037)
                  ·
                    refine ⟨854316789415022780348441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9112712420426909657050037 854316789415022780348441)
                    ·
                      refine ⟨640737592061267085261331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854316789415022780348441 640737592061267085261331)
                      ·
                        rfl

theorem cell23_1247832_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 2, 1, 3, 5, 2].length) (baseStart_1247832 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247832 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247832 prefixEnd_1247832 := by exact prefixLift 1247832
  have htrace : WordTrace (prefixWord ++ tailWord_1247832) baseStart_1247832 baseEnd_1247832 := by
    simpa [prefixWord, tailWord_1247832, baseEnd_1247832] using wordTrace_append hprefix tailTrace_1247832
  have hstable : (prefixWord ++ tailWord_1247832).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247832).length < 2 ^ (prefixWord ++ tailWord_1247832).sum := by decide
  have hdescent : baseEnd_1247832 < baseStart_1247832 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247832) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247855 : List Nat := [1, 1, 2, 1, 3, 2, 3, 1, 3, 6]
def baseStart_1247855 : Nat := 118140960795 + 1247855 * 2 ^ 59
def prefixEnd_1247855 : Nat := 4983230072969 + 3 ^ 40 * 1247855 * 2
def baseEnd_1247855 : Nat := 213583134038773498424575

theorem tailTrace_1247855 : CollatzResearch.WordTrace tailWord_1247855 prefixEnd_1247855 213583134038773498424575 := by
  unfold tailWord_1247855
  simp only [CollatzResearch.WordTrace]
  refine ⟨45513010894241926512025019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30342007262827951008016679 45513010894241926512025019)
  ·
    refine ⟨68269516341362889768037529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45513010894241926512025019 68269516341362889768037529)
    ·
      refine ⟨51202137256022167326028147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68269516341362889768037529 51202137256022167326028147)
      ·
        refine ⟨76803205884033250989042221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51202137256022167326028147 76803205884033250989042221)
        ·
          refine ⟨28801202206512469120890833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76803205884033250989042221 28801202206512469120890833)
          ·
            refine ⟨21600901654884351840668125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28801202206512469120890833 21600901654884351840668125)
            ·
              refine ⟨8100338120581631940250547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21600901654884351840668125 8100338120581631940250547)
              ·
                refine ⟨12150507180872447910375821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8100338120581631940250547 12150507180872447910375821)
                ·
                  refine ⟨4556440192827167966390933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12150507180872447910375821 4556440192827167966390933)
                  ·
                    refine ⟨213583134038773498424575, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4556440192827167966390933 213583134038773498424575)
                    ·
                      rfl

theorem cell23_1247855_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3, 1, 3, 6].length) (baseStart_1247855 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247855 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247855 prefixEnd_1247855 := by exact prefixLift 1247855
  have htrace : WordTrace (prefixWord ++ tailWord_1247855) baseStart_1247855 baseEnd_1247855 := by
    simpa [prefixWord, tailWord_1247855, baseEnd_1247855] using wordTrace_append hprefix tailTrace_1247855
  have hstable : (prefixWord ++ tailWord_1247855).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247855).length < 2 ^ (prefixWord ++ tailWord_1247855).sum := by decide
  have hdescent : baseEnd_1247855 < baseStart_1247855 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247855) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247875 : List Nat := [1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6]
def baseStart_1247875 : Nat := 118140960795 + 1247875 * 2 ^ 59
def prefixEnd_1247875 : Nat := 4983230072969 + 3 ^ 40 * 1247875 * 2
def baseEnd_1247875 : Nat := 640759671729410417023633

theorem tailTrace_1247875 : CollatzResearch.WordTrace tailWord_1247875 prefixEnd_1247875 640759671729410417023633 := by
  unfold tailWord_1247875
  simp only [CollatzResearch.WordTrace]
  refine ⟨45513740354169469927753079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30342493569446313285168719 45513740354169469927753079)
  ·
    refine ⟨68270610531254204891629619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45513740354169469927753079 68270610531254204891629619)
    ·
      refine ⟨102405915796881307337444429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68270610531254204891629619 102405915796881307337444429)
      ·
        refine ⟨38402218423830490251541661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102405915796881307337444429 38402218423830490251541661)
        ·
          refine ⟨14400831908936433844328123, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38402218423830490251541661 14400831908936433844328123)
          ·
            refine ⟨21601247863404650766492185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14400831908936433844328123 21601247863404650766492185)
            ·
              refine ⟨16200935897553488074869139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21601247863404650766492185 16200935897553488074869139)
              ·
                refine ⟨24301403846330232112303709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16200935897553488074869139 24301403846330232112303709)
                ·
                  refine ⟨9113026442373837042113891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24301403846330232112303709 9113026442373837042113891)
                  ·
                    refine ⟨13669539663560755563170837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9113026442373837042113891 13669539663560755563170837)
                    ·
                      refine ⟨640759671729410417023633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13669539663560755563170837 640759671729410417023633)
                      ·
                        rfl

theorem cell23_1247875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 1, 2, 1, 3, 1, 6].length) (baseStart_1247875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247875 prefixEnd_1247875 := by exact prefixLift 1247875
  have htrace : WordTrace (prefixWord ++ tailWord_1247875) baseStart_1247875 baseEnd_1247875 := by
    simpa [prefixWord, tailWord_1247875, baseEnd_1247875] using wordTrace_append hprefix tailTrace_1247875
  have hstable : (prefixWord ++ tailWord_1247875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247875).length < 2 ^ (prefixWord ++ tailWord_1247875).sum := by decide
  have hdescent : baseEnd_1247875 < baseStart_1247875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247896 : List Nat := [2, 1, 2, 4, 1, 1, 3, 2, 3, 2, 2]
def baseStart_1247896 : Nat := 118140960795 + 1247896 * 2 ^ 59
def prefixEnd_1247896 : Nat := 4983230072969 + 3 ^ 40 * 1247896 * 2
def baseEnd_1247896 : Nat := 640770454823154834861037

theorem tailTrace_1247896 : CollatzResearch.WordTrace tailWord_1247896 prefixEnd_1247896 640770454823154834861037 := by
  unfold tailWord_1247896
  simp only [CollatzResearch.WordTrace]
  refine ⟨22757253143546695257133771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30343004191395593676178361 22757253143546695257133771)
  ·
    refine ⟨34135879715320042885700657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22757253143546695257133771 34135879715320042885700657)
    ·
      refine ⟨25601909786490032164275493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34135879715320042885700657 25601909786490032164275493)
      ·
        refine ⟨4800358084966881030801655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25601909786490032164275493 4800358084966881030801655)
        ·
          refine ⟨7200537127450321546202483, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4800358084966881030801655 7200537127450321546202483)
          ·
            refine ⟨10800805691175482319303725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7200537127450321546202483 10800805691175482319303725)
            ·
              refine ⟨4050302134190805869738897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10800805691175482319303725 4050302134190805869738897)
              ·
                refine ⟨3037726600643104402304173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4050302134190805869738897 3037726600643104402304173)
                ·
                  refine ⟨1139147475241164150864065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3037726600643104402304173 1139147475241164150864065)
                  ·
                    refine ⟨854360606430873113148049, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139147475241164150864065 854360606430873113148049)
                    ·
                      refine ⟨640770454823154834861037, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854360606430873113148049 640770454823154834861037)
                      ·
                        rfl

theorem cell23_1247896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 3, 2, 3, 2, 2].length) (baseStart_1247896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247896 prefixEnd_1247896 := by exact prefixLift 1247896
  have htrace : WordTrace (prefixWord ++ tailWord_1247896) baseStart_1247896 baseEnd_1247896 := by
    simpa [prefixWord, tailWord_1247896, baseEnd_1247896] using wordTrace_append hprefix tailTrace_1247896
  have hstable : (prefixWord ++ tailWord_1247896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247896).length < 2 ^ (prefixWord ++ tailWord_1247896).sum := by decide
  have hdescent : baseEnd_1247896 < baseStart_1247896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247946 : List Nat := [3, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3]
def baseStart_1247946 : Nat := 118140960795 + 1247946 * 2 ^ 59
def prefixEnd_1247946 : Nat := 4983230072969 + 3 ^ 40 * 1247946 * 2
def baseEnd_1247946 : Nat := 640796128855879639235807

theorem tailTrace_1247946 : CollatzResearch.WordTrace tailWord_1247946 prefixEnd_1247946 640796128855879639235807 := by
  unfold tailWord_1247946
  simp only [CollatzResearch.WordTrace]
  refine ⟨11379082484228062263396923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30344219957941499369058461 11379082484228062263396923)
  ·
    refine ⟨17068623726342093395095385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11379082484228062263396923 17068623726342093395095385)
    ·
      refine ⟨12801467794756570046321539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17068623726342093395095385 12801467794756570046321539)
      ·
        refine ⟨19202201692134855069482309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12801467794756570046321539 19202201692134855069482309)
        ·
          refine ⟨3600412817275285325527933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19202201692134855069482309 3600412817275285325527933)
          ·
            refine ⟨1350154806478231997072975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3600412817275285325527933 1350154806478231997072975)
            ·
              refine ⟨2025232209717347995609463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350154806478231997072975 2025232209717347995609463)
              ·
                refine ⟨3037848314576021993414195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025232209717347995609463 3037848314576021993414195)
                ·
                  refine ⟨4556772471864032990121293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3037848314576021993414195 4556772471864032990121293)
                  ·
                    refine ⟨1708789676949012371295485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4556772471864032990121293 1708789676949012371295485)
                    ·
                      refine ⟨640796128855879639235807, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1708789676949012371295485 640796128855879639235807)
                      ·
                        rfl

theorem cell23_1247946_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 3, 1, 1, 1, 3, 3].length) (baseStart_1247946 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247946 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247946 prefixEnd_1247946 := by exact prefixLift 1247946
  have htrace : WordTrace (prefixWord ++ tailWord_1247946) baseStart_1247946 baseEnd_1247946 := by
    simpa [prefixWord, tailWord_1247946, baseEnd_1247946] using wordTrace_append hprefix tailTrace_1247946
  have hstable : (prefixWord ++ tailWord_1247946).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247946).length < 2 ^ (prefixWord ++ tailWord_1247946).sum := by decide
  have hdescent : baseEnd_1247946 < baseStart_1247946 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247946) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1247972 : List Nat := [2, 3, 1, 1, 1, 4, 1, 1, 1, 3, 5]
def baseStart_1247972 : Nat := 118140960795 + 1247972 * 2 ^ 59
def prefixEnd_1247972 : Nat := 4983230072969 + 3 ^ 40 * 1247972 * 2
def baseEnd_1247972 : Nat := 640809479352896537510687

theorem tailTrace_1247972 : CollatzResearch.WordTrace tailWord_1247972 prefixEnd_1247972 640809479352896537510687 := by
  unfold tailWord_1247972
  simp only [CollatzResearch.WordTrace]
  refine ⟨22758639117409027747017085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30344852156545370329356113 22758639117409027747017085)
  ·
    refine ⟨8534489669028385405131407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22758639117409027747017085 8534489669028385405131407)
    ·
      refine ⟨12801734503542578107697111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8534489669028385405131407 12801734503542578107697111)
      ·
        refine ⟨19202601755313867161545667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12801734503542578107697111 19202601755313867161545667)
        ·
          refine ⟨28803902632970800742318501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19202601755313867161545667 28803902632970800742318501)
          ·
            refine ⟨5400731743682025139184719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28803902632970800742318501 5400731743682025139184719)
            ·
              refine ⟨8101097615523037708777079, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5400731743682025139184719 8101097615523037708777079)
              ·
                refine ⟨12151646423284556563165619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8101097615523037708777079 12151646423284556563165619)
                ·
                  refine ⟨18227469634926834844748429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12151646423284556563165619 18227469634926834844748429)
                  ·
                    refine ⟨6835301113097563066780661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18227469634926834844748429 6835301113097563066780661)
                    ·
                      refine ⟨640809479352896537510687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6835301113097563066780661 640809479352896537510687)
                      ·
                        rfl

theorem cell23_1247972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 1, 1, 1, 3, 5].length) (baseStart_1247972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1247972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1247972 prefixEnd_1247972 := by exact prefixLift 1247972
  have htrace : WordTrace (prefixWord ++ tailWord_1247972) baseStart_1247972 baseEnd_1247972 := by
    simpa [prefixWord, tailWord_1247972, baseEnd_1247972] using wordTrace_append hprefix tailTrace_1247972
  have hstable : (prefixWord ++ tailWord_1247972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1247972).length < 2 ^ (prefixWord ++ tailWord_1247972).sum := by decide
  have hdescent : baseEnd_1247972 < baseStart_1247972 := by decide
  rcases family_descends (prefixWord ++ tailWord_1247972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248076 : List Nat := [2, 2, 1, 3, 3, 1, 3, 1, 2, 1, 4]
def baseStart_1248076 : Nat := 118140960795 + 1248076 * 2 ^ 59
def prefixEnd_1248076 : Nat := 4983230072969 + 3 ^ 40 * 1248076 * 2
def baseEnd_1248076 : Nat := 640862881340964130610209

theorem tailTrace_1248076 : CollatzResearch.WordTrace tailWord_1248076 prefixEnd_1248076 640862881340964130610209 := by
  unfold tailWord_1248076
  simp only [CollatzResearch.WordTrace]
  refine ⟨22760535713220640627910041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30347380950960854170546721 22760535713220640627910041)
  ·
    refine ⟨17070401784915480470932531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22760535713220640627910041 17070401784915480470932531)
    ·
      refine ⟨25605602677373220706398797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17070401784915480470932531 25605602677373220706398797)
      ·
        refine ⟨9602101004014957764899549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25605602677373220706398797 9602101004014957764899549)
        ·
          refine ⟨3600787876505609161837331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9602101004014957764899549 3600787876505609161837331)
          ·
            refine ⟨5401181814758413742755997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3600787876505609161837331 5401181814758413742755997)
            ·
              refine ⟨2025443180534405153533499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5401181814758413742755997 2025443180534405153533499)
              ·
                refine ⟨3038164770801607730300249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025443180534405153533499 3038164770801607730300249)
                ·
                  refine ⟨2278623578101205797725187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3038164770801607730300249 2278623578101205797725187)
                  ·
                    refine ⟨3417935367151808696587781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2278623578101205797725187 3417935367151808696587781)
                    ·
                      refine ⟨640862881340964130610209, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3417935367151808696587781 640862881340964130610209)
                      ·
                        rfl

theorem cell23_1248076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 1, 3, 1, 2, 1, 4].length) (baseStart_1248076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248076 prefixEnd_1248076 := by exact prefixLift 1248076
  have htrace : WordTrace (prefixWord ++ tailWord_1248076) baseStart_1248076 baseEnd_1248076 := by
    simpa [prefixWord, tailWord_1248076, baseEnd_1248076] using wordTrace_append hprefix tailTrace_1248076
  have hstable : (prefixWord ++ tailWord_1248076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248076).length < 2 ^ (prefixWord ++ tailWord_1248076).sum := by decide
  have hdescent : baseEnd_1248076 < baseStart_1248076 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248099 : List Nat := [1, 1, 1, 5, 3, 2, 1, 1, 8]
def baseStart_1248099 : Nat := 118140960795 + 1248099 * 2 ^ 59
def prefixEnd_1248099 : Nat := 4983230072969 + 3 ^ 40 * 1248099 * 2
def baseEnd_1248099 : Nat := 71208299044001948958067

theorem tailTrace_1248099 : CollatzResearch.WordTrace tailWord_1248099 prefixEnd_1248099 71208299044001948958067 := by
  unfold tailWord_1248099
  simp only [CollatzResearch.WordTrace]
  refine ⟨45521910305357956183907351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30347940203571970789271567 45521910305357956183907351)
  ·
    refine ⟨68282865458036934275861027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45521910305357956183907351 68282865458036934275861027)
    ·
      refine ⟨102424298187055401413791541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68282865458036934275861027 102424298187055401413791541)
      ·
        refine ⟨9602277955036443882542957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102424298187055401413791541 9602277955036443882542957)
        ·
          refine ⟨3600854233138666455953609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9602277955036443882542957 3600854233138666455953609)
          ·
            refine ⟨2700640674853999841965207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3600854233138666455953609 2700640674853999841965207)
            ·
              refine ⟨4050961012280999762947811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700640674853999841965207 4050961012280999762947811)
              ·
                refine ⟨6076441518421499644421717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4050961012280999762947811 6076441518421499644421717)
                ·
                  refine ⟨71208299044001948958067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6076441518421499644421717 71208299044001948958067)
                  ·
                    rfl

theorem cell23_1248099_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 2, 1, 1, 8].length) (baseStart_1248099 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248099 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248099 prefixEnd_1248099 := by exact prefixLift 1248099
  have htrace : WordTrace (prefixWord ++ tailWord_1248099) baseStart_1248099 baseEnd_1248099 := by
    simpa [prefixWord, tailWord_1248099, baseEnd_1248099] using wordTrace_append hprefix tailTrace_1248099
  have hstable : (prefixWord ++ tailWord_1248099).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248099).length < 2 ^ (prefixWord ++ tailWord_1248099).sum := by decide
  have hdescent : baseEnd_1248099 < baseStart_1248099 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248099) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248103 : List Nat := [1, 1, 5, 1, 2, 2, 2, 4, 1, 4]
def baseStart_1248103 : Nat := 118140960795 + 1248103 * 2 ^ 59
def prefixEnd_1248103 : Nat := 4983230072969 + 3 ^ 40 * 1248103 * 2
def baseEnd_1248103 : Nat := 213625581772878508324195

theorem tailTrace_1248103 : CollatzResearch.WordTrace tailWord_1248103 prefixEnd_1248103 213625581772878508324195 := by
  unfold tailWord_1248103
  simp only [CollatzResearch.WordTrace]
  refine ⟨45522056197343464867052963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30348037464895643244701975 45522056197343464867052963)
  ·
    refine ⟨68283084296015197300579445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45522056197343464867052963 68283084296015197300579445)
    ·
      refine ⟨6401539152751424746929323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68283084296015197300579445 6401539152751424746929323)
      ·
        refine ⟨9602308729127137120393985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6401539152751424746929323 9602308729127137120393985)
        ·
          refine ⟨7201731546845352840295489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9602308729127137120393985 7201731546845352840295489)
          ·
            refine ⟨5401298660134014630221617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7201731546845352840295489 5401298660134014630221617)
            ·
              refine ⟨4050973995100510972666213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5401298660134014630221617 4050973995100510972666213)
              ·
                refine ⟨759557624081345807374915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4050973995100510972666213 759557624081345807374915)
                ·
                  refine ⟨1139336436122018711062373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759557624081345807374915 1139336436122018711062373)
                  ·
                    refine ⟨213625581772878508324195, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139336436122018711062373 213625581772878508324195)
                    ·
                      rfl

theorem cell23_1248103_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 4, 1, 4].length) (baseStart_1248103 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248103 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248103 prefixEnd_1248103 := by exact prefixLift 1248103
  have htrace : WordTrace (prefixWord ++ tailWord_1248103) baseStart_1248103 baseEnd_1248103 := by
    simpa [prefixWord, tailWord_1248103, baseEnd_1248103] using wordTrace_append hprefix tailTrace_1248103
  have hstable : (prefixWord ++ tailWord_1248103).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248103).length < 2 ^ (prefixWord ++ tailWord_1248103).sum := by decide
  have hdescent : baseEnd_1248103 < baseStart_1248103 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248103) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248169 : List Nat := [1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 5]
def baseStart_1248169 : Nat := 118140960795 + 1248169 * 2 ^ 59
def prefixEnd_1248169 : Nat := 4983230072969 + 3 ^ 40 * 1248169 * 2
def baseEnd_1248169 : Nat := 640910635041832266747281

theorem tailTrace_1248169 : CollatzResearch.WordTrace tailWord_1248169 prefixEnd_1248169 640910635041832266747281 := by
  unfold tailWord_1248169
  simp only [CollatzResearch.WordTrace]
  refine ⟨45524463415104358138955561, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30349642276736238759303707 45524463415104358138955561)
  ·
    refine ⟨34143347561328268604216671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45524463415104358138955561 34143347561328268604216671)
    ·
      refine ⟨51215021341992402906325007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34143347561328268604216671 51215021341992402906325007)
      ·
        refine ⟨76822532012988604359487511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51215021341992402906325007 76822532012988604359487511)
        ·
          refine ⟨115233798019482906539231267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76822532012988604359487511 115233798019482906539231267)
          ·
            refine ⟨172850697029224359808846901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115233798019482906539231267 172850697029224359808846901)
            ·
              refine ⟨16204752846489783732079397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 172850697029224359808846901 16204752846489783732079397)
              ·
                refine ⟨3038391158716834449764887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16204752846489783732079397 3038391158716834449764887)
                ·
                  refine ⟨4557586738075251674647331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038391158716834449764887 4557586738075251674647331)
                  ·
                    refine ⟨6836380107112877511970997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4557586738075251674647331 6836380107112877511970997)
                    ·
                      refine ⟨640910635041832266747281, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6836380107112877511970997 640910635041832266747281)
                      ·
                        rfl

theorem cell23_1248169_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 5, 4, 1, 1, 5].length) (baseStart_1248169 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248169 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248169 prefixEnd_1248169 := by exact prefixLift 1248169
  have htrace : WordTrace (prefixWord ++ tailWord_1248169) baseStart_1248169 baseEnd_1248169 := by
    simpa [prefixWord, tailWord_1248169, baseEnd_1248169] using wordTrace_append hprefix tailTrace_1248169
  have hstable : (prefixWord ++ tailWord_1248169).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248169).length < 2 ^ (prefixWord ++ tailWord_1248169).sum := by decide
  have hdescent : baseEnd_1248169 < baseStart_1248169 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248169) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248180 : List Nat := [2, 5, 2, 1, 1, 1, 3, 2, 1, 5]
def baseStart_1248180 : Nat := 118140960795 + 1248180 * 2 ^ 59
def prefixEnd_1248180 : Nat := 4983230072969 + 3 ^ 40 * 1248180 * 2
def baseEnd_1248180 : Nat := 213638761109677241236577

theorem tailTrace_1248180 : CollatzResearch.WordTrace tailWord_1248180 prefixEnd_1248180 213638761109677241236577 := by
  unfold tailWord_1248180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22762432309032253508802997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30349909745376338011737329 22762432309032253508802997)
  ·
    refine ⟨2133978028971773766450281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22762432309032253508802997 2133978028971773766450281)
    ·
      refine ⟨1600483521728830324837711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2133978028971773766450281 1600483521728830324837711)
      ·
        refine ⟨2400725282593245487256567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1600483521728830324837711 2400725282593245487256567)
        ·
          refine ⟨3601087923889868230884851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400725282593245487256567 3601087923889868230884851)
          ·
            refine ⟨5401631885834802346327277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601087923889868230884851 5401631885834802346327277)
            ·
              refine ⟨2025611957188050879872729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5401631885834802346327277 2025611957188050879872729)
              ·
                refine ⟨1519208967891038159904547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025611957188050879872729 1519208967891038159904547)
                ·
                  refine ⟨2278813451836557239856821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519208967891038159904547 2278813451836557239856821)
                  ·
                    refine ⟨213638761109677241236577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2278813451836557239856821 213638761109677241236577)
                    ·
                      rfl

theorem cell23_1248180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 1, 1, 3, 2, 1, 5].length) (baseStart_1248180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248180 prefixEnd_1248180 := by exact prefixLift 1248180
  have htrace : WordTrace (prefixWord ++ tailWord_1248180) baseStart_1248180 baseEnd_1248180 := by
    simpa [prefixWord, tailWord_1248180, baseEnd_1248180] using wordTrace_append hprefix tailTrace_1248180
  have hstable : (prefixWord ++ tailWord_1248180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248180).length < 2 ^ (prefixWord ++ tailWord_1248180).sum := by decide
  have hdescent : baseEnd_1248180 < baseStart_1248180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248183 : List Nat := [1, 1, 3, 1, 3, 1, 2, 4, 3, 2, 2]
def baseStart_1248183 : Nat := 118140960795 + 1248183 * 2 ^ 59
def prefixEnd_1248183 : Nat := 4983230072969 + 3 ^ 40 * 1248183 * 2
def baseEnd_1248183 : Nat := 640917823770995211972217

theorem tailTrace_1248183 : CollatzResearch.WordTrace tailWord_1248183 prefixEnd_1248183 640917823770995211972217 := by
  unfold tailWord_1248183
  simp only [CollatzResearch.WordTrace]
  refine ⟨45524974037053638529965203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30349982691369092353310135 45524974037053638529965203)
  ·
    refine ⟨68287461055580457794947805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45524974037053638529965203 68287461055580457794947805)
    ·
      refine ⟨25607797895842671673105427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68287461055580457794947805 25607797895842671673105427)
      ·
        refine ⟨38411696843764007509658141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25607797895842671673105427 38411696843764007509658141)
        ·
          refine ⟨14404386316411502816121803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38411696843764007509658141 14404386316411502816121803)
          ·
            refine ⟨21606579474617254224182705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14404386316411502816121803 21606579474617254224182705)
            ·
              refine ⟨16204934605962940668137029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21606579474617254224182705 16204934605962940668137029)
              ·
                refine ⟨3038425238618051375275693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16204934605962940668137029 3038425238618051375275693)
                ·
                  refine ⟨1139409464481769265728385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3038425238618051375275693 1139409464481769265728385)
                  ·
                    refine ⟨854557098361326949296289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139409464481769265728385 854557098361326949296289)
                    ·
                      refine ⟨640917823770995211972217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854557098361326949296289 640917823770995211972217)
                      ·
                        rfl

theorem cell23_1248183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 2, 4, 3, 2, 2].length) (baseStart_1248183 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248183 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248183 prefixEnd_1248183 := by exact prefixLift 1248183
  have htrace : WordTrace (prefixWord ++ tailWord_1248183) baseStart_1248183 baseEnd_1248183 := by
    simpa [prefixWord, tailWord_1248183, baseEnd_1248183] using wordTrace_append hprefix tailTrace_1248183
  have hstable : (prefixWord ++ tailWord_1248183).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248183).length < 2 ^ (prefixWord ++ tailWord_1248183).sum := by decide
  have hdescent : baseEnd_1248183 < baseStart_1248183 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248186 : List Nat := [3, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3]
def baseStart_1248186 : Nat := 118140960795 + 1248186 * 2 ^ 59
def prefixEnd_1248186 : Nat := 4983230072969 + 3 ^ 40 * 1248186 * 2
def baseEnd_1248186 : Nat := 640919364212958700234703

theorem tailTrace_1248186 : CollatzResearch.WordTrace tailWord_1248186 prefixEnd_1248186 640919364212958700234703 := by
  unfold tailWord_1248186
  simp only [CollatzResearch.WordTrace]
  refine ⟨11381270864010692510581103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30350055637361846694882941 11381270864010692510581103)
  ·
    refine ⟨17071906296016038765871655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11381270864010692510581103 17071906296016038765871655)
    ·
      refine ⟨25607859444024058148807483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17071906296016038765871655 25607859444024058148807483)
      ·
        refine ⟨38411789166036087223211225, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25607859444024058148807483 38411789166036087223211225)
        ·
          refine ⟨28808841874527065417408419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38411789166036087223211225 28808841874527065417408419)
          ·
            refine ⟨43213262811790598126112629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28808841874527065417408419 43213262811790598126112629)
            ·
              refine ⟨4051243388605368574323059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43213262811790598126112629 4051243388605368574323059)
              ·
                refine ⟨6076865082908052861484589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4051243388605368574323059 6076865082908052861484589)
                ·
                  refine ⟨2278824406090519823056721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6076865082908052861484589 2278824406090519823056721)
                  ·
                    refine ⟨1709118304567889867292541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278824406090519823056721 1709118304567889867292541)
                    ·
                      refine ⟨640919364212958700234703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1709118304567889867292541 640919364212958700234703)
                      ·
                        rfl

theorem cell23_1248186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 5, 1, 3, 2, 3].length) (baseStart_1248186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248186 prefixEnd_1248186 := by exact prefixLift 1248186
  have htrace : WordTrace (prefixWord ++ tailWord_1248186) baseStart_1248186 baseEnd_1248186 := by
    simpa [prefixWord, tailWord_1248186, baseEnd_1248186] using wordTrace_append hprefix tailTrace_1248186
  have hstable : (prefixWord ++ tailWord_1248186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248186).length < 2 ^ (prefixWord ++ tailWord_1248186).sum := by decide
  have hdescent : baseEnd_1248186 < baseStart_1248186 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248200 : List Nat := [2, 1, 3, 1, 5, 1, 3, 1, 1, 1, 4]
def baseStart_1248200 : Nat := 118140960795 + 1248200 * 2 ^ 59
def prefixEnd_1248200 : Nat := 4983230072969 + 3 ^ 40 * 1248200 * 2
def baseEnd_1248200 : Nat := 640926552942121645459639

theorem tailTrace_1248200 : CollatzResearch.WordTrace tailWord_1248200 prefixEnd_1248200 640926552942121645459639 := by
  unfold tailWord_1248200
  simp only [CollatzResearch.WordTrace]
  refine ⟨22762797038996025216667027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30350396051994700288889369 22762797038996025216667027)
  ·
    refine ⟨34144195558494037825000541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22762797038996025216667027 34144195558494037825000541)
    ·
      refine ⟨12804073334435264184375203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34144195558494037825000541 12804073334435264184375203)
      ·
        refine ⟨19206110001652896276562805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12804073334435264184375203 19206110001652896276562805)
        ·
          refine ⟨1800572812654959025927763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19206110001652896276562805 1800572812654959025927763)
          ·
            refine ⟨2700859218982438538891645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1800572812654959025927763 2700859218982438538891645)
            ·
              refine ⟨1012822207118414452084367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2700859218982438538891645 1012822207118414452084367)
              ·
                refine ⟨1519233310677621678126551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012822207118414452084367 1519233310677621678126551)
                ·
                  refine ⟨2278849966016432517189827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519233310677621678126551 2278849966016432517189827)
                  ·
                    refine ⟨3418274949024648775784741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2278849966016432517189827 3418274949024648775784741)
                    ·
                      refine ⟨640926552942121645459639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3418274949024648775784741 640926552942121645459639)
                      ·
                        rfl

theorem cell23_1248200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 1, 3, 1, 1, 1, 4].length) (baseStart_1248200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248200 prefixEnd_1248200 := by exact prefixLift 1248200
  have htrace : WordTrace (prefixWord ++ tailWord_1248200) baseStart_1248200 baseEnd_1248200 := by
    simpa [prefixWord, tailWord_1248200, baseEnd_1248200] using wordTrace_append hprefix tailTrace_1248200
  have hstable : (prefixWord ++ tailWord_1248200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248200).length < 2 ^ (prefixWord ++ tailWord_1248200).sum := by decide
  have hdescent : baseEnd_1248200 < baseStart_1248200 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248210 : List Nat := [3, 2, 2, 3, 1, 2, 2, 2, 2, 4]
def baseStart_1248210 : Nat := 118140960795 + 1248210 * 2 ^ 59
def prefixEnd_1248210 : Nat := 4983230072969 + 3 ^ 40 * 1248210 * 2
def baseEnd_1248210 : Nat := 213643895916222202111531

theorem tailTrace_1248210 : CollatzResearch.WordTrace tailWord_1248210 prefixEnd_1248210 213643895916222202111531 := by
  unfold tailWord_1248210
  simp only [CollatzResearch.WordTrace]
  refine ⟨11381489701988955535299521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30350639205303881427465389 11381489701988955535299521)
  ·
    refine ⟨8536117276491716651474641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11381489701988955535299521 8536117276491716651474641)
    ·
      refine ⟨6402087957368787488605981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8536117276491716651474641 6402087957368787488605981)
      ·
        refine ⟨2400782984013295308227243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6402087957368787488605981 2400782984013295308227243)
        ·
          refine ⟨3601174476019942962340865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2400782984013295308227243 3601174476019942962340865)
          ·
            refine ⟨2700880857014957221755649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3601174476019942962340865 2700880857014957221755649)
            ·
              refine ⟨2025660642761217916316737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2700880857014957221755649 2025660642761217916316737)
              ·
                refine ⟨1519245482070913437237553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2025660642761217916316737 1519245482070913437237553)
                ·
                  refine ⟨1139434111553185077928165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1519245482070913437237553 1139434111553185077928165)
                  ·
                    refine ⟨213643895916222202111531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139434111553185077928165 213643895916222202111531)
                    ·
                      rfl

theorem cell23_1248210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 2, 2, 2, 2, 4].length) (baseStart_1248210 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248210 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248210 prefixEnd_1248210 := by exact prefixLift 1248210
  have htrace : WordTrace (prefixWord ++ tailWord_1248210) baseStart_1248210 baseEnd_1248210 := by
    simpa [prefixWord, tailWord_1248210, baseEnd_1248210] using wordTrace_append hprefix tailTrace_1248210
  have hstable : (prefixWord ++ tailWord_1248210).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248210).length < 2 ^ (prefixWord ++ tailWord_1248210).sum := by decide
  have hdescent : baseEnd_1248210 < baseStart_1248210 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248217 : List Nat := [1, 2, 1, 2, 5, 2, 1, 4, 1, 2, 2]
def baseStart_1248217 : Nat := 118140960795 + 1248217 * 2 ^ 59
def prefixEnd_1248217 : Nat := 4983230072969 + 3 ^ 40 * 1248217 * 2
def baseEnd_1248217 : Nat := 640935282113248078947061

theorem tailTrace_1248217 : CollatzResearch.WordTrace tailWord_1248217 prefixEnd_1248217 640935282113248078947061 := by
  unfold tailWord_1248217
  simp only [CollatzResearch.WordTrace]
  refine ⟨45526214118930462336702905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30350809412620308224468603 45526214118930462336702905)
  ·
    refine ⟨34144660589197846752527179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45526214118930462336702905 34144660589197846752527179)
    ·
      refine ⟨51216990883796770128790769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34144660589197846752527179 51216990883796770128790769)
      ·
        refine ⟨38412743162847577596593077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51216990883796770128790769 38412743162847577596593077)
        ·
          refine ⟨3601194671516960399680601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 38412743162847577596593077 3601194671516960399680601)
          ·
            refine ⟨2700896003637720299760451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3601194671516960399680601 2700896003637720299760451)
            ·
              refine ⟨4051344005456580449640677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2700896003637720299760451 4051344005456580449640677)
              ·
                refine ⟨759627001023108834307627, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4051344005456580449640677 759627001023108834307627)
                ·
                  refine ⟨1139440501534663251461441, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759627001023108834307627 1139440501534663251461441)
                  ·
                    refine ⟨854580376150997438596081, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139440501534663251461441 854580376150997438596081)
                    ·
                      refine ⟨640935282113248078947061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854580376150997438596081 640935282113248078947061)
                      ·
                        rfl

theorem cell23_1248217_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 5, 2, 1, 4, 1, 2, 2].length) (baseStart_1248217 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248217 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248217 prefixEnd_1248217 := by exact prefixLift 1248217
  have htrace : WordTrace (prefixWord ++ tailWord_1248217) baseStart_1248217 baseEnd_1248217 := by
    simpa [prefixWord, tailWord_1248217, baseEnd_1248217] using wordTrace_append hprefix tailTrace_1248217
  have hstable : (prefixWord ++ tailWord_1248217).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248217).length < 2 ^ (prefixWord ++ tailWord_1248217).sum := by decide
  have hdescent : baseEnd_1248217 < baseStart_1248217 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248217) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248223 : List Nat := [1, 1, 2, 3, 6, 1, 1, 8]
def baseStart_1248223 : Nat := 118140960795 + 1248223 * 2 ^ 59
def prefixEnd_1248223 : Nat := 4983230072969 + 3 ^ 40 * 1248223 * 2
def baseEnd_1248223 : Nat := 23738457888784261313779

theorem tailTrace_1248223 : CollatzResearch.WordTrace tailWord_1248223 prefixEnd_1248223 23738457888784261313779 := by
  unfold tailWord_1248223
  simp only [CollatzResearch.WordTrace]
  refine ⟨45526432956908725361421323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30350955304605816907614215 45526432956908725361421323)
  ·
    refine ⟨68289649435363088042131985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45526432956908725361421323 68289649435363088042131985)
    ·
      refine ⟨51217237076522316031598989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68289649435363088042131985 51217237076522316031598989)
      ·
        refine ⟨19206463903695868511849621, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51217237076522316031598989 19206463903695868511849621)
        ·
          refine ⟨900302995485743836492951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19206463903695868511849621 900302995485743836492951)
          ·
            refine ⟨1350454493228615754739427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900302995485743836492951 1350454493228615754739427)
            ·
              refine ⟨2025681739842923632109141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350454493228615754739427 2025681739842923632109141)
              ·
                refine ⟨23738457888784261313779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2025681739842923632109141 23738457888784261313779)
                ·
                  rfl

theorem cell23_1248223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 6, 1, 1, 8].length) (baseStart_1248223 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248223 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248223 prefixEnd_1248223 := by exact prefixLift 1248223
  have htrace : WordTrace (prefixWord ++ tailWord_1248223) baseStart_1248223 baseEnd_1248223 := by
    simpa [prefixWord, tailWord_1248223, baseEnd_1248223] using wordTrace_append hprefix tailTrace_1248223
  have hstable : (prefixWord ++ tailWord_1248223).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248223).length < 2 ^ (prefixWord ++ tailWord_1248223).sum := by decide
  have hdescent : baseEnd_1248223 < baseStart_1248223 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248249 : List Nat := [1, 2, 1, 3, 1, 3, 1, 2, 1, 8]
def baseStart_1248249 : Nat := 118140960795 + 1248249 * 2 ^ 59
def prefixEnd_1248249 : Nat := 4983230072969 + 3 ^ 40 * 1248249 * 2
def baseEnd_1248249 : Nat := 213650571164730651248971

theorem tailTrace_1248249 : CollatzResearch.WordTrace tailWord_1248249 prefixEnd_1248249 213650571164730651248971 := by
  unfold tailWord_1248249
  simp only [CollatzResearch.WordTrace]
  refine ⟨45527381254814531801867801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30351587503209687867911867 45527381254814531801867801)
  ·
    refine ⟨34145535941110898851400851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45527381254814531801867801 34145535941110898851400851)
    ·
      refine ⟨51218303911666348277101277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34145535941110898851400851 51218303911666348277101277)
      ·
        refine ⟨19206863966874880603912979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51218303911666348277101277 19206863966874880603912979)
        ·
          refine ⟨28810295950312320905869469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19206863966874880603912979 28810295950312320905869469)
          ·
            refine ⟨10803860981367120339701051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28810295950312320905869469 10803860981367120339701051)
            ·
              refine ⟨16205791472050680509551577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10803860981367120339701051 16205791472050680509551577)
              ·
                refine ⟨12154343604038010382163683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16205791472050680509551577 12154343604038010382163683)
                ·
                  refine ⟨18231515406057015573245525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12154343604038010382163683 18231515406057015573245525)
                  ·
                    refine ⟨213650571164730651248971, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18231515406057015573245525 213650571164730651248971)
                    ·
                      rfl

theorem cell23_1248249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 1, 2, 1, 8].length) (baseStart_1248249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248249 prefixEnd_1248249 := by exact prefixLift 1248249
  have htrace : WordTrace (prefixWord ++ tailWord_1248249) baseStart_1248249 baseEnd_1248249 := by
    simpa [prefixWord, tailWord_1248249, baseEnd_1248249] using wordTrace_append hprefix tailTrace_1248249
  have hstable : (prefixWord ++ tailWord_1248249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248249).length < 2 ^ (prefixWord ++ tailWord_1248249).sum := by decide
  have hdescent : baseEnd_1248249 < baseStart_1248249 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248254 : List Nat := [4, 2, 2, 2, 2, 2, 2, 1, 1, 2, 3]
def baseStart_1248254 : Nat := 118140960795 + 1248254 * 2 ^ 59
def prefixEnd_1248254 : Nat := 4983230072969 + 3 ^ 40 * 1248254 * 2
def baseEnd_1248254 : Nat := 640954280897464434184391

theorem tailTrace_1248254 : CollatzResearch.WordTrace tailWord_1248254 prefixEnd_1248254 640954280897464434184391 := by
  unfold tailWord_1248254
  simp only [CollatzResearch.WordTrace]
  refine ⟨5690945452474552206974977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30351709079864278437199877 5690945452474552206974977)
  ·
    refine ⟨4268209089355914155231233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5690945452474552206974977 4268209089355914155231233)
    ·
      refine ⟨3201156817016935616423425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4268209089355914155231233 3201156817016935616423425)
      ·
        refine ⟨2400867612762701712317569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3201156817016935616423425 2400867612762701712317569)
        ·
          refine ⟨1800650709572026284238177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2400867612762701712317569 1800650709572026284238177)
          ·
            refine ⟨1350488032179019713178633, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1800650709572026284238177 1350488032179019713178633)
            ·
              refine ⟨1012866024134264784883975, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1350488032179019713178633 1012866024134264784883975)
              ·
                refine ⟨1519299036201397177325963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1012866024134264784883975 1519299036201397177325963)
                ·
                  refine ⟨2278948554302095765988945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1519299036201397177325963 2278948554302095765988945)
                  ·
                    refine ⟨1709211415726571824491709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2278948554302095765988945 1709211415726571824491709)
                    ·
                      refine ⟨640954280897464434184391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1709211415726571824491709 640954280897464434184391)
                      ·
                        rfl

theorem cell23_1248254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 2, 2, 1, 1, 2, 3].length) (baseStart_1248254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248254 prefixEnd_1248254 := by exact prefixLift 1248254
  have htrace : WordTrace (prefixWord ++ tailWord_1248254) baseStart_1248254 baseEnd_1248254 := by
    simpa [prefixWord, tailWord_1248254, baseEnd_1248254] using wordTrace_append hprefix tailTrace_1248254
  have hstable : (prefixWord ++ tailWord_1248254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248254).length < 2 ^ (prefixWord ++ tailWord_1248254).sum := by decide
  have hdescent : baseEnd_1248254 < baseStart_1248254 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248256 : List Nat := [2, 1, 1, 2, 1, 1, 1, 2, 2, 8, 2]
def baseStart_1248256 : Nat := 118140960795 + 1248256 * 2 ^ 59
def prefixEnd_1248256 : Nat := 4983230072969 + 3 ^ 40 * 1248256 * 2
def baseEnd_1248256 : Nat := 640955307858773426359381

theorem tailTrace_1248256 : CollatzResearch.WordTrace tailWord_1248256 prefixEnd_1248256 640955307858773426359381 := by
  unfold tailWord_1248256
  simp only [CollatzResearch.WordTrace]
  refine ⟨22763818282894585998686311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30351757710526114664915081 22763818282894585998686311)
  ·
    refine ⟨34145727424341878998029467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22763818282894585998686311 34145727424341878998029467)
    ·
      refine ⟨51218591136512818497044201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34145727424341878998029467 51218591136512818497044201)
      ·
        refine ⟨38413943352384613872783151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51218591136512818497044201 38413943352384613872783151)
        ·
          refine ⟨57620915028576920809174727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38413943352384613872783151 57620915028576920809174727)
          ·
            refine ⟨86431372542865381213762091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57620915028576920809174727 86431372542865381213762091)
            ·
              refine ⟨129647058814298071820643137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 86431372542865381213762091 129647058814298071820643137)
              ·
                refine ⟨97235294110723553865482353, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 129647058814298071820643137 97235294110723553865482353)
                ·
                  refine ⟨72926470583042665399111765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 97235294110723553865482353 72926470583042665399111765)
                  ·
                    refine ⟨854607077145031235145841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 72926470583042665399111765 854607077145031235145841)
                    ·
                      refine ⟨640955307858773426359381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854607077145031235145841 640955307858773426359381)
                      ·
                        rfl

theorem cell23_1248256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 8, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 1, 2, 2, 8, 2].length) (baseStart_1248256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248256 prefixEnd_1248256 := by exact prefixLift 1248256
  have htrace : WordTrace (prefixWord ++ tailWord_1248256) baseStart_1248256 baseEnd_1248256 := by
    simpa [prefixWord, tailWord_1248256, baseEnd_1248256] using wordTrace_append hprefix tailTrace_1248256
  have hstable : (prefixWord ++ tailWord_1248256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248256).length < 2 ^ (prefixWord ++ tailWord_1248256).sum := by decide
  have hdescent : baseEnd_1248256 < baseStart_1248256 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248266 : List Nat := [3, 1, 2, 2, 3, 1, 1, 2, 2, 6]
def baseStart_1248266 : Nat := 118140960795 + 1248266 * 2 ^ 59
def prefixEnd_1248266 : Nat := 4983230072969 + 3 ^ 40 * 1248266 * 2
def baseEnd_1248266 : Nat := 213653480888439462411445

theorem tailTrace_1248266 : CollatzResearch.WordTrace tailWord_1248266 prefixEnd_1248266 213653480888439462411445 := by
  unfold tailWord_1248266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11382000323938235926309163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30352000863835295803491101 11382000323938235926309163)
  ·
    refine ⟨17073000485907353889463745, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11382000323938235926309163 17073000485907353889463745)
    ·
      refine ⟨12804750364430515417097809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17073000485907353889463745 12804750364430515417097809)
      ·
        refine ⟨9603562773322886562823357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12804750364430515417097809 9603562773322886562823357)
        ·
          refine ⟨3601336039996082461058759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9603562773322886562823357 3601336039996082461058759)
          ·
            refine ⟨5402004059994123691588139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601336039996082461058759 5402004059994123691588139)
            ·
              refine ⟨8103006089991185537382209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5402004059994123691588139 8103006089991185537382209)
              ·
                refine ⟨6077254567493389153036657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8103006089991185537382209 6077254567493389153036657)
                ·
                  refine ⟨4557940925620041864777493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6077254567493389153036657 4557940925620041864777493)
                  ·
                    refine ⟨213653480888439462411445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4557940925620041864777493 213653480888439462411445)
                    ·
                      rfl

theorem cell23_1248266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 1, 1, 2, 2, 6].length) (baseStart_1248266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248266 prefixEnd_1248266 := by exact prefixLift 1248266
  have htrace : WordTrace (prefixWord ++ tailWord_1248266) baseStart_1248266 baseEnd_1248266 := by
    simpa [prefixWord, tailWord_1248266, baseEnd_1248266] using wordTrace_append hprefix tailTrace_1248266
  have hstable : (prefixWord ++ tailWord_1248266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248266).length < 2 ^ (prefixWord ++ tailWord_1248266).sum := by decide
  have hdescent : baseEnd_1248266 < baseStart_1248266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248290 : List Nat := [3, 3, 1, 1, 1, 3, 3, 1, 1, 4, 2]
def baseStart_1248290 : Nat := 118140960795 + 1248290 * 2 ^ 59
def prefixEnd_1248290 : Nat := 4983230072969 + 3 ^ 40 * 1248290 * 2
def baseEnd_1248290 : Nat := 640972766201026293334225

theorem tailTrace_1248290 : CollatzResearch.WordTrace tailWord_1248290 prefixEnd_1248290 640972766201026293334225 := by
  unfold tailWord_1248290
  simp only [CollatzResearch.WordTrace]
  refine ⟨11382219161916498951027581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30352584431777330536073549 11382219161916498951027581)
  ·
    refine ⟨4268332185718687106635343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11382219161916498951027581 4268332185718687106635343)
    ·
      refine ⟨6402498278578030659953015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4268332185718687106635343 6402498278578030659953015)
      ·
        refine ⟨9603747417867045989929523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6402498278578030659953015 9603747417867045989929523)
        ·
          refine ⟨14405621126800568984894285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9603747417867045989929523 14405621126800568984894285)
          ·
            refine ⟨5402107922550213369335357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14405621126800568984894285 5402107922550213369335357)
            ·
              refine ⟨2025790470956330013500759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5402107922550213369335357 2025790470956330013500759)
              ·
                refine ⟨3038685706434495020251139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2025790470956330013500759 3038685706434495020251139)
                ·
                  refine ⟨4558028559651742530376709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3038685706434495020251139 4558028559651742530376709)
                  ·
                    refine ⟨854630354934701724445633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4558028559651742530376709 854630354934701724445633)
                    ·
                      refine ⟨640972766201026293334225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854630354934701724445633 640972766201026293334225)
                      ·
                        rfl

theorem cell23_1248290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 3, 3, 1, 1, 4, 2].length) (baseStart_1248290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248290 prefixEnd_1248290 := by exact prefixLift 1248290
  have htrace : WordTrace (prefixWord ++ tailWord_1248290) baseStart_1248290 baseEnd_1248290 := by
    simpa [prefixWord, tailWord_1248290, baseEnd_1248290] using wordTrace_append hprefix tailTrace_1248290
  have hstable : (prefixWord ++ tailWord_1248290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248290).length < 2 ^ (prefixWord ++ tailWord_1248290).sum := by decide
  have hdescent : baseEnd_1248290 < baseStart_1248290 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248346 : List Nat := [3, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1248346 : Nat := 118140960795 + 1248346 * 2 ^ 59
def prefixEnd_1248346 : Nat := 4983230072969 + 3 ^ 40 * 1248346 * 2
def baseEnd_1248346 : Nat := 641001521117678074233967

theorem tailTrace_1248346 : CollatzResearch.WordTrace tailWord_1248346 prefixEnd_1248346 641001521117678074233967 := by
  unfold tailWord_1248346
  simp only [CollatzResearch.WordTrace]
  refine ⟨11382729783865779342037223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30353946090308744912099261 11382729783865779342037223)
  ·
    refine ⟨17074094675798669013055835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11382729783865779342037223 17074094675798669013055835)
    ·
      refine ⟨25611142013698003519583753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17074094675798669013055835 25611142013698003519583753)
      ·
        refine ⟨19208356510273502639687815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25611142013698003519583753 19208356510273502639687815)
        ·
          refine ⟨28812534765410253959531723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19208356510273502639687815 28812534765410253959531723)
          ·
            refine ⟨43218802148115380939297585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28812534765410253959531723 43218802148115380939297585)
            ·
              refine ⟨32414101611086535704473189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43218802148115380939297585 32414101611086535704473189)
              ·
                refine ⟨6077644052078725444588723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32414101611086535704473189 6077644052078725444588723)
                ·
                  refine ⟨9116466078118088166883085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6077644052078725444588723 9116466078118088166883085)
                  ·
                    refine ⟨3418674779294283062581157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9116466078118088166883085 3418674779294283062581157)
                    ·
                      refine ⟨641001521117678074233967, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3418674779294283062581157 641001521117678074233967)
                      ·
                        rfl

theorem cell23_1248346_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1248346 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248346 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248346 prefixEnd_1248346 := by exact prefixLift 1248346
  have htrace : WordTrace (prefixWord ++ tailWord_1248346) baseStart_1248346 baseEnd_1248346 := by
    simpa [prefixWord, tailWord_1248346, baseEnd_1248346] using wordTrace_append hprefix tailTrace_1248346
  have hstable : (prefixWord ++ tailWord_1248346).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248346).length < 2 ^ (prefixWord ++ tailWord_1248346).sum := by decide
  have hdescent : baseEnd_1248346 < baseStart_1248346 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248346) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248447 : List Nat := [1, 1, 2, 2, 2, 2, 4, 4, 1, 1, 3]
def baseStart_1248447 : Nat := 118140960795 + 1248447 * 2 ^ 59
def prefixEnd_1248447 : Nat := 4983230072969 + 3 ^ 40 * 1248447 * 2
def baseEnd_1248447 : Nat := 641053382663782179071003

theorem tailTrace_1248447 : CollatzResearch.WordTrace tailWord_1248447 prefixEnd_1248447 641053382663782179071003 := by
  unfold tailWord_1248447
  simp only [CollatzResearch.WordTrace]
  refine ⟨45534602908097211617575595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30356401938731474411717063 45534602908097211617575595)
  ·
    refine ⟨68301904362145817426363393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45534602908097211617575595 68301904362145817426363393)
    ·
      refine ⟨51226428271609363069772545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68301904362145817426363393 51226428271609363069772545)
      ·
        refine ⟨38419821203707022302329409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51226428271609363069772545 38419821203707022302329409)
        ·
          refine ⟨28814865902780266726747057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38419821203707022302329409 28814865902780266726747057)
          ·
            refine ⟨21611149427085200045060293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28814865902780266726747057 21611149427085200045060293)
            ·
              refine ⟨4052090517578475008448805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21611149427085200045060293 4052090517578475008448805)
              ·
                refine ⟨759766972045964064084151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4052090517578475008448805 759766972045964064084151)
                ·
                  refine ⟨1139650458068946096126227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759766972045964064084151 1139650458068946096126227)
                  ·
                    refine ⟨1709475687103419144189341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1139650458068946096126227 1709475687103419144189341)
                    ·
                      refine ⟨641053382663782179071003, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1709475687103419144189341 641053382663782179071003)
                      ·
                        rfl

theorem cell23_1248447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 4, 1, 1, 3].length) (baseStart_1248447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248447 prefixEnd_1248447 := by exact prefixLift 1248447
  have htrace : WordTrace (prefixWord ++ tailWord_1248447) baseStart_1248447 baseEnd_1248447 := by
    simpa [prefixWord, tailWord_1248447, baseEnd_1248447] using wordTrace_append hprefix tailTrace_1248447
  have hstable : (prefixWord ++ tailWord_1248447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248447).length < 2 ^ (prefixWord ++ tailWord_1248447).sum := by decide
  have hdescent : baseEnd_1248447 < baseStart_1248447 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248490 : List Nat := [3, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5]
def baseStart_1248490 : Nat := 118140960795 + 1248490 * 2 ^ 59
def prefixEnd_1248490 : Nat := 4983230072969 + 3 ^ 40 * 1248490 * 2
def baseEnd_1248490 : Nat := 641075462331925510833305

theorem tailTrace_1248490 : CollatzResearch.WordTrace tailWord_1248490 prefixEnd_1248490 641075462331925510833305 := by
  unfold tailWord_1248490
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384042811735357490347731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30357447497960953307593949 11384042811735357490347731)
  ·
    refine ⟨17076064217603036235521597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11384042811735357490347731 17076064217603036235521597)
    ·
      refine ⟨6403524081601138588320599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17076064217603036235521597 6403524081601138588320599)
      ·
        refine ⟨9605286122401707882480899, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6403524081601138588320599 9605286122401707882480899)
        ·
          refine ⟨14407929183602561823721349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9605286122401707882480899 14407929183602561823721349)
          ·
            refine ⟨2701486721925480341947753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14407929183602561823721349 2701486721925480341947753)
            ·
              refine ⟨2026115041444110256460815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701486721925480341947753 2026115041444110256460815)
              ·
                refine ⟨3039172562166165384691223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2026115041444110256460815 3039172562166165384691223)
                ·
                  refine ⟨4558758843249248077036835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3039172562166165384691223 4558758843249248077036835)
                  ·
                    refine ⟨6838138264873872115555253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4558758843249248077036835 6838138264873872115555253)
                    ·
                      refine ⟨641075462331925510833305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6838138264873872115555253 641075462331925510833305)
                      ·
                        rfl

theorem cell23_1248490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 4, 2, 1, 1, 1, 5].length) (baseStart_1248490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248490 prefixEnd_1248490 := by exact prefixLift 1248490
  have htrace : WordTrace (prefixWord ++ tailWord_1248490) baseStart_1248490 baseEnd_1248490 := by
    simpa [prefixWord, tailWord_1248490, baseEnd_1248490] using wordTrace_append hprefix tailTrace_1248490
  have hstable : (prefixWord ++ tailWord_1248490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248490).length < 2 ^ (prefixWord ++ tailWord_1248490).sum := by decide
  have hdescent : baseEnd_1248490 < baseStart_1248490 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248493 : List Nat := [1, 5, 1, 2, 2, 1, 11]
def baseStart_1248493 : Nat := 118140960795 + 1248493 * 2 ^ 59
def prefixEnd_1248493 : Nat := 4983230072969 + 3 ^ 40 * 1248493 * 2
def baseEnd_1248493 : Nat := 7914530898443074062911

theorem tailTrace_1248493 : CollatzResearch.WordTrace tailWord_1248493 prefixEnd_1248493 7914530898443074062911 := by
  unfold tailWord_1248493
  simp only [CollatzResearch.WordTrace]
  refine ⟨45536280665930561473750133, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30357520443953707649166755 45536280665930561473750133)
  ·
    refine ⟨4269026312430990138164075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45536280665930561473750133 4269026312430990138164075)
    ·
      refine ⟨6403539468646485207246113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4269026312430990138164075 6403539468646485207246113)
      ·
        refine ⟨4802654601484863905434585, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6403539468646485207246113 4802654601484863905434585)
        ·
          refine ⟨3601990951113647929075939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4802654601484863905434585 3601990951113647929075939)
          ·
            refine ⟨5402986426670471893613909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3601990951113647929075939 5402986426670471893613909)
            ·
              refine ⟨7914530898443074062911, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5402986426670471893613909 7914530898443074062911)
              ·
                rfl

theorem cell23_1248493_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 2, 1, 11].length) (baseStart_1248493 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248493 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248493 prefixEnd_1248493 := by exact prefixLift 1248493
  have htrace : WordTrace (prefixWord ++ tailWord_1248493) baseStart_1248493 baseEnd_1248493 := by
    simpa [prefixWord, tailWord_1248493, baseEnd_1248493] using wordTrace_append hprefix tailTrace_1248493
  have hstable : (prefixWord ++ tailWord_1248493).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248493).length < 2 ^ (prefixWord ++ tailWord_1248493).sum := by decide
  have hdescent : baseEnd_1248493 < baseStart_1248493 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248493) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248503 : List Nat := [1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 3]
def baseStart_1248503 : Nat := 118140960795 + 1248503 * 2 ^ 59
def prefixEnd_1248503 : Nat := 4983230072969 + 3 ^ 40 * 1248503 * 2
def baseEnd_1248503 : Nat := 641082137580433959970745

theorem tailTrace_1248503 : CollatzResearch.WordTrace tailWord_1248503 prefixEnd_1248503 641082137580433959970745 := by
  unfold tailWord_1248503
  simp only [CollatzResearch.WordTrace]
  refine ⟨45536645395894333181614163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30357763597262888787742775 45536645395894333181614163)
  ·
    refine ⟨68304968093841499772421245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45536645395894333181614163 68304968093841499772421245)
    ·
      refine ⟨25614363035190562414657967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68304968093841499772421245 25614363035190562414657967)
      ·
        refine ⟨38421544552785843621986951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25614363035190562414657967 38421544552785843621986951)
        ·
          refine ⟨57632316829178765432980427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38421544552785843621986951 57632316829178765432980427)
          ·
            refine ⟨86448475243768148149470641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57632316829178765432980427 86448475243768148149470641)
            ·
              refine ⟨64836356432826111112102981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86448475243768148149470641 64836356432826111112102981)
              ·
                refine ⟨12156816831154895833519309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64836356432826111112102981 12156816831154895833519309)
                ·
                  refine ⟨4558806311683085937569741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12156816831154895833519309 4558806311683085937569741)
                  ·
                    refine ⟨1709552366881157226588653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4558806311683085937569741 1709552366881157226588653)
                    ·
                      refine ⟨641082137580433959970745, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1709552366881157226588653 641082137580433959970745)
                      ·
                        rfl

theorem cell23_1248503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 4, 3, 3, 3].length) (baseStart_1248503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248503 prefixEnd_1248503 := by exact prefixLift 1248503
  have htrace : WordTrace (prefixWord ++ tailWord_1248503) baseStart_1248503 baseEnd_1248503 := by
    simpa [prefixWord, tailWord_1248503, baseEnd_1248503] using wordTrace_append hprefix tailTrace_1248503
  have hstable : (prefixWord ++ tailWord_1248503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248503).length < 2 ^ (prefixWord ++ tailWord_1248503).sum := by decide
  have hdescent : baseEnd_1248503 < baseStart_1248503 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248510 : List Nat := [4, 2, 2, 1, 1, 3, 2, 8]
def baseStart_1248510 : Nat := 118140960795 + 1248510 * 2 ^ 59
def prefixEnd_1248510 : Nat := 4983230072969 + 3 ^ 40 * 1248510 * 2
def baseEnd_1248510 : Nat := 23743915997963534540119

theorem tailTrace_1248510 : CollatzResearch.WordTrace tailWord_1248510 prefixEnd_1248510 23743915997963534540119 := by
  unfold tailWord_1248510
  simp only [CollatzResearch.WordTrace]
  refine ⟨5692112588358621672139873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30357933804579315584745989 5692112588358621672139873)
  ·
    refine ⟨4269084441268966254104905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5692112588358621672139873 4269084441268966254104905)
    ·
      refine ⟨3201813330951724690578679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4269084441268966254104905 3201813330951724690578679)
      ·
        refine ⟨4802719996427587035868019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201813330951724690578679 4802719996427587035868019)
        ·
          refine ⟨7204079994641380553802029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4802719996427587035868019 7204079994641380553802029)
          ·
            refine ⟨2701529997990517707675761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7204079994641380553802029 2701529997990517707675761)
            ·
              refine ⟨2026147498492888280756821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701529997990517707675761 2026147498492888280756821)
              ·
                refine ⟨23743915997963534540119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2026147498492888280756821 23743915997963534540119)
                ·
                  rfl

theorem cell23_1248510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 3, 2, 8].length) (baseStart_1248510 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248510 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248510 prefixEnd_1248510 := by exact prefixLift 1248510
  have htrace : WordTrace (prefixWord ++ tailWord_1248510) baseStart_1248510 baseEnd_1248510 := by
    simpa [prefixWord, tailWord_1248510, baseEnd_1248510] using wordTrace_append hprefix tailTrace_1248510
  have hstable : (prefixWord ++ tailWord_1248510).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248510).length < 2 ^ (prefixWord ++ tailWord_1248510).sum := by decide
  have hdescent : baseEnd_1248510 < baseStart_1248510 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248514 : List Nat := [3, 4, 1, 1, 3, 1, 1, 3, 2, 4]
def baseStart_1248514 : Nat := 118140960795 + 1248514 * 2 ^ 59
def prefixEnd_1248514 : Nat := 4983230072969 + 3 ^ 40 * 1248514 * 2
def baseEnd_1248514 : Nat := 213695928622544472311065

theorem tailTrace_1248514 : CollatzResearch.WordTrace tailWord_1248514 prefixEnd_1248514 213695928622544472311065 := by
  unfold tailWord_1248514
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384261649713620515066149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30358031065902988040176397 11384261649713620515066149)
  ·
    refine ⟨2134549059321303846574903, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 11384261649713620515066149 2134549059321303846574903)
    ·
      refine ⟨3201823588981955769862355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2134549059321303846574903 3201823588981955769862355)
      ·
        refine ⟨4802735383472933654793533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3201823588981955769862355 4802735383472933654793533)
        ·
          refine ⟨1801025768802350120547575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4802735383472933654793533 1801025768802350120547575)
          ·
            refine ⟨2701538653203525180821363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801025768802350120547575 2701538653203525180821363)
            ·
              refine ⟨4052307979805287771232045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2701538653203525180821363 4052307979805287771232045)
              ·
                refine ⟨1519615492426982914212017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4052307979805287771232045 1519615492426982914212017)
                ·
                  refine ⟨1139711619320237185659013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1519615492426982914212017 1139711619320237185659013)
                  ·
                    refine ⟨213695928622544472311065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139711619320237185659013 213695928622544472311065)
                    ·
                      rfl

theorem cell23_1248514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 3, 2, 4].length) (baseStart_1248514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248514 prefixEnd_1248514 := by exact prefixLift 1248514
  have htrace : WordTrace (prefixWord ++ tailWord_1248514) baseStart_1248514 baseEnd_1248514 := by
    simpa [prefixWord, tailWord_1248514, baseEnd_1248514] using wordTrace_append hprefix tailTrace_1248514
  have hstable : (prefixWord ++ tailWord_1248514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248514).length < 2 ^ (prefixWord ++ tailWord_1248514).sum := by decide
  have hdescent : baseEnd_1248514 < baseStart_1248514 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248554 : List Nat := [3, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3]
def baseStart_1248554 : Nat := 118140960795 + 1248554 * 2 ^ 59
def prefixEnd_1248554 : Nat := 4983230072969 + 3 ^ 40 * 1248554 * 2
def baseEnd_1248554 : Nat := 641108325093813260433011

theorem tailTrace_1248554 : CollatzResearch.WordTrace tailWord_1248554 prefixEnd_1248554 641108325093813260433011 := by
  unfold tailWord_1248554
  simp only [CollatzResearch.WordTrace]
  refine ⟨11384626379677392222930179, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30359003679139712594480477 11384626379677392222930179)
  ·
    refine ⟨17076939569516088334395269, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11384626379677392222930179 17076939569516088334395269)
    ·
      refine ⟨3201926169284266562699113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17076939569516088334395269 3201926169284266562699113)
      ·
        refine ⟨2401444626963199922024335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3201926169284266562699113 2401444626963199922024335)
        ·
          refine ⟨3602166940444799883036503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2401444626963199922024335 3602166940444799883036503)
          ·
            refine ⟨5403250410667199824554755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602166940444799883036503 5403250410667199824554755)
            ·
              refine ⟨8104875616000799736832133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403250410667199824554755 8104875616000799736832133)
              ·
                refine ⟨1519664178000149950656025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8104875616000799736832133 1519664178000149950656025)
                ·
                  refine ⟨1139748133500112462992019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1519664178000149950656025 1139748133500112462992019)
                  ·
                    refine ⟨1709622200250168694488029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1139748133500112462992019 1709622200250168694488029)
                    ·
                      refine ⟨641108325093813260433011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1709622200250168694488029 641108325093813260433011)
                      ·
                        rfl

theorem cell23_1248554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 1, 1, 1, 4, 2, 1, 3].length) (baseStart_1248554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248554 prefixEnd_1248554 := by exact prefixLift 1248554
  have htrace : WordTrace (prefixWord ++ tailWord_1248554) baseStart_1248554 baseEnd_1248554 := by
    simpa [prefixWord, tailWord_1248554, baseEnd_1248554] using wordTrace_append hprefix tailTrace_1248554
  have hstable : (prefixWord ++ tailWord_1248554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248554).length < 2 ^ (prefixWord ++ tailWord_1248554).sum := by decide
  have hdescent : baseEnd_1248554 < baseStart_1248554 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248560 : List Nat := [2, 1, 1, 1, 2, 2, 3, 2, 3, 4, 2]
def baseStart_1248560 : Nat := 118140960795 + 1248560 * 2 ^ 59
def prefixEnd_1248560 : Nat := 4983230072969 + 3 ^ 40 * 1248560 * 2
def baseEnd_1248560 : Nat := 641111405977740236957983

theorem tailTrace_1248560 : CollatzResearch.WordTrace tailWord_1248560 prefixEnd_1248560 641111405977740236957983 := by
  unfold tailWord_1248560
  simp only [CollatzResearch.WordTrace]
  refine ⟨22769362178343915958219567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30359149571125221277626089 22769362178343915958219567)
  ·
    refine ⟨34154043267515873937329351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22769362178343915958219567 34154043267515873937329351)
    ·
      refine ⟨51231064901273810905994027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34154043267515873937329351 51231064901273810905994027)
      ·
        refine ⟨76846597351910716358991041, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51231064901273810905994027 76846597351910716358991041)
        ·
          refine ⟨57634948013933037269243281, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76846597351910716358991041 57634948013933037269243281)
          ·
            refine ⟨43226211010449777951932461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57634948013933037269243281 43226211010449777951932461)
            ·
              refine ⟨16209829128918666731974673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43226211010449777951932461 16209829128918666731974673)
              ·
                refine ⟨12157371846689000048981005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16209829128918666731974673 12157371846689000048981005)
                ·
                  refine ⟨4559014442508375018367877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12157371846689000048981005 4559014442508375018367877)
                  ·
                    refine ⟨854815207970320315943977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4559014442508375018367877 854815207970320315943977)
                    ·
                      refine ⟨641111405977740236957983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854815207970320315943977 641111405977740236957983)
                      ·
                        rfl

theorem cell23_1248560_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 3, 2, 3, 4, 2].length) (baseStart_1248560 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248560 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248560 prefixEnd_1248560 := by exact prefixLift 1248560
  have htrace : WordTrace (prefixWord ++ tailWord_1248560) baseStart_1248560 baseEnd_1248560 := by
    simpa [prefixWord, tailWord_1248560, baseEnd_1248560] using wordTrace_append hprefix tailTrace_1248560
  have hstable : (prefixWord ++ tailWord_1248560).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248560).length < 2 ^ (prefixWord ++ tailWord_1248560).sum := by decide
  have hdescent : baseEnd_1248560 < baseStart_1248560 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248560) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248583 : List Nat := [1, 1, 4, 1, 2, 3, 1, 1, 9]
def baseStart_1248583 : Nat := 118140960795 + 1248583 * 2 ^ 59
def prefixEnd_1248583 : Nat := 4983230072969 + 3 ^ 40 * 1248583 * 2
def baseEnd_1248583 : Nat := 71235912892532627441153

theorem tailTrace_1248583 : CollatzResearch.WordTrace tailWord_1248583 prefixEnd_1248583 71235912892532627441153 := by
  unfold tailWord_1248583
  simp only [CollatzResearch.WordTrace]
  refine ⟨45539563235604506844526403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30359708823736337896350935 45539563235604506844526403)
  ·
    refine ⟨68309344853406760266789605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45539563235604506844526403 68309344853406760266789605)
    ·
      refine ⟨12808002160013767550023051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68309344853406760266789605 12808002160013767550023051)
      ·
        refine ⟨19212003240020651325034577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12808002160013767550023051 19212003240020651325034577)
        ·
          refine ⟨14409002430015488493775933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19212003240020651325034577 14409002430015488493775933)
          ·
            refine ⟨5403375911255808185165975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14409002430015488493775933 5403375911255808185165975)
            ·
              refine ⟨8105063866883712277748963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5403375911255808185165975 8105063866883712277748963)
              ·
                refine ⟨12157595800325568416623445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105063866883712277748963 12157595800325568416623445)
                ·
                  refine ⟨71235912892532627441153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12157595800325568416623445 71235912892532627441153)
                  ·
                    rfl

theorem cell23_1248583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 3, 1, 1, 9].length) (baseStart_1248583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248583 prefixEnd_1248583 := by exact prefixLift 1248583
  have htrace : WordTrace (prefixWord ++ tailWord_1248583) baseStart_1248583 baseEnd_1248583 := by
    simpa [prefixWord, tailWord_1248583, baseEnd_1248583] using wordTrace_append hprefix tailTrace_1248583
  have hstable : (prefixWord ++ tailWord_1248583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248583).length < 2 ^ (prefixWord ++ tailWord_1248583).sum := by decide
  have hdescent : baseEnd_1248583 < baseStart_1248583 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248605 : List Nat := [1, 4, 5, 1, 1, 2, 1, 2, 2, 1, 3]
def baseStart_1248605 : Nat := 118140960795 + 1248605 * 2 ^ 59
def prefixEnd_1248605 : Nat := 4983230072969 + 3 ^ 40 * 1248605 * 2
def baseEnd_1248605 : Nat := 641134512607192560895277

theorem tailTrace_1248605 : CollatzResearch.WordTrace tailWord_1248605 prefixEnd_1248605 641134512607192560895277 := by
  unfold tailWord_1248605
  simp only [CollatzResearch.WordTrace]
  refine ⟨45540365641524804601827269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30360243761016536401218179 45540365641524804601827269)
  ·
    refine ⟨8538818557785900862842613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45540365641524804601827269 8538818557785900862842613)
    ·
      refine ⟨800514239792428205891495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 8538818557785900862842613 800514239792428205891495)
      ·
        refine ⟨1200771359688642308837243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800514239792428205891495 1200771359688642308837243)
        ·
          refine ⟨1801157039532963463255865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1200771359688642308837243 1801157039532963463255865)
          ·
            refine ⟨1350867779649722597441899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1801157039532963463255865 1350867779649722597441899)
            ·
              refine ⟨2026301669474583896162849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350867779649722597441899 2026301669474583896162849)
              ·
                refine ⟨1519726252105937922122137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026301669474583896162849 1519726252105937922122137)
                ·
                  refine ⟨1139794689079453441591603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1519726252105937922122137 1139794689079453441591603)
                  ·
                    refine ⟨1709692033619180162387405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1139794689079453441591603 1709692033619180162387405)
                    ·
                      refine ⟨641134512607192560895277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1709692033619180162387405 641134512607192560895277)
                      ·
                        rfl

theorem cell23_1248605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 5, 1, 1, 2, 1, 2, 2, 1, 3].length) (baseStart_1248605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248605 prefixEnd_1248605 := by exact prefixLift 1248605
  have htrace : WordTrace (prefixWord ++ tailWord_1248605) baseStart_1248605 baseEnd_1248605 := by
    simpa [prefixWord, tailWord_1248605, baseEnd_1248605] using wordTrace_append hprefix tailTrace_1248605
  have hstable : (prefixWord ++ tailWord_1248605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248605).length < 2 ^ (prefixWord ++ tailWord_1248605).sum := by decide
  have hdescent : baseEnd_1248605 < baseStart_1248605 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248611 : List Nat := [1, 1, 1, 5, 2, 4, 1, 2, 2, 2, 2]
def baseStart_1248611 : Nat := 118140960795 + 1248611 * 2 ^ 59
def prefixEnd_1248611 : Nat := 4983230072969 + 3 ^ 40 * 1248611 * 2
def baseEnd_1248611 : Nat := 641137593491119537420249

theorem tailTrace_1248611 : CollatzResearch.WordTrace tailWord_1248611 prefixEnd_1248611 641137593491119537420249 := by
  unfold tailWord_1248611
  simp only [CollatzResearch.WordTrace]
  refine ⟨45540584479503067626545687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30360389653002045084363791 45540584479503067626545687)
  ·
    refine ⟨68310876719254601439818531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45540584479503067626545687 68310876719254601439818531)
    ·
      refine ⟨102466315078881902159727797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68310876719254601439818531 102466315078881902159727797)
      ·
        refine ⟨9606217038645178327474481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102466315078881902159727797 9606217038645178327474481)
        ·
          refine ⟨7204662778983883745605861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9606217038645178327474481 7204662778983883745605861)
          ·
            refine ⟨1350874271059478202301099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7204662778983883745605861 1350874271059478202301099)
            ·
              refine ⟨2026311406589217303451649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1350874271059478202301099 2026311406589217303451649)
              ·
                refine ⟨1519733554941912977588737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026311406589217303451649 1519733554941912977588737)
                ·
                  refine ⟨1139800166206434733191553, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1519733554941912977588737 1139800166206434733191553)
                  ·
                    refine ⟨854850124654826049893665, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139800166206434733191553 854850124654826049893665)
                    ·
                      refine ⟨641137593491119537420249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854850124654826049893665 641137593491119537420249)
                      ·
                        rfl

theorem cell23_1248611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 2, 4, 1, 2, 2, 2, 2].length) (baseStart_1248611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248611 prefixEnd_1248611 := by exact prefixLift 1248611
  have htrace : WordTrace (prefixWord ++ tailWord_1248611) baseStart_1248611 baseEnd_1248611 := by
    simpa [prefixWord, tailWord_1248611, baseEnd_1248611] using wordTrace_append hprefix tailTrace_1248611
  have hstable : (prefixWord ++ tailWord_1248611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248611).length < 2 ^ (prefixWord ++ tailWord_1248611).sum := by decide
  have hdescent : baseEnd_1248611 < baseStart_1248611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248623 : List Nat := [1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 7]
def baseStart_1248623 : Nat := 118140960795 + 1248623 * 2 ^ 59
def prefixEnd_1248623 : Nat := 4983230072969 + 3 ^ 40 * 1248623 * 2
def baseEnd_1248623 : Nat := 641143755258973490470193

theorem tailTrace_1248623 : CollatzResearch.WordTrace tailWord_1248623 prefixEnd_1248623 641143755258973490470193 := by
  unfold tailWord_1248623
  simp only [CollatzResearch.WordTrace]
  refine ⟨45541022155459593675982523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30360681436973062450655015 45541022155459593675982523)
  ·
    refine ⟨68311533233189390513973785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45541022155459593675982523 68311533233189390513973785)
    ·
      refine ⟨51233649924892042885480339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68311533233189390513973785 51233649924892042885480339)
      ·
        refine ⟨76850474887338064328220509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51233649924892042885480339 76850474887338064328220509)
        ·
          refine ⟨28818928082751774123082691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76850474887338064328220509 28818928082751774123082691)
          ·
            refine ⟨43228392124127661184624037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28818928082751774123082691 43228392124127661184624037)
            ·
              refine ⟨8105323523273936472117007, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43228392124127661184624037 8105323523273936472117007)
              ·
                refine ⟨12157985284910904708175511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8105323523273936472117007 12157985284910904708175511)
                ·
                  refine ⟨18236977927366357062263267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12157985284910904708175511 18236977927366357062263267)
                  ·
                    refine ⟨27355466891049535593394901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18236977927366357062263267 27355466891049535593394901)
                    ·
                      refine ⟨641143755258973490470193, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27355466891049535593394901 641143755258973490470193)
                      ·
                        rfl

theorem cell23_1248623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 1, 4, 1, 1, 1, 7].length) (baseStart_1248623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248623 prefixEnd_1248623 := by exact prefixLift 1248623
  have htrace : WordTrace (prefixWord ++ tailWord_1248623) baseStart_1248623 baseEnd_1248623 := by
    simpa [prefixWord, tailWord_1248623, baseEnd_1248623] using wordTrace_append hprefix tailTrace_1248623
  have hstable : (prefixWord ++ tailWord_1248623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248623).length < 2 ^ (prefixWord ++ tailWord_1248623).sum := by decide
  have hdescent : baseEnd_1248623 < baseStart_1248623 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248683 : List Nat := [1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7]
def baseStart_1248683 : Nat := 118140960795 + 1248683 * 2 ^ 59
def prefixEnd_1248683 : Nat := 4983230072969 + 3 ^ 40 * 1248683 * 2
def baseEnd_1248683 : Nat := 641174564098243255719917

theorem tailTrace_1248683 : CollatzResearch.WordTrace tailWord_1248683 prefixEnd_1248683 641174564098243255719917 := by
  unfold tailWord_1248683
  simp only [CollatzResearch.WordTrace]
  refine ⟨45543210535242223923166703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30362140356828149282111135 45543210535242223923166703)
  ·
    refine ⟨68314815802863335884750055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45543210535242223923166703 68314815802863335884750055)
    ·
      refine ⟨102472223704295003827125083, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68314815802863335884750055 102472223704295003827125083)
      ·
        refine ⟨153708335556442505740687625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102472223704295003827125083 153708335556442505740687625)
        ·
          refine ⟨115281251667331879305515719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153708335556442505740687625 115281251667331879305515719)
          ·
            refine ⟨172921877500997818958273579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115281251667331879305515719 172921877500997818958273579)
            ·
              refine ⟨259382816251496728437410369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 172921877500997818958273579 259382816251496728437410369)
              ·
                refine ⟨194537112188622546328057777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 259382816251496728437410369 194537112188622546328057777)
                ·
                  refine ⟨145902834141466909746043333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 194537112188622546328057777 145902834141466909746043333)
                  ·
                    refine ⟨27356781401525045577383125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 145902834141466909746043333 27356781401525045577383125)
                    ·
                      refine ⟨641174564098243255719917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27356781401525045577383125 641174564098243255719917)
                      ·
                        rfl

theorem cell23_1248683_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_1248683 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248683 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248683 prefixEnd_1248683 := by exact prefixLift 1248683
  have htrace : WordTrace (prefixWord ++ tailWord_1248683) baseStart_1248683 baseEnd_1248683 := by
    simpa [prefixWord, tailWord_1248683, baseEnd_1248683] using wordTrace_append hprefix tailTrace_1248683
  have hstable : (prefixWord ++ tailWord_1248683).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248683).length < 2 ^ (prefixWord ++ tailWord_1248683).sum := by decide
  have hdescent : baseEnd_1248683 < baseStart_1248683 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248683) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248724 : List Nat := [2, 4, 1, 2, 3, 1, 2, 2, 6]
def baseStart_1248724 : Nat := 118140960795 + 1248724 * 2 ^ 59
def prefixEnd_1248724 : Nat := 4983230072969 + 3 ^ 40 * 1248724 * 2
def baseEnd_1248724 : Nat := 71243957422786399478581

theorem tailTrace_1248724 : CollatzResearch.WordTrace tailWord_1248724 prefixEnd_1248724 71243957422786399478581 := by
  unfold tailWord_1248724
  simp only [CollatzResearch.WordTrace]
  refine ⟨22772352964046843962704613, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30363137285395791950272817 22772352964046843962704613)
  ·
    refine ⟨4269816180758783243007115, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22772352964046843962704613 4269816180758783243007115)
    ·
      refine ⟨6404724271138174864510673, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4269816180758783243007115 6404724271138174864510673)
      ·
        refine ⟨4803543203353631148383005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6404724271138174864510673 4803543203353631148383005)
        ·
          refine ⟨1801328701257611680643627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4803543203353631148383005 1801328701257611680643627)
          ·
            refine ⟨2701993051886417520965441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1801328701257611680643627 2701993051886417520965441)
            ·
              refine ⟨2026494788914813140724081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2701993051886417520965441 2026494788914813140724081)
              ·
                refine ⟨1519871091686109855543061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026494788914813140724081 1519871091686109855543061)
                ·
                  refine ⟨71243957422786399478581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1519871091686109855543061 71243957422786399478581)
                  ·
                    rfl

theorem cell23_1248724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 3, 1, 2, 2, 6].length) (baseStart_1248724 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248724 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248724 prefixEnd_1248724 := by exact prefixLift 1248724
  have htrace : WordTrace (prefixWord ++ tailWord_1248724) baseStart_1248724 baseEnd_1248724 := by
    simpa [prefixWord, tailWord_1248724, baseEnd_1248724] using wordTrace_append hprefix tailTrace_1248724
  have hstable : (prefixWord ++ tailWord_1248724).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248724).length < 2 ^ (prefixWord ++ tailWord_1248724).sum := by decide
  have hdescent : baseEnd_1248724 < baseStart_1248724 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248801 : List Nat := [1, 2, 3, 2, 2, 3, 3, 1, 2, 4]
def baseStart_1248801 : Nat := 118140960795 + 1248801 * 2 ^ 59
def prefixEnd_1248801 : Nat := 4983230072969 + 3 ^ 40 * 1248801 * 2
def baseEnd_1248801 : Nat := 213745051605157931348125

theorem tailTrace_1248801 : CollatzResearch.WordTrace tailWord_1248801 prefixEnd_1248801 213745051605157931348125 := by
  unfold tailWord_1248801
  simp only [CollatzResearch.WordTrace]
  refine ⟨45547514348814730075962257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30365009565876486717308171 45547514348814730075962257)
  ·
    refine ⟨34160635761611047556971693, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45547514348814730075962257 34160635761611047556971693)
    ·
      refine ⟨12810238410604142833864385, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34160635761611047556971693 12810238410604142833864385)
      ·
        refine ⟨9607678807953107125398289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12810238410604142833864385 9607678807953107125398289)
        ·
          refine ⟨7205759105964830344048717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9607678807953107125398289 7205759105964830344048717)
          ·
            refine ⟨2702159664736811379018269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7205759105964830344048717 2702159664736811379018269)
            ·
              refine ⟨1013309874276304267131851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2702159664736811379018269 1013309874276304267131851)
              ·
                refine ⟨1519964811414456400697777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013309874276304267131851 1519964811414456400697777)
                ·
                  refine ⟨1139973608560842300523333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1519964811414456400697777 1139973608560842300523333)
                  ·
                    refine ⟨213745051605157931348125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1139973608560842300523333 213745051605157931348125)
                    ·
                      rfl

theorem cell23_1248801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 2, 3, 3, 1, 2, 4].length) (baseStart_1248801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248801 prefixEnd_1248801 := by exact prefixLift 1248801
  have htrace : WordTrace (prefixWord ++ tailWord_1248801) baseStart_1248801 baseEnd_1248801 := by
    simpa [prefixWord, tailWord_1248801, baseEnd_1248801] using wordTrace_append hprefix tailTrace_1248801
  have hstable : (prefixWord ++ tailWord_1248801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248801).length < 2 ^ (prefixWord ++ tailWord_1248801).sum := by decide
  have hdescent : baseEnd_1248801 < baseStart_1248801 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248814 : List Nat := [4, 1, 3, 1, 2, 1, 4, 7]
def baseStart_1248814 : Nat := 118140960795 + 1248814 * 2 ^ 59
def prefixEnd_1248814 : Nat := 4983230072969 + 3 ^ 40 * 1248814 * 2
def baseEnd_1248814 : Nat := 23749697409777120117845

theorem tailTrace_1248814 : CollatzResearch.WordTrace tailWord_1248814 prefixEnd_1248814 23749697409777120117845 := by
  unfold tailWord_1248814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5693498562220954162023187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30365325665178422197456997 5693498562220954162023187)
  ·
    refine ⟨8540247843331431243034781, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5693498562220954162023187 8540247843331431243034781)
    ·
      refine ⟨3202592941249286716138043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8540247843331431243034781 3202592941249286716138043)
      ·
        refine ⟨4803889411873930074207065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3202592941249286716138043 4803889411873930074207065)
        ·
          refine ⟨3602917058905447555655299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4803889411873930074207065 3602917058905447555655299)
          ·
            refine ⟨5404375588358171333482949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3602917058905447555655299 5404375588358171333482949)
            ·
              refine ⟨1013320422817157125028053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5404375588358171333482949 1013320422817157125028053)
              ·
                refine ⟨23749697409777120117845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1013320422817157125028053 23749697409777120117845)
                ·
                  rfl

theorem cell23_1248814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 1, 4, 7].length) (baseStart_1248814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248814 prefixEnd_1248814 := by exact prefixLift 1248814
  have htrace : WordTrace (prefixWord ++ tailWord_1248814) baseStart_1248814 baseEnd_1248814 := by
    simpa [prefixWord, tailWord_1248814, baseEnd_1248814] using wordTrace_append hprefix tailTrace_1248814
  have hstable : (prefixWord ++ tailWord_1248814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248814).length < 2 ^ (prefixWord ++ tailWord_1248814).sum := by decide
  have hdescent : baseEnd_1248814 < baseStart_1248814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248824 : List Nat := [2, 1, 2, 1, 4, 2, 1, 2, 4, 1, 3]
def baseStart_1248824 : Nat := 118140960795 + 1248824 * 2 ^ 59
def prefixEnd_1248824 : Nat := 4983230072969 + 3 ^ 40 * 1248824 * 2
def baseEnd_1248824 : Nat := 641246964870527204056769

theorem tailTrace_1248824 : CollatzResearch.WordTrace tailWord_1248824 prefixEnd_1248824 641246964870527204056769 := by
  unfold tailWord_1248824
  simp only [CollatzResearch.WordTrace]
  refine ⟨22774176613865702502024763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30365568818487603336033017 22774176613865702502024763)
  ·
    refine ⟨34161264920798553753037145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22774176613865702502024763 34161264920798553753037145)
    ·
      refine ⟨25620948690598915314777859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34161264920798553753037145 25620948690598915314777859)
      ·
        refine ⟨38431423035898372972166789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25620948690598915314777859 38431423035898372972166789)
        ·
          refine ⟨7205891819230944932281273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38431423035898372972166789 7205891819230944932281273)
          ·
            refine ⟨5404418864423208699210955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7205891819230944932281273 5404418864423208699210955)
            ·
              refine ⟨8106628296634813048816433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404418864423208699210955 8106628296634813048816433)
              ·
                refine ⟨6079971222476109786612325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8106628296634813048816433 6079971222476109786612325)
                ·
                  refine ⟨1139994604214270584989811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6079971222476109786612325 1139994604214270584989811)
                  ·
                    refine ⟨1709991906321405877484717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1139994604214270584989811 1709991906321405877484717)
                    ·
                      refine ⟨641246964870527204056769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1709991906321405877484717 641246964870527204056769)
                      ·
                        rfl

theorem cell23_1248824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 4, 2, 1, 2, 4, 1, 3].length) (baseStart_1248824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248824 prefixEnd_1248824 := by exact prefixLift 1248824
  have htrace : WordTrace (prefixWord ++ tailWord_1248824) baseStart_1248824 baseEnd_1248824 := by
    simpa [prefixWord, tailWord_1248824, baseEnd_1248824] using wordTrace_append hprefix tailTrace_1248824
  have hstable : (prefixWord ++ tailWord_1248824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248824).length < 2 ^ (prefixWord ++ tailWord_1248824).sum := by decide
  have hdescent : baseEnd_1248824 < baseStart_1248824 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248825 : List Nat := [1, 2, 1, 5, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1248825 : Nat := 118140960795 + 1248825 * 2 ^ 59
def prefixEnd_1248825 : Nat := 4983230072969 + 3 ^ 40 * 1248825 * 2
def baseEnd_1248825 : Nat := 641247478351181700144265

theorem tailTrace_1248825 : CollatzResearch.WordTrace tailWord_1248825 prefixEnd_1248825 641247478351181700144265 := by
  unfold tailWord_1248825
  simp only [CollatzResearch.WordTrace]
  refine ⟨45548389700727782174835929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30365593133818521449890619 45548389700727782174835929)
  ·
    refine ⟨34161292275545836631126947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45548389700727782174835929 34161292275545836631126947)
    ·
      refine ⟨51241938413318754946690421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34161292275545836631126947 51241938413318754946690421)
      ·
        refine ⟨4803931726248633276252227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51241938413318754946690421 4803931726248633276252227)
        ·
          refine ⟨7205897589372949914378341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4803931726248633276252227 7205897589372949914378341)
          ·
            refine ⟨1351105798007428108945939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7205897589372949914378341 1351105798007428108945939)
            ·
              refine ⟨2026658697011142163418909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351105798007428108945939 2026658697011142163418909)
              ·
                refine ⟨759997011379178311282091, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2026658697011142163418909 759997011379178311282091)
                ·
                  refine ⟨1139995517068767466923137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 759997011379178311282091 1139995517068767466923137)
                  ·
                    refine ⟨854996637801575600192353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1139995517068767466923137 854996637801575600192353)
                    ·
                      refine ⟨641247478351181700144265, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 854996637801575600192353 641247478351181700144265)
                      ·
                        rfl

theorem cell23_1248825_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1248825 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248825 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248825 prefixEnd_1248825 := by exact prefixLift 1248825
  have htrace : WordTrace (prefixWord ++ tailWord_1248825) baseStart_1248825 baseEnd_1248825 := by
    simpa [prefixWord, tailWord_1248825, baseEnd_1248825] using wordTrace_append hprefix tailTrace_1248825
  have hstable : (prefixWord ++ tailWord_1248825).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248825).length < 2 ^ (prefixWord ++ tailWord_1248825).sum := by decide
  have hdescent : baseEnd_1248825 < baseStart_1248825 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248825) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248864 : List Nat := [2, 1, 1, 3, 2, 1, 1, 5, 1, 4, 2]
def baseStart_1248864 : Nat := 118140960795 + 1248864 * 2 ^ 59
def prefixEnd_1248864 : Nat := 4983230072969 + 3 ^ 40 * 1248864 * 2
def baseEnd_1248864 : Nat := 641267504096707047556585

theorem tailTrace_1248864 : CollatzResearch.WordTrace tailWord_1248864 prefixEnd_1248864 641267504096707047556585 := by
  unfold tailWord_1248864
  simp only [CollatzResearch.WordTrace]
  refine ⟨22774906073793245917752823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30366541431724327890337097 22774906073793245917752823)
  ·
    refine ⟨34162359110689868876629235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22774906073793245917752823 34162359110689868876629235)
    ·
      refine ⟨51243538666034803314943853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34162359110689868876629235 51243538666034803314943853)
      ·
        refine ⟨19216326999763051243103945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51243538666034803314943853 19216326999763051243103945)
        ·
          refine ⟨14412245249822288432327959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19216326999763051243103945 14412245249822288432327959)
          ·
            refine ⟨21618367874733432648491939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14412245249822288432327959 21618367874733432648491939)
            ·
              refine ⟨32427551812100148972737909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21618367874733432648491939 32427551812100148972737909)
              ·
                refine ⟨3040082982384388966194179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32427551812100148972737909 3040082982384388966194179)
                ·
                  refine ⟨4560124473576583449291269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040082982384388966194179 4560124473576583449291269)
                  ·
                    refine ⟨855023338795609396742113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4560124473576583449291269 855023338795609396742113)
                    ·
                      refine ⟨641267504096707047556585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855023338795609396742113 641267504096707047556585)
                      ·
                        rfl

theorem cell23_1248864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 5, 1, 4, 2].length) (baseStart_1248864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248864 prefixEnd_1248864 := by exact prefixLift 1248864
  have htrace : WordTrace (prefixWord ++ tailWord_1248864) baseStart_1248864 baseEnd_1248864 := by
    simpa [prefixWord, tailWord_1248864, baseEnd_1248864] using wordTrace_append hprefix tailTrace_1248864
  have hstable : (prefixWord ++ tailWord_1248864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248864).length < 2 ^ (prefixWord ++ tailWord_1248864).sum := by decide
  have hdescent : baseEnd_1248864 < baseStart_1248864 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248867 : List Nat := [1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5]
def baseStart_1248867 : Nat := 118140960795 + 1248867 * 2 ^ 59
def prefixEnd_1248867 : Nat := 4983230072969 + 3 ^ 40 * 1248867 * 2
def baseEnd_1248867 : Nat := 641269044538670535819071

theorem tailTrace_1248867 : CollatzResearch.WordTrace tailWord_1248867 prefixEnd_1248867 641269044538670535819071 := by
  unfold tailWord_1248867
  simp only [CollatzResearch.WordTrace]
  refine ⟨45549921566575623347864855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30366614377717082231909903 45549921566575623347864855)
  ·
    refine ⟨68324882349863435021797283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45549921566575623347864855 68324882349863435021797283)
    ·
      refine ⟨102487323524795152532695925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68324882349863435021797283 102487323524795152532695925)
      ·
        refine ⟨9608186580449545549940243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102487323524795152532695925 9608186580449545549940243)
        ·
          refine ⟨14412279870674318324910365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9608186580449545549940243 14412279870674318324910365)
          ·
            refine ⟨5404604951502869371841387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14412279870674318324910365 5404604951502869371841387)
            ·
              refine ⟨8106907427254304057762081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5404604951502869371841387 8106907427254304057762081)
              ·
                refine ⟨6080180570440728043321561, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8106907427254304057762081 6080180570440728043321561)
                ·
                  refine ⟨4560135427830546032491171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6080180570440728043321561 4560135427830546032491171)
                  ·
                    refine ⟨6840203141745819048736757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4560135427830546032491171 6840203141745819048736757)
                    ·
                      refine ⟨641269044538670535819071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6840203141745819048736757 641269044538670535819071)
                      ·
                        rfl

theorem cell23_1248867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 3, 1, 2, 2, 1, 5].length) (baseStart_1248867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248867 prefixEnd_1248867 := by exact prefixLift 1248867
  have htrace : WordTrace (prefixWord ++ tailWord_1248867) baseStart_1248867 baseEnd_1248867 := by
    simpa [prefixWord, tailWord_1248867, baseEnd_1248867] using wordTrace_append hprefix tailTrace_1248867
  have hstable : (prefixWord ++ tailWord_1248867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248867).length < 2 ^ (prefixWord ++ tailWord_1248867).sum := by decide
  have hdescent : baseEnd_1248867 < baseStart_1248867 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248868 : List Nat := [2, 3, 1, 1, 2, 5, 1, 2, 1, 3, 2]
def baseStart_1248868 : Nat := 118140960795 + 1248868 * 2 ^ 59
def prefixEnd_1248868 : Nat := 4983230072969 + 3 ^ 40 * 1248868 * 2
def baseEnd_1248868 : Nat := 641269558019325031906567

theorem tailTrace_1248868 : CollatzResearch.WordTrace tailWord_1248868 prefixEnd_1248868 641269558019325031906567 := by
  unfold tailWord_1248868
  simp only [CollatzResearch.WordTrace]
  refine ⟨22774979019786000259325629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30366638693048000345767505 22774979019786000259325629)
  ·
    refine ⟨8540617132419750097247111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22774979019786000259325629 8540617132419750097247111)
    ·
      refine ⟨12810925698629625145870667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8540617132419750097247111 12810925698629625145870667)
      ·
        refine ⟨19216388547944437718806001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12810925698629625145870667 19216388547944437718806001)
        ·
          refine ⟨14412291410958328289104501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19216388547944437718806001 14412291410958328289104501)
          ·
            refine ⟨1351152319777343277103547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14412291410958328289104501 1351152319777343277103547)
            ·
              refine ⟨2026728479666014915655321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351152319777343277103547 2026728479666014915655321)
              ·
                refine ⟨1520046359749511186741491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2026728479666014915655321 1520046359749511186741491)
                ·
                  refine ⟨2280069539624266780112237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520046359749511186741491 2280069539624266780112237)
                  ·
                    refine ⟨855026077359100042542089, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280069539624266780112237 855026077359100042542089)
                    ·
                      refine ⟨641269558019325031906567, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855026077359100042542089 641269558019325031906567)
                      ·
                        rfl

theorem cell23_1248868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 5, 1, 2, 1, 3, 2].length) (baseStart_1248868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248868 prefixEnd_1248868 := by exact prefixLift 1248868
  have htrace : WordTrace (prefixWord ++ tailWord_1248868) baseStart_1248868 baseEnd_1248868 := by
    simpa [prefixWord, tailWord_1248868, baseEnd_1248868] using wordTrace_append hprefix tailTrace_1248868
  have hstable : (prefixWord ++ tailWord_1248868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248868).length < 2 ^ (prefixWord ++ tailWord_1248868).sum := by decide
  have hdescent : baseEnd_1248868 < baseStart_1248868 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248885 : List Nat := [1, 3, 4, 2, 1, 2, 3, 1, 1, 3, 2]
def baseStart_1248885 : Nat := 118140960795 + 1248885 * 2 ^ 59
def prefixEnd_1248885 : Nat := 4983230072969 + 3 ^ 40 * 1248885 * 2
def baseEnd_1248885 : Nat := 641278287190451465393989

theorem tailTrace_1248885 : CollatzResearch.WordTrace tailWord_1248885 prefixEnd_1248885 641278287190451465393989 := by
  unfold tailWord_1248885
  simp only [CollatzResearch.WordTrace]
  refine ⟨45550578080510412422020109, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30367052053673608281346739 45550578080510412422020109)
  ·
    refine ⟨17081466780191404658257541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45550578080510412422020109 17081466780191404658257541)
    ·
      refine ⟨3202775021285888373423289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17081466780191404658257541 3202775021285888373423289)
      ·
        refine ⟨2402081265964416280067467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3202775021285888373423289 2402081265964416280067467)
        ·
          refine ⟨3603121898946624420101201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402081265964416280067467 3603121898946624420101201)
          ·
            refine ⟨2702341424209968315075901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3603121898946624420101201 2702341424209968315075901)
            ·
              refine ⟨1013378034078738118153463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2702341424209968315075901 1013378034078738118153463)
              ·
                refine ⟨1520067051118107177230195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013378034078738118153463 1520067051118107177230195)
                ·
                  refine ⟨2280100576677160765845293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520067051118107177230195 2280100576677160765845293)
                  ·
                    refine ⟨855037716253935287191985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280100576677160765845293 855037716253935287191985)
                    ·
                      refine ⟨641278287190451465393989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855037716253935287191985 641278287190451465393989)
                      ·
                        rfl

theorem cell23_1248885_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 2, 1, 2, 3, 1, 1, 3, 2].length) (baseStart_1248885 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248885 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248885 prefixEnd_1248885 := by exact prefixLift 1248885
  have htrace : WordTrace (prefixWord ++ tailWord_1248885) baseStart_1248885 baseEnd_1248885 := by
    simpa [prefixWord, tailWord_1248885, baseEnd_1248885] using wordTrace_append hprefix tailTrace_1248885
  have hstable : (prefixWord ++ tailWord_1248885).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248885).length < 2 ^ (prefixWord ++ tailWord_1248885).sum := by decide
  have hdescent : baseEnd_1248885 < baseStart_1248885 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248885) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248917 : List Nat := [1, 3, 2, 1, 1, 1, 1, 4, 4, 5]
def baseStart_1248917 : Nat := 118140960795 + 1248917 * 2 ^ 59
def prefixEnd_1248917 : Nat := 4983230072969 + 3 ^ 40 * 1248917 * 2
def baseEnd_1248917 : Nat := 213764906190465113397947

theorem tailTrace_1248917 : CollatzResearch.WordTrace tailWord_1248917 prefixEnd_1248917 213764906190465113397947 := by
  unfold tailWord_1248917
  simp only [CollatzResearch.WordTrace]
  refine ⟨45551745216394481887185005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30367830144262987924790003 45551745216394481887185005)
  ·
    refine ⟨17081904456147930707694377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45551745216394481887185005 17081904456147930707694377)
    ·
      refine ⟨12811428342110948030770783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17081904456147930707694377 12811428342110948030770783)
      ·
        refine ⟨19217142513166422046156175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12811428342110948030770783 19217142513166422046156175)
        ·
          refine ⟨28825713769749633069234263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19217142513166422046156175 28825713769749633069234263)
          ·
            refine ⟨43238570654624449603851395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28825713769749633069234263 43238570654624449603851395)
            ·
              refine ⟨64857855981936674405777093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43238570654624449603851395 64857855981936674405777093)
              ·
                refine ⟨12160847996613126451083205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 64857855981936674405777093 12160847996613126451083205)
                ·
                  refine ⟨2280158999364961209578101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12160847996613126451083205 2280158999364961209578101)
                  ·
                    refine ⟨213764906190465113397947, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2280158999364961209578101 213764906190465113397947)
                    ·
                      rfl

theorem cell23_1248917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 4, 4, 5].length) (baseStart_1248917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248917 prefixEnd_1248917 := by exact prefixLift 1248917
  have htrace : WordTrace (prefixWord ++ tailWord_1248917) baseStart_1248917 baseEnd_1248917 := by
    simpa [prefixWord, tailWord_1248917, baseEnd_1248917] using wordTrace_append hprefix tailTrace_1248917
  have hstable : (prefixWord ++ tailWord_1248917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248917).length < 2 ^ (prefixWord ++ tailWord_1248917).sum := by decide
  have hdescent : baseEnd_1248917 < baseStart_1248917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248936 : List Nat := [2, 1, 7, 1, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1248936 : Nat := 118140960795 + 1248936 * 2 ^ 59
def prefixEnd_1248936 : Nat := 4983230072969 + 3 ^ 40 * 1248936 * 2
def baseEnd_1248936 : Nat := 641304474703830765856255

theorem tailTrace_1248936 : CollatzResearch.WordTrace tailWord_1248936 prefixEnd_1248936 641304474703830765856255 := by
  unfold tailWord_1248936
  simp only [CollatzResearch.WordTrace]
  refine ⟨22776219101662824066063331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30368292135550432088084441 22776219101662824066063331)
  ·
    refine ⟨34164328652494236099094997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22776219101662824066063331 34164328652494236099094997)
    ·
      refine ⟨800726452792833658572539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34164328652494236099094997 800726452792833658572539)
      ·
        refine ⟨1201089679189250487858809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 800726452792833658572539 1201089679189250487858809)
        ·
          refine ⟨900817259391937865894107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201089679189250487858809 900817259391937865894107)
          ·
            refine ⟨1351225889087906798841161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900817259391937865894107 1351225889087906798841161)
            ·
              refine ⟨1013419416815930099130871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351225889087906798841161 1013419416815930099130871)
              ·
                refine ⟨1520129125223895148696307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013419416815930099130871 1520129125223895148696307)
                ·
                  refine ⟨2280193687835842723044461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520129125223895148696307 2280193687835842723044461)
                  ·
                    refine ⟨855072632938441021141673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280193687835842723044461 855072632938441021141673)
                    ·
                      refine ⟨641304474703830765856255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855072632938441021141673 641304474703830765856255)
                      ·
                        rfl

theorem cell23_1248936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 7, 1, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1248936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248936 prefixEnd_1248936 := by exact prefixLift 1248936
  have htrace : WordTrace (prefixWord ++ tailWord_1248936) baseStart_1248936 baseEnd_1248936 := by
    simpa [prefixWord, tailWord_1248936, baseEnd_1248936] using wordTrace_append hprefix tailTrace_1248936
  have hstable : (prefixWord ++ tailWord_1248936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248936).length < 2 ^ (prefixWord ++ tailWord_1248936).sum := by decide
  have hdescent : baseEnd_1248936 < baseStart_1248936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248967 : List Nat := [1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 6]
def baseStart_1248967 : Nat := 118140960795 + 1248967 * 2 ^ 59
def prefixEnd_1248967 : Nat := 4983230072969 + 3 ^ 40 * 1248967 * 2
def baseEnd_1248967 : Nat := 641320392604120144568611

theorem tailTrace_1248967 : CollatzResearch.WordTrace tailWord_1248967 prefixEnd_1248967 641320392604120144568611 := by
  unfold tailWord_1248967
  simp only [CollatzResearch.WordTrace]
  refine ⟨45553568866213340426505155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30369045910808893617670103 45553568866213340426505155)
  ·
    refine ⟨68330353299320010639757733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45553568866213340426505155 68330353299320010639757733)
    ·
      refine ⟨12811941243622501994954575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68330353299320010639757733 12811941243622501994954575)
      ·
        refine ⟨19217911865433752992431863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12811941243622501994954575 19217911865433752992431863)
        ·
          refine ⟨28826867798150629488647795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19217911865433752992431863 28826867798150629488647795)
          ·
            refine ⟨43240301697225944232971693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28826867798150629488647795 43240301697225944232971693)
            ·
              refine ⟨16215113136459729087364385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43240301697225944232971693 16215113136459729087364385)
              ·
                refine ⟨12161334852344796815523289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16215113136459729087364385 12161334852344796815523289)
                ·
                  refine ⟨9121001139258597611642467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12161334852344796815523289 9121001139258597611642467)
                  ·
                    refine ⟨13681501708887896417463701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9121001139258597611642467 13681501708887896417463701)
                    ·
                      refine ⟨641320392604120144568611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13681501708887896417463701 641320392604120144568611)
                      ·
                        rfl

theorem cell23_1248967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 1, 6].length) (baseStart_1248967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248967 prefixEnd_1248967 := by exact prefixLift 1248967
  have htrace : WordTrace (prefixWord ++ tailWord_1248967) baseStart_1248967 baseEnd_1248967 := by
    simpa [prefixWord, tailWord_1248967, baseEnd_1248967] using wordTrace_append hprefix tailTrace_1248967
  have hstable : (prefixWord ++ tailWord_1248967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248967).length < 2 ^ (prefixWord ++ tailWord_1248967).sum := by decide
  have hdescent : baseEnd_1248967 < baseStart_1248967 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1248974 : List Nat := [4, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3]
def baseStart_1248974 : Nat := 118140960795 + 1248974 * 2 ^ 59
def prefixEnd_1248974 : Nat := 4983230072969 + 3 ^ 40 * 1248974 * 2
def baseEnd_1248974 : Nat := 641323986968701617181079

theorem tailTrace_1248974 : CollatzResearch.WordTrace tailWord_1248974 prefixEnd_1248974 641323986968701617181079 := by
  unfold tailWord_1248974
  simp only [CollatzResearch.WordTrace]
  refine ⟨5694228022148497577751247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30369216118125320414673317 5694228022148497577751247)
  ·
    refine ⟨8541342033222746366626871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5694228022148497577751247 8541342033222746366626871)
    ·
      refine ⟨12812013049834119549940307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541342033222746366626871 12812013049834119549940307)
      ·
        refine ⟨19218019574751179324910461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12812013049834119549940307 19218019574751179324910461)
        ·
          refine ⟨7206757340531692246841423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19218019574751179324910461 7206757340531692246841423)
          ·
            refine ⟨10810136010797538370262135, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7206757340531692246841423 10810136010797538370262135)
            ·
              refine ⟨16215204016196307555393203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10810136010797538370262135 16215204016196307555393203)
              ·
                refine ⟨24322806024294461333089805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16215204016196307555393203 24322806024294461333089805)
                ·
                  refine ⟨9121052259110422999908677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 24322806024294461333089805 9121052259110422999908677)
                  ·
                    refine ⟨1710197298583204312482877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9121052259110422999908677 1710197298583204312482877)
                    ·
                      refine ⟨641323986968701617181079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1710197298583204312482877 641323986968701617181079)
                      ·
                        rfl

theorem cell23_1248974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 1, 1, 1, 3, 4, 3].length) (baseStart_1248974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1248974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1248974 prefixEnd_1248974 := by exact prefixLift 1248974
  have htrace : WordTrace (prefixWord ++ tailWord_1248974) baseStart_1248974 baseEnd_1248974 := by
    simpa [prefixWord, tailWord_1248974, baseEnd_1248974] using wordTrace_append hprefix tailTrace_1248974
  have hstable : (prefixWord ++ tailWord_1248974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1248974).length < 2 ^ (prefixWord ++ tailWord_1248974).sum := by decide
  have hdescent : baseEnd_1248974 < baseStart_1248974 := by decide
  rcases family_descends (prefixWord ++ tailWord_1248974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249017 : List Nat := [1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 7]
def baseStart_1249017 : Nat := 118140960795 + 1249017 * 2 ^ 59
def prefixEnd_1249017 : Nat := 4983230072969 + 3 ^ 40 * 1249017 * 2
def baseEnd_1249017 : Nat := 641346066636844948943381

theorem tailTrace_1249017 : CollatzResearch.WordTrace tailWord_1249017 prefixEnd_1249017 641346066636844948943381 := by
  unfold tailWord_1249017
  simp only [CollatzResearch.WordTrace]
  refine ⟨45555392516032198965825305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30370261677354799310550203 45555392516032198965825305)
  ·
    refine ⟨34166544387024149224368979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45555392516032198965825305 34166544387024149224368979)
    ·
      refine ⟨51249816580536223836553469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34166544387024149224368979 51249816580536223836553469)
      ·
        refine ⟨19218681217701083938707551, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51249816580536223836553469 19218681217701083938707551)
        ·
          refine ⟨28828021826551625908061327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19218681217701083938707551 28828021826551625908061327)
          ·
            refine ⟨43242032739827438862091991, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28828021826551625908061327 43242032739827438862091991)
            ·
              refine ⟨64863049109741158293137987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43242032739827438862091991 64863049109741158293137987)
              ·
                refine ⟨97294573664611737439706981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64863049109741158293137987 97294573664611737439706981)
                ·
                  refine ⟨18242732562114700769945059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 97294573664611737439706981 18242732562114700769945059)
                  ·
                    refine ⟨27364098843172051154917589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 18242732562114700769945059 27364098843172051154917589)
                    ·
                      refine ⟨641346066636844948943381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27364098843172051154917589 641346066636844948943381)
                      ·
                        rfl

theorem cell23_1249017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 1, 1, 1, 4, 1, 7].length) (baseStart_1249017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249017 prefixEnd_1249017 := by exact prefixLift 1249017
  have htrace : WordTrace (prefixWord ++ tailWord_1249017) baseStart_1249017 baseEnd_1249017 := by
    simpa [prefixWord, tailWord_1249017, baseEnd_1249017] using wordTrace_append hprefix tailTrace_1249017
  have hstable : (prefixWord ++ tailWord_1249017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249017).length < 2 ^ (prefixWord ++ tailWord_1249017).sum := by decide
  have hdescent : baseEnd_1249017 < baseStart_1249017 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249021 : List Nat := [1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 3]
def baseStart_1249021 : Nat := 118140960795 + 1249021 * 2 ^ 59
def prefixEnd_1249021 : Nat := 4983230072969 + 3 ^ 40 * 1249021 * 2
def baseEnd_1249021 : Nat := 641348120559462933293363

theorem tailTrace_1249021 : CollatzResearch.WordTrace tailWord_1249021 prefixEnd_1249021 641348120559462933293363 := by
  unfold tailWord_1249021
  simp only [CollatzResearch.WordTrace]
  refine ⟨45555538408017707648970917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30370358938678471765980611 45555538408017707648970917)
  ·
    refine ⟨8541663451503320184182047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45555538408017707648970917 8541663451503320184182047)
    ·
      refine ⟨12812495177254980276273071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8541663451503320184182047 12812495177254980276273071)
      ·
        refine ⟨19218742765882470414409607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12812495177254980276273071 19218742765882470414409607)
        ·
          refine ⟨28828114148823705621614411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19218742765882470414409607 28828114148823705621614411)
          ·
            refine ⟨43242171223235558432421617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28828114148823705621614411 43242171223235558432421617)
            ·
              refine ⟨32431628417426668824316213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43242171223235558432421617 32431628417426668824316213)
              ·
                refine ⟨3040465164133750202279645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32431628417426668824316213 3040465164133750202279645)
                ·
                  refine ⟨1140174436550156325854867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3040465164133750202279645 1140174436550156325854867)
                  ·
                    refine ⟨1710261654825234488782301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140174436550156325854867 1710261654825234488782301)
                    ·
                      refine ⟨641348120559462933293363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1710261654825234488782301 641348120559462933293363)
                      ·
                        rfl

theorem cell23_1249021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 1, 2, 5, 3, 1, 3].length) (baseStart_1249021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249021 prefixEnd_1249021 := by exact prefixLift 1249021
  have htrace : WordTrace (prefixWord ++ tailWord_1249021) baseStart_1249021 baseEnd_1249021 := by
    simpa [prefixWord, tailWord_1249021, baseEnd_1249021] using wordTrace_append hprefix tailTrace_1249021
  have hstable : (prefixWord ++ tailWord_1249021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249021).length < 2 ^ (prefixWord ++ tailWord_1249021).sum := by decide
  have hdescent : baseEnd_1249021 < baseStart_1249021 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249028 : List Nat := [2, 3, 2, 2, 1, 4, 2, 1, 6]
def baseStart_1249028 : Nat := 118140960795 + 1249028 * 2 ^ 59
def prefixEnd_1249028 : Nat := 4983230072969 + 3 ^ 40 * 1249028 * 2
def baseEnd_1249028 : Nat := 71261301658227156211759

theorem tailTrace_1249028 : CollatzResearch.WordTrace tailWord_1249028 prefixEnd_1249028 71261301658227156211759 := by
  unfold tailWord_1249028
  simp only [CollatzResearch.WordTrace]
  refine ⟨22777896859496173922237869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30370529145994898562983825 22777896859496173922237869)
  ·
    refine ⟨8541711322311065220839201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22777896859496173922237869 8541711322311065220839201)
    ·
      refine ⟨6406283491733298915629401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8541711322311065220839201 6406283491733298915629401)
      ·
        refine ⟨4804712618799974186722051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6406283491733298915629401 4804712618799974186722051)
        ·
          refine ⟨7207068928199961280083077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4804712618799974186722051 7207068928199961280083077)
          ·
            refine ⟨1351325424037492740015577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7207068928199961280083077 1351325424037492740015577)
            ·
              refine ⟨1013494068028119555011683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351325424037492740015577 1013494068028119555011683)
              ·
                refine ⟨1520241102042179332517525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013494068028119555011683 1520241102042179332517525)
                ·
                  refine ⟨71261301658227156211759, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1520241102042179332517525 71261301658227156211759)
                  ·
                    rfl

theorem cell23_1249028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 4, 2, 1, 6].length) (baseStart_1249028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249028 prefixEnd_1249028 := by exact prefixLift 1249028
  have htrace : WordTrace (prefixWord ++ tailWord_1249028) baseStart_1249028 baseEnd_1249028 := by
    simpa [prefixWord, tailWord_1249028, baseEnd_1249028] using wordTrace_append hprefix tailTrace_1249028
  have hstable : (prefixWord ++ tailWord_1249028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249028).length < 2 ^ (prefixWord ++ tailWord_1249028).sum := by decide
  have hdescent : baseEnd_1249028 < baseStart_1249028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249058 : List Nat := [3, 3, 1, 1, 2, 1, 5, 1, 1, 5]
def baseStart_1249058 : Nat := 118140960795 + 1249058 * 2 ^ 59
def prefixEnd_1249058 : Nat := 4983230072969 + 3 ^ 40 * 1249058 * 2
def baseEnd_1249058 : Nat := 213789039781226429510231

theorem tailTrace_1249058 : CollatzResearch.WordTrace tailWord_1249058 prefixEnd_1249058 213789039781226429510231 := by
  unfold tailWord_1249058
  simp only [CollatzResearch.WordTrace]
  refine ⟨11389221977220915742016957, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30371258605922441978711885 11389221977220915742016957)
  ·
    refine ⟨4270958241457843403256359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11389221977220915742016957 4270958241457843403256359)
    ·
      refine ⟨6406437362186765104884539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4270958241457843403256359 6406437362186765104884539)
      ·
        refine ⟨9609656043280147657326809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6406437362186765104884539 9609656043280147657326809)
        ·
          refine ⟨7207242032460110742995107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9609656043280147657326809 7207242032460110742995107)
          ·
            refine ⟨10810863048690166114492661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207242032460110742995107 10810863048690166114492661)
            ·
              refine ⟨1013518410814703073233687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10810863048690166114492661 1013518410814703073233687)
              ·
                refine ⟨1520277616222054609850531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013518410814703073233687 1520277616222054609850531)
                ·
                  refine ⟨2280416424333081914775797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520277616222054609850531 2280416424333081914775797)
                  ·
                    refine ⟨213789039781226429510231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2280416424333081914775797 213789039781226429510231)
                    ·
                      rfl

theorem cell23_1249058_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 5, 1, 1, 5].length) (baseStart_1249058 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249058 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249058 prefixEnd_1249058 := by exact prefixLift 1249058
  have htrace : WordTrace (prefixWord ++ tailWord_1249058) baseStart_1249058 baseEnd_1249058 := by
    simpa [prefixWord, tailWord_1249058, baseEnd_1249058] using wordTrace_append hprefix tailTrace_1249058
  have hstable : (prefixWord ++ tailWord_1249058).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249058).length < 2 ^ (prefixWord ++ tailWord_1249058).sum := by decide
  have hdescent : baseEnd_1249058 < baseStart_1249058 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249058) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249078 : List Nat := [5, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4]
def baseStart_1249078 : Nat := 118140960795 + 1249078 * 2 ^ 59
def prefixEnd_1249078 : Nat := 4983230072969 + 3 ^ 40 * 1249078 * 2
def baseEnd_1249078 : Nat := 641377388956769210280601

theorem tailTrace_1249078 : CollatzResearch.WordTrace tailWord_1249078 prefixEnd_1249078 641377388956769210280601 := by
  unfold tailWord_1249078
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847351085550700398987243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30371744912540804255863925 2847351085550700398987243)
  ·
    refine ⟨4271026628326050598480865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847351085550700398987243 4271026628326050598480865)
    ·
      refine ⟨3203269971244537948860649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4271026628326050598480865 3203269971244537948860649)
      ·
        refine ⟨2402452478433403461645487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3203269971244537948860649 2402452478433403461645487)
        ·
          refine ⟨3603678717650105192468231, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2402452478433403461645487 3603678717650105192468231)
          ·
            refine ⟨5405518076475157788702347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3603678717650105192468231 5405518076475157788702347)
            ·
              refine ⟨8108277114712736683053521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5405518076475157788702347 8108277114712736683053521)
              ·
                refine ⟨6081207836034552512290141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8108277114712736683053521 6081207836034552512290141)
                ·
                  refine ⟨2280452938512957192108803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6081207836034552512290141 2280452938512957192108803)
                  ·
                    refine ⟨3420679407769435788163205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2280452938512957192108803 3420679407769435788163205)
                    ·
                      refine ⟨641377388956769210280601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3420679407769435788163205 641377388956769210280601)
                      ·
                        rfl

theorem cell23_1249078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 1, 1, 2, 3, 1, 4].length) (baseStart_1249078 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249078 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249078 prefixEnd_1249078 := by exact prefixLift 1249078
  have htrace : WordTrace (prefixWord ++ tailWord_1249078) baseStart_1249078 baseEnd_1249078 := by
    simpa [prefixWord, tailWord_1249078, baseEnd_1249078] using wordTrace_append hprefix tailTrace_1249078
  have hstable : (prefixWord ++ tailWord_1249078).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249078).length < 2 ^ (prefixWord ++ tailWord_1249078).sum := by decide
  have hdescent : baseEnd_1249078 < baseStart_1249078 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249084 : List Nat := [2, 2, 2, 2, 1, 1, 5, 8]
def baseStart_1249084 : Nat := 118140960795 + 1249084 * 2 ^ 59
def prefixEnd_1249084 : Nat := 4983230072969 + 3 ^ 40 * 1249084 * 2
def baseEnd_1249084 : Nat := 23754832216322080992799

theorem tailTrace_1249084 : CollatzResearch.WordTrace tailWord_1249084 prefixEnd_1249084 23754832216322080992799 := by
  unfold tailWord_1249084
  simp only [CollatzResearch.WordTrace]
  refine ⟨22778918103394734704257153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30371890804526312939009537 22778918103394734704257153)
  ·
    refine ⟨17084188577546051028192865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22778918103394734704257153 17084188577546051028192865)
    ·
      refine ⟨12813141433159538271144649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17084188577546051028192865 12813141433159538271144649)
      ·
        refine ⟨9609856074869653703358487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12813141433159538271144649 9609856074869653703358487)
        ·
          refine ⟨14414784112304480555037731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9609856074869653703358487 14414784112304480555037731)
          ·
            refine ⟨21622176168456720832556597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14414784112304480555037731 21622176168456720832556597)
            ·
              refine ⟨2027079015792817578052181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 21622176168456720832556597 2027079015792817578052181)
              ·
                refine ⟨23754832216322080992799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2027079015792817578052181 23754832216322080992799)
                ·
                  rfl

theorem cell23_1249084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 5, 8].length) (baseStart_1249084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249084 prefixEnd_1249084 := by exact prefixLift 1249084
  have htrace : WordTrace (prefixWord ++ tailWord_1249084) baseStart_1249084 baseEnd_1249084 := by
    simpa [prefixWord, tailWord_1249084, baseEnd_1249084] using wordTrace_append hprefix tailTrace_1249084
  have hstable : (prefixWord ++ tailWord_1249084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249084).length < 2 ^ (prefixWord ++ tailWord_1249084).sum := by decide
  have hdescent : baseEnd_1249084 < baseStart_1249084 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249091 : List Nat := [1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 4]
def baseStart_1249091 : Nat := 118140960795 + 1249091 * 2 ^ 59
def prefixEnd_1249091 : Nat := 4983230072969 + 3 ^ 40 * 1249091 * 2
def baseEnd_1249091 : Nat := 641384064205277659418041

theorem tailTrace_1249091 : CollatzResearch.WordTrace tailWord_1249091 prefixEnd_1249091 641384064205277659418041 := by
  unfold tailWord_1249091
  simp only [CollatzResearch.WordTrace]
  refine ⟨45558091517764109604019127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30372061011842739736012751 45558091517764109604019127)
  ·
    refine ⟨68337137276646164406028691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45558091517764109604019127 68337137276646164406028691)
    ·
      refine ⟨102505705914969246609043037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68337137276646164406028691 102505705914969246609043037)
      ·
        refine ⟨38439639718113467478391139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102505705914969246609043037 38439639718113467478391139)
        ·
          refine ⟨57659459577170201217586709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38439639718113467478391139 57659459577170201217586709)
          ·
            refine ⟨2702787167679853182074377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 57659459577170201217586709 2702787167679853182074377)
            ·
              refine ⟨2027090375759889886555783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2702787167679853182074377 2027090375759889886555783)
              ·
                refine ⟨3040635563639834829833675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027090375759889886555783 3040635563639834829833675)
                ·
                  refine ⟨4560953345459752244750513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040635563639834829833675 4560953345459752244750513)
                  ·
                    refine ⟨3420715009094814183562885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4560953345459752244750513 3420715009094814183562885)
                    ·
                      refine ⟨641384064205277659418041, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3420715009094814183562885 641384064205277659418041)
                      ·
                        rfl

theorem cell23_1249091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 6, 2, 1, 1, 2, 4].length) (baseStart_1249091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249091 prefixEnd_1249091 := by exact prefixLift 1249091
  have htrace : WordTrace (prefixWord ++ tailWord_1249091) baseStart_1249091 baseEnd_1249091 := by
    simpa [prefixWord, tailWord_1249091, baseEnd_1249091] using wordTrace_append hprefix tailTrace_1249091
  have hstable : (prefixWord ++ tailWord_1249091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249091).length < 2 ^ (prefixWord ++ tailWord_1249091).sum := by decide
  have hdescent : baseEnd_1249091 < baseStart_1249091 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249128 : List Nat := [2, 1, 4, 2, 1, 1, 3, 1, 4, 1, 3]
def baseStart_1249128 : Nat := 118140960795 + 1249128 * 2 ^ 59
def prefixEnd_1249128 : Nat := 4983230072969 + 3 ^ 40 * 1249128 * 2
def baseEnd_1249128 : Nat := 641403062989494014655371

theorem tailTrace_1249128 : CollatzResearch.WordTrace tailWord_1249128 prefixEnd_1249128 641403062989494014655371 := by
  unfold tailWord_1249128
  simp only [CollatzResearch.WordTrace]
  refine ⟨22779720509315032461558019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30372960679086709948744025 22779720509315032461558019)
  ·
    refine ⟨34169580763972548692337029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22779720509315032461558019 34169580763972548692337029)
    ·
      refine ⟨6406796393244852879813193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34169580763972548692337029 6406796393244852879813193)
      ·
        refine ⟨4805097294933639659859895, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6406796393244852879813193 4805097294933639659859895)
        ·
          refine ⟨7207645942400459489789843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4805097294933639659859895 7207645942400459489789843)
          ·
            refine ⟨10811468913600689234684765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7207645942400459489789843 10811468913600689234684765)
            ·
              refine ⟨4054300842600258463006787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10811468913600689234684765 4054300842600258463006787)
              ·
                refine ⟨6081451263900387694510181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4054300842600258463006787 6081451263900387694510181)
                ·
                  refine ⟨1140272111981322692720659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6081451263900387694510181 1140272111981322692720659)
                  ·
                    refine ⟨1710408167971984039080989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140272111981322692720659 1710408167971984039080989)
                    ·
                      refine ⟨641403062989494014655371, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1710408167971984039080989 641403062989494014655371)
                      ·
                        rfl

theorem cell23_1249128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 3, 1, 4, 1, 3].length) (baseStart_1249128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249128 prefixEnd_1249128 := by exact prefixLift 1249128
  have htrace : WordTrace (prefixWord ++ tailWord_1249128) baseStart_1249128 baseEnd_1249128 := by
    simpa [prefixWord, tailWord_1249128, baseEnd_1249128] using wordTrace_append hprefix tailTrace_1249128
  have hstable : (prefixWord ++ tailWord_1249128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249128).length < 2 ^ (prefixWord ++ tailWord_1249128).sum := by decide
  have hdescent : baseEnd_1249128 < baseStart_1249128 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249142 : List Nat := [5, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4]
def baseStart_1249142 : Nat := 118140960795 + 1249142 * 2 ^ 59
def prefixEnd_1249142 : Nat := 4983230072969 + 3 ^ 40 * 1249142 * 2
def baseEnd_1249142 : Nat := 641410251718656959880307

theorem tailTrace_1249142 : CollatzResearch.WordTrace tailWord_1249142 prefixEnd_1249142 641410251718656959880307 := by
  unfold tailWord_1249142
  simp only [CollatzResearch.WordTrace]
  refine ⟨2847496977536209082132855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30373301093719563542750453 2847496977536209082132855)
  ·
    refine ⟨4271245466304313623199283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2847496977536209082132855 4271245466304313623199283)
    ·
      refine ⟨6406868199456470434798925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4271245466304313623199283 6406868199456470434798925)
      ·
        refine ⟨2402575574796176413049597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6406868199456470434798925 2402575574796176413049597)
        ·
          refine ⟨900965840548566154893599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2402575574796176413049597 900965840548566154893599)
          ·
            refine ⟨1351448760822849232340399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 900965840548566154893599 1351448760822849232340399)
            ·
              refine ⟨2027173141234273848510599, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351448760822849232340399 2027173141234273848510599)
              ·
                refine ⟨3040759711851410772765899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027173141234273848510599 3040759711851410772765899)
                ·
                  refine ⟨4561139567777116159148849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3040759711851410772765899 4561139567777116159148849)
                  ·
                    refine ⟨3420854675832837119361637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4561139567777116159148849 3420854675832837119361637)
                    ·
                      refine ⟨641410251718656959880307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3420854675832837119361637 641410251718656959880307)
                      ·
                        rfl

theorem cell23_1249142_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 3, 1, 1, 1, 1, 2, 4].length) (baseStart_1249142 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249142 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249142 prefixEnd_1249142 := by exact prefixLift 1249142
  have htrace : WordTrace (prefixWord ++ tailWord_1249142) baseStart_1249142 baseEnd_1249142 := by
    simpa [prefixWord, tailWord_1249142, baseEnd_1249142] using wordTrace_append hprefix tailTrace_1249142
  have hstable : (prefixWord ++ tailWord_1249142).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249142).length < 2 ^ (prefixWord ++ tailWord_1249142).sum := by decide
  have hdescent : baseEnd_1249142 < baseStart_1249142 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249142) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249145 : List Nat := [1, 2, 1, 3, 2, 2, 5, 1, 2, 1, 3]
def baseStart_1249145 : Nat := 118140960795 + 1249145 * 2 ^ 59
def prefixEnd_1249145 : Nat := 4983230072969 + 3 ^ 40 * 1249145 * 2
def baseEnd_1249145 : Nat := 641411792160620448142793

theorem tailTrace_1249145 : CollatzResearch.WordTrace tailWord_1249145 prefixEnd_1249145 641411792160620448142793 := by
  unfold tailWord_1249145
  simp only [CollatzResearch.WordTrace]
  refine ⟨45560061059568476826484889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30373374039712317884323259 45560061059568476826484889)
  ·
    refine ⟨34170045794676357619863667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45560061059568476826484889 34170045794676357619863667)
    ·
      refine ⟨51255068692014536429795501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34170045794676357619863667 51255068692014536429795501)
      ·
        refine ⟨19220650759505451161173313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51255068692014536429795501 19220650759505451161173313)
        ·
          refine ⟨14415488069629088370879985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19220650759505451161173313 14415488069629088370879985)
          ·
            refine ⟨10811616052221816278159989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14415488069629088370879985 10811616052221816278159989)
            ·
              refine ⟨1013589004895795276077499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 10811616052221816278159989 1013589004895795276077499)
              ·
                refine ⟨1520383507343692914116249, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013589004895795276077499 1520383507343692914116249)
                ·
                  refine ⟨1140287630507769685587187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1520383507343692914116249 1140287630507769685587187)
                  ·
                    refine ⟨1710431445761654528380781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140287630507769685587187 1710431445761654528380781)
                    ·
                      refine ⟨641411792160620448142793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1710431445761654528380781 641411792160620448142793)
                      ·
                        rfl

theorem cell23_1249145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 2, 5, 1, 2, 1, 3].length) (baseStart_1249145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249145 prefixEnd_1249145 := by exact prefixLift 1249145
  have htrace : WordTrace (prefixWord ++ tailWord_1249145) baseStart_1249145 baseEnd_1249145 := by
    simpa [prefixWord, tailWord_1249145, baseEnd_1249145] using wordTrace_append hprefix tailTrace_1249145
  have hstable : (prefixWord ++ tailWord_1249145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249145).length < 2 ^ (prefixWord ++ tailWord_1249145).sum := by decide
  have hdescent : baseEnd_1249145 < baseStart_1249145 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249155 : List Nat := [1, 1, 1, 3, 4, 3, 2, 2, 1, 3, 2]
def baseStart_1249155 : Nat := 118140960795 + 1249155 * 2 ^ 59
def prefixEnd_1249155 : Nat := 4983230072969 + 3 ^ 40 * 1249155 * 2
def baseEnd_1249155 : Nat := 641416926967165409017747

theorem tailTrace_1249155 : CollatzResearch.WordTrace tailWord_1249155 prefixEnd_1249155 641416926967165409017747 := by
  unfold tailWord_1249155
  simp only [CollatzResearch.WordTrace]
  refine ⟨45560425789532248534348919, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30373617193021499022899279 45560425789532248534348919)
  ·
    refine ⟨68340638684298372801523379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45560425789532248534348919 68340638684298372801523379)
    ·
      refine ⟨102510958026447559202285069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68340638684298372801523379 102510958026447559202285069)
      ·
        refine ⟨38441609259917834700856901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102510958026447559202285069 38441609259917834700856901)
        ·
          refine ⟨7207801736234594006410669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38441609259917834700856901 7207801736234594006410669)
          ·
            refine ⟨2702925651087972752404001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7207801736234594006410669 2702925651087972752404001)
            ·
              refine ⟨2027194238315979564303001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2702925651087972752404001 2027194238315979564303001)
              ·
                refine ⟨1520395678736984673227251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027194238315979564303001 1520395678736984673227251)
                ·
                  refine ⟨2280593518105477009840877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520395678736984673227251 2280593518105477009840877)
                  ·
                    refine ⟨855222569289553878690329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2280593518105477009840877 855222569289553878690329)
                    ·
                      refine ⟨641416926967165409017747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855222569289553878690329 641416926967165409017747)
                      ·
                        rfl

theorem cell23_1249155_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 4, 3, 2, 2, 1, 3, 2].length) (baseStart_1249155 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249155 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249155 prefixEnd_1249155 := by exact prefixLift 1249155
  have htrace : WordTrace (prefixWord ++ tailWord_1249155) baseStart_1249155 baseEnd_1249155 := by
    simpa [prefixWord, tailWord_1249155, baseEnd_1249155] using wordTrace_append hprefix tailTrace_1249155
  have hstable : (prefixWord ++ tailWord_1249155).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249155).length < 2 ^ (prefixWord ++ tailWord_1249155).sum := by decide
  have hdescent : baseEnd_1249155 < baseStart_1249155 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249155) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249168 : List Nat := [2, 1, 1, 1, 1, 1, 2, 6, 4, 2, 2]
def baseStart_1249168 : Nat := 118140960795 + 1249168 * 2 ^ 59
def prefixEnd_1249168 : Nat := 4983230072969 + 3 ^ 40 * 1249168 * 2
def baseEnd_1249168 : Nat := 641423602215673858155187

theorem tailTrace_1249168 : CollatzResearch.WordTrace tailWord_1249168 prefixEnd_1249168 641423602215673858155187 := by
  unfold tailWord_1249168
  simp only [CollatzResearch.WordTrace]
  refine ⟨22780449969242575877286079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30373933292323434503048105 22780449969242575877286079)
  ·
    refine ⟨34170674953863863815929119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22780449969242575877286079 34170674953863863815929119)
    ·
      refine ⟨51256012430795795723893679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34170674953863863815929119 51256012430795795723893679)
      ·
        refine ⟨76884018646193693585840519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51256012430795795723893679 76884018646193693585840519)
        ·
          refine ⟨115326027969290540378760779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76884018646193693585840519 115326027969290540378760779)
          ·
            refine ⟨172989041953935810568141169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115326027969290540378760779 172989041953935810568141169)
            ·
              refine ⟨129741781465451857926105877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 172989041953935810568141169 129741781465451857926105877)
              ·
                refine ⟨6081646006193055840286213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 129741781465451857926105877 6081646006193055840286213)
                ·
                  refine ⟨1140308626161197970053665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6081646006193055840286213 1140308626161197970053665)
                  ·
                    refine ⟨855231469620898477540249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1140308626161197970053665 855231469620898477540249)
                    ·
                      refine ⟨641423602215673858155187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855231469620898477540249 641423602215673858155187)
                      ·
                        rfl

theorem cell23_1249168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 2, 6, 4, 2, 2].length) (baseStart_1249168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249168 prefixEnd_1249168 := by exact prefixLift 1249168
  have htrace : WordTrace (prefixWord ++ tailWord_1249168) baseStart_1249168 baseEnd_1249168 := by
    simpa [prefixWord, tailWord_1249168, baseEnd_1249168] using wordTrace_append hprefix tailTrace_1249168
  have hstable : (prefixWord ++ tailWord_1249168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249168).length < 2 ^ (prefixWord ++ tailWord_1249168).sum := by decide
  have hdescent : baseEnd_1249168 < baseStart_1249168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249184 : List Nat := [2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9]
def baseStart_1249184 : Nat := 118140960795 + 1249184 * 2 ^ 59
def prefixEnd_1249184 : Nat := 4983230072969 + 3 ^ 40 * 1249184 * 2
def baseEnd_1249184 : Nat := 641431817906145795555113

theorem tailTrace_1249184 : CollatzResearch.WordTrace tailWord_1249184 prefixEnd_1249184 641431817906145795555113 := by
  unfold tailWord_1249184
  simp only [CollatzResearch.WordTrace]
  refine ⟨22780741753213593243577303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30374322337618124324769737 22780741753213593243577303)
  ·
    refine ⟨34171112629820389865365955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22780741753213593243577303 34171112629820389865365955)
    ·
      refine ⟨51256668944730584798048933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34171112629820389865365955 51256668944730584798048933)
      ·
        refine ⟨9610625427136984649634175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51256668944730584798048933 9610625427136984649634175)
        ·
          refine ⟨14415938140705476974451263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9610625427136984649634175 14415938140705476974451263)
          ·
            refine ⟨21623907211058215461676895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14415938140705476974451263 21623907211058215461676895)
            ·
              refine ⟨32435860816587323192515343, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21623907211058215461676895 32435860816587323192515343)
              ·
                refine ⟨48653791224880984788773015, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32435860816587323192515343 48653791224880984788773015)
                ·
                  refine ⟨72980686837321477183159523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48653791224880984788773015 72980686837321477183159523)
                  ·
                    refine ⟨109471030255982215774739285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 72980686837321477183159523 109471030255982215774739285)
                    ·
                      refine ⟨641431817906145795555113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 109471030255982215774739285 641431817906145795555113)
                      ·
                        rfl

theorem cell23_1249184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 1, 1, 1, 1, 9].length) (baseStart_1249184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249184 prefixEnd_1249184 := by exact prefixLift 1249184
  have htrace : WordTrace (prefixWord ++ tailWord_1249184) baseStart_1249184 baseEnd_1249184 := by
    simpa [prefixWord, tailWord_1249184, baseEnd_1249184] using wordTrace_append hprefix tailTrace_1249184
  have hstable : (prefixWord ++ tailWord_1249184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249184).length < 2 ^ (prefixWord ++ tailWord_1249184).sum := by decide
  have hdescent : baseEnd_1249184 < baseStart_1249184 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249242 : List Nat := [3, 1, 1, 2, 5, 2, 2, 2, 5]
def baseStart_1249242 : Nat := 118140960795 + 1249242 * 2 ^ 59
def prefixEnd_1249242 : Nat := 4983230072969 + 3 ^ 40 * 1249242 * 2
def baseEnd_1249242 : Nat := 71273511087122952069983

theorem tailTrace_1249242 : CollatzResearch.WordTrace tailWord_1249242 prefixEnd_1249242 71273511087122952069983 := by
  unfold tailWord_1249242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11390899735054265598191495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30375732626811374928510653 11390899735054265598191495)
  ·
    refine ⟨17086349602581398397287243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11390899735054265598191495 17086349602581398397287243)
    ·
      refine ⟨25629524403872097595930865, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17086349602581398397287243 25629524403872097595930865)
      ·
        refine ⟨19222143302904073196948149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25629524403872097595930865 19222143302904073196948149)
        ·
          refine ⟨1802075934647256862213889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19222143302904073196948149 1802075934647256862213889)
          ·
            refine ⟨1351556950985442646660417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1802075934647256862213889 1351556950985442646660417)
            ·
              refine ⟨1013667713239081984995313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351556950985442646660417 1013667713239081984995313)
              ·
                refine ⟨760250784929311488746485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1013667713239081984995313 760250784929311488746485)
                ·
                  refine ⟨71273511087122952069983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760250784929311488746485 71273511087122952069983)
                  ·
                    rfl

theorem cell23_1249242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 2, 2, 2, 5].length) (baseStart_1249242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249242 prefixEnd_1249242 := by exact prefixLift 1249242
  have htrace : WordTrace (prefixWord ++ tailWord_1249242) baseStart_1249242 baseEnd_1249242 := by
    simpa [prefixWord, tailWord_1249242, baseEnd_1249242] using wordTrace_append hprefix tailTrace_1249242
  have hstable : (prefixWord ++ tailWord_1249242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249242).length < 2 ^ (prefixWord ++ tailWord_1249242).sum := by decide
  have hdescent : baseEnd_1249242 < baseStart_1249242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249281 : List Nat := [1, 2, 4, 1, 2, 1, 2, 2, 8]
def baseStart_1249281 : Nat := 118140960795 + 1249281 * 2 ^ 59
def prefixEnd_1249281 : Nat := 4983230072969 + 3 ^ 40 * 1249281 * 2
def baseEnd_1249281 : Nat := 71275736169959101782463

theorem tailTrace_1249281 : CollatzResearch.WordTrace tailWord_1249281 prefixEnd_1249281 71275736169959101782463 := by
  unfold tailWord_1249281
  simp only [CollatzResearch.WordTrace]
  refine ⟨45565021387075772053435697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30376680924717181368957131 45565021387075772053435697)
  ·
    refine ⟨34173766040306829040076773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45565021387075772053435697 34173766040306829040076773)
    ·
      refine ⟨6407581132557530445014395, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34173766040306829040076773 6407581132557530445014395)
      ·
        refine ⟨9611371698836295667521593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6407581132557530445014395 9611371698836295667521593)
        ·
          refine ⟨7208528774127221750641195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9611371698836295667521593 7208528774127221750641195)
          ·
            refine ⟨10812793161190832625961793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7208528774127221750641195 10812793161190832625961793)
            ·
              refine ⟨8109594870893124469471345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10812793161190832625961793 8109594870893124469471345)
              ·
                refine ⟨6082196153169843352103509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8109594870893124469471345 6082196153169843352103509)
                ·
                  refine ⟨71275736169959101782463, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6082196153169843352103509 71275736169959101782463)
                  ·
                    rfl

theorem cell23_1249281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 2, 2, 8].length) (baseStart_1249281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249281 prefixEnd_1249281 := by exact prefixLift 1249281
  have htrace : WordTrace (prefixWord ++ tailWord_1249281) baseStart_1249281 baseEnd_1249281 := by
    simpa [prefixWord, tailWord_1249281, baseEnd_1249281] using wordTrace_append hprefix tailTrace_1249281
  have hstable : (prefixWord ++ tailWord_1249281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249281).length < 2 ^ (prefixWord ++ tailWord_1249281).sum := by decide
  have hdescent : baseEnd_1249281 < baseStart_1249281 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249285 : List Nat := [1, 3, 1, 1, 2, 4, 1, 5, 1, 4]
def baseStart_1249285 : Nat := 118140960795 + 1249285 * 2 ^ 59
def prefixEnd_1249285 : Nat := 4983230072969 + 3 ^ 40 * 1249285 * 2
def baseEnd_1249285 : Nat := 213827893150749966797383

theorem tailTrace_1249285 : CollatzResearch.WordTrace tailWord_1249285 prefixEnd_1249285 213827893150749966797383 := by
  unfold tailWord_1249285
  simp only [CollatzResearch.WordTrace]
  refine ⟨45565167279061280736581309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30376778186040853824387539 45565167279061280736581309)
  ·
    refine ⟨17086937729647980276217991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45565167279061280736581309 17086937729647980276217991)
    ·
      refine ⟨25630406594471970414326987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17086937729647980276217991 25630406594471970414326987)
      ·
        refine ⟨38445609891707955621490481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25630406594471970414326987 38445609891707955621490481)
        ·
          refine ⟨28834207418780966716117861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38445609891707955621490481 28834207418780966716117861)
          ·
            refine ⟨5406413891021431259272099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28834207418780966716117861 5406413891021431259272099)
            ·
              refine ⟨8109620836532146888908149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5406413891021431259272099 8109620836532146888908149)
              ·
                refine ⟨760276953424888770835139, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8109620836532146888908149 760276953424888770835139)
                ·
                  refine ⟨1140415430137333156252709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760276953424888770835139 1140415430137333156252709)
                  ·
                    refine ⟨213827893150749966797383, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140415430137333156252709 213827893150749966797383)
                    ·
                      rfl

theorem cell23_1249285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 4, 1, 5, 1, 4].length) (baseStart_1249285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249285 prefixEnd_1249285 := by exact prefixLift 1249285
  have htrace : WordTrace (prefixWord ++ tailWord_1249285) baseStart_1249285 baseEnd_1249285 := by
    simpa [prefixWord, tailWord_1249285, baseEnd_1249285] using wordTrace_append hprefix tailTrace_1249285
  have hstable : (prefixWord ++ tailWord_1249285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249285).length < 2 ^ (prefixWord ++ tailWord_1249285).sum := by decide
  have hdescent : baseEnd_1249285 < baseStart_1249285 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249328 : List Nat := [2, 1, 1, 1, 2, 5, 1, 4, 1, 5]
def baseStart_1249328 : Nat := 118140960795 + 1249328 * 2 ^ 59
def prefixEnd_1249328 : Nat := 4983230072969 + 3 ^ 40 * 1249328 * 2
def baseEnd_1249328 : Nat := 213835253040131077384817

theorem tailTrace_1249328 : CollatzResearch.WordTrace tailWord_1249328 prefixEnd_1249328 213835253040131077384817 := by
  unfold tailWord_1249328
  simp only [CollatzResearch.WordTrace]
  refine ⟨22783367808952749540198319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30377823745270332720264425 22783367808952749540198319)
  ·
    refine ⟨34175051713429124310297479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22783367808952749540198319 34175051713429124310297479)
    ·
      refine ⟨51262577570143686465446219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34175051713429124310297479 51262577570143686465446219)
      ·
        refine ⟨76893866355215529698169329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51262577570143686465446219 76893866355215529698169329)
        ·
          refine ⟨57670399766411647273626997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76893866355215529698169329 57670399766411647273626997)
          ·
            refine ⟨5406599978101091931902531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57670399766411647273626997 5406599978101091931902531)
            ·
              refine ⟨8109899967151637897853797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5406599978101091931902531 8109899967151637897853797)
              ·
                refine ⟨1520606243840932105847587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8109899967151637897853797 1520606243840932105847587)
                ·
                  refine ⟨2280909365761398158771381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520606243840932105847587 2280909365761398158771381)
                  ·
                    refine ⟨213835253040131077384817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2280909365761398158771381 213835253040131077384817)
                    ·
                      rfl

theorem cell23_1249328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 4, 1, 5].length) (baseStart_1249328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249328 prefixEnd_1249328 := by exact prefixLift 1249328
  have htrace : WordTrace (prefixWord ++ tailWord_1249328) baseStart_1249328 baseEnd_1249328 := by
    simpa [prefixWord, tailWord_1249328, baseEnd_1249328] using wordTrace_append hprefix tailTrace_1249328
  have hstable : (prefixWord ++ tailWord_1249328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249328).length < 2 ^ (prefixWord ++ tailWord_1249328).sum := by decide
  have hdescent : baseEnd_1249328 < baseStart_1249328 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249345 : List Nat := [1, 2, 5, 1, 2, 1, 2, 3, 1, 5]
def baseStart_1249345 : Nat := 118140960795 + 1249345 * 2 ^ 59
def prefixEnd_1249345 : Nat := 4983230072969 + 3 ^ 40 * 1249345 * 2
def baseEnd_1249345 : Nat := 213838162763839888547291

theorem tailTrace_1249345 : CollatzResearch.WordTrace tailWord_1249345 prefixEnd_1249345 213838162763839888547291 := by
  unfold tailWord_1249345
  simp only [CollatzResearch.WordTrace]
  refine ⟨45567355658843910983765489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30378237105895940655843659 45567355658843910983765489)
  ·
    refine ⟨34175516744132933237824117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45567355658843910983765489 34175516744132933237824117)
    ·
      refine ⟨3203954694762462491046011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34175516744132933237824117 3203954694762462491046011)
      ·
        refine ⟨4805932042143693736569017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3203954694762462491046011 4805932042143693736569017)
        ·
          refine ⟨3604449031607770302426763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4805932042143693736569017 3604449031607770302426763)
          ·
            refine ⟨5406673547411655453640145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3604449031607770302426763 5406673547411655453640145)
            ·
              refine ⟨4055005160558741590230109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5406673547411655453640145 4055005160558741590230109)
              ·
                refine ⟨1520626935209528096336291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4055005160558741590230109 1520626935209528096336291)
                ·
                  refine ⟨2280940402814292144504437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1520626935209528096336291 2280940402814292144504437)
                  ·
                    refine ⟨213838162763839888547291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2280940402814292144504437 213838162763839888547291)
                    ·
                      rfl

theorem cell23_1249345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 3, 1, 5].length) (baseStart_1249345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249345 prefixEnd_1249345 := by exact prefixLift 1249345
  have htrace : WordTrace (prefixWord ++ tailWord_1249345) baseStart_1249345 baseEnd_1249345 := by
    simpa [prefixWord, tailWord_1249345, baseEnd_1249345] using wordTrace_append hprefix tailTrace_1249345
  have hstable : (prefixWord ++ tailWord_1249345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249345).length < 2 ^ (prefixWord ++ tailWord_1249345).sum := by decide
  have hdescent : baseEnd_1249345 < baseStart_1249345 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249368 : List Nat := [2, 1, 2, 2, 1, 4, 2, 2, 1, 1, 5]
def baseStart_1249368 : Nat := 118140960795 + 1249368 * 2 ^ 59
def prefixEnd_1249368 : Nat := 4983230072969 + 3 ^ 40 * 1249368 * 2
def baseEnd_1249368 : Nat := 641526298346573075654267

theorem tailTrace_1249368 : CollatzResearch.WordTrace tailWord_1249368 prefixEnd_1249368 641526298346573075654267 := by
  unfold tailWord_1249368
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784097268880292955926379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30378796358507057274568505 22784097268880292955926379)
  ·
    refine ⟨34176145903320439433889569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22784097268880292955926379 34176145903320439433889569)
    ·
      refine ⟨25632109427490329575417177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34176145903320439433889569 25632109427490329575417177)
      ·
        refine ⟨19224082070617747181562883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25632109427490329575417177 19224082070617747181562883)
        ·
          refine ⟨28836123105926620772344325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19224082070617747181562883 28836123105926620772344325)
          ·
            refine ⟨5406773082361241394814561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28836123105926620772344325 5406773082361241394814561)
            ·
              refine ⟨4055079811770931046110921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5406773082361241394814561 4055079811770931046110921)
              ·
                refine ⟨3041309858828198284583191, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4055079811770931046110921 3041309858828198284583191)
                ·
                  refine ⟨4561964788242297426874787, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041309858828198284583191 4561964788242297426874787)
                  ·
                    refine ⟨6842947182363446140312181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4561964788242297426874787 6842947182363446140312181)
                    ·
                      refine ⟨641526298346573075654267, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6842947182363446140312181 641526298346573075654267)
                      ·
                        rfl

theorem cell23_1249368_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 4, 2, 2, 1, 1, 5].length) (baseStart_1249368 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249368 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249368 prefixEnd_1249368 := by exact prefixLift 1249368
  have htrace : WordTrace (prefixWord ++ tailWord_1249368) baseStart_1249368 baseEnd_1249368 := by
    simpa [prefixWord, tailWord_1249368, baseEnd_1249368] using wordTrace_append hprefix tailTrace_1249368
  have hstable : (prefixWord ++ tailWord_1249368).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249368).length < 2 ^ (prefixWord ++ tailWord_1249368).sum := by decide
  have hdescent : baseEnd_1249368 < baseStart_1249368 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249368) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249415 : List Nat := [1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 3]
def baseStart_1249415 : Nat := 118140960795 + 1249415 * 2 ^ 59
def prefixEnd_1249415 : Nat := 4983230072969 + 3 ^ 40 * 1249415 * 2
def baseEnd_1249415 : Nat := 641550431937334391766551

theorem tailTrace_1249415 : CollatzResearch.WordTrace tailWord_1249415 prefixEnd_1249415 641550431937334391766551 := by
  unfold tailWord_1249415
  simp only [CollatzResearch.WordTrace]
  refine ⟨45569908768590312938813699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30379939179060208625875799 45569908768590312938813699)
  ·
    refine ⟨68354863152885469408220549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45569908768590312938813699 68354863152885469408220549)
    ·
      refine ⟨12816536841166025514041353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68354863152885469408220549 12816536841166025514041353)
      ·
        refine ⟨9612402630874519135531015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12816536841166025514041353 9612402630874519135531015)
        ·
          refine ⟨14418603946311778703296523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9612402630874519135531015 14418603946311778703296523)
          ·
            refine ⟨21627905919467668054944785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14418603946311778703296523 21627905919467668054944785)
            ·
              refine ⟨16220929439600751041208589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21627905919467668054944785 16220929439600751041208589)
              ·
                refine ⟨6082848539850281640453221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16220929439600751041208589 6082848539850281640453221)
                ·
                  refine ⟨1140534101221927807584979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6082848539850281640453221 1140534101221927807584979)
                  ·
                    refine ⟨1710801151832891711377469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1140534101221927807584979 1710801151832891711377469)
                    ·
                      refine ⟨641550431937334391766551, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1710801151832891711377469 641550431937334391766551)
                      ·
                        rfl

theorem cell23_1249415_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 3, 4, 1, 3].length) (baseStart_1249415 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249415 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249415 prefixEnd_1249415 := by exact prefixLift 1249415
  have htrace : WordTrace (prefixWord ++ tailWord_1249415) baseStart_1249415 baseEnd_1249415 := by
    simpa [prefixWord, tailWord_1249415, baseEnd_1249415] using wordTrace_append hprefix tailTrace_1249415
  have hstable : (prefixWord ++ tailWord_1249415).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249415).length < 2 ^ (prefixWord ++ tailWord_1249415).sum := by decide
  have hdescent : baseEnd_1249415 < baseStart_1249415 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249415) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249416 : List Nat := [2, 1, 3, 4, 1, 2, 1, 4, 1, 2, 2]
def baseStart_1249416 : Nat := 118140960795 + 1249416 * 2 ^ 59
def prefixEnd_1249416 : Nat := 4983230072969 + 3 ^ 40 * 1249416 * 2
def baseEnd_1249416 : Nat := 641550945417988887854047

theorem tailTrace_1249416 : CollatzResearch.WordTrace tailWord_1249416 prefixEnd_1249416 641550945417988887854047 := by
  unfold tailWord_1249416
  simp only [CollatzResearch.WordTrace]
  refine ⟨22784972620793345054800051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30379963494391126739733401 22784972620793345054800051)
  ·
    refine ⟨34177458931190017582200077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22784972620793345054800051 34177458931190017582200077)
    ·
      refine ⟨12816547099196256593325029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34177458931190017582200077 12816547099196256593325029)
      ·
        refine ⟨2403102581099298111248443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12816547099196256593325029 2403102581099298111248443)
        ·
          refine ⟨3604653871648947166872665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2403102581099298111248443 3604653871648947166872665)
          ·
            refine ⟨2703490403736710375154499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3604653871648947166872665 2703490403736710375154499)
            ·
              refine ⟨4055235605605065562731749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2703490403736710375154499 4055235605605065562731749)
              ·
                refine ⟨760356676050949793012203, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4055235605605065562731749 760356676050949793012203)
                ·
                  refine ⟨1140535014076424689518305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760356676050949793012203 1140535014076424689518305)
                  ·
                    refine ⟨855401260557318517138729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1140535014076424689518305 855401260557318517138729)
                    ·
                      refine ⟨641550945417988887854047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855401260557318517138729 641550945417988887854047)
                      ·
                        rfl

theorem cell23_1249416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 1, 2, 1, 4, 1, 2, 2].length) (baseStart_1249416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249416 prefixEnd_1249416 := by exact prefixLift 1249416
  have htrace : WordTrace (prefixWord ++ tailWord_1249416) baseStart_1249416 baseEnd_1249416 := by
    simpa [prefixWord, tailWord_1249416, baseEnd_1249416] using wordTrace_append hprefix tailTrace_1249416
  have hstable : (prefixWord ++ tailWord_1249416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249416).length < 2 ^ (prefixWord ++ tailWord_1249416).sum := by decide
  have hdescent : baseEnd_1249416 < baseStart_1249416 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249418 : List Nat := [3, 1, 2, 3, 1, 2, 1, 1, 2, 7]
def baseStart_1249418 : Nat := 118140960795 + 1249418 * 2 ^ 59
def prefixEnd_1249418 : Nat := 4983230072969 + 3 ^ 40 * 1249418 * 2
def baseEnd_1249418 : Nat := 213850657459765960009679

theorem tailTrace_1249418 : CollatzResearch.WordTrace tailWord_1249418 prefixEnd_1249418 213850657459765960009679 := by
  unfold tailWord_1249418
  simp only [CollatzResearch.WordTrace]
  refine ⟨11392504546894861112793227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30380012125052962967448605 11392504546894861112793227)
  ·
    refine ⟨17088756820342291669189841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11392504546894861112793227 17088756820342291669189841)
    ·
      refine ⟨12816567615256718751892381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17088756820342291669189841 12816567615256718751892381)
      ·
        refine ⟨4806212855721269531959643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12816567615256718751892381 4806212855721269531959643)
        ·
          refine ⟨7209319283581904297939465, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4806212855721269531959643 7209319283581904297939465)
          ·
            refine ⟨5406989462686428223454599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7209319283581904297939465 5406989462686428223454599)
            ·
              refine ⟨8110484194029642335181899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5406989462686428223454599 8110484194029642335181899)
              ·
                refine ⟨12165726291044463502772849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8110484194029642335181899 12165726291044463502772849)
                ·
                  refine ⟨9124294718283347627079637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12165726291044463502772849 9124294718283347627079637)
                  ·
                    refine ⟨213850657459765960009679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9124294718283347627079637 213850657459765960009679)
                    ·
                      rfl

theorem cell23_1249418_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 1, 1, 2, 7].length) (baseStart_1249418 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249418 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249418 prefixEnd_1249418 := by exact prefixLift 1249418
  have htrace : WordTrace (prefixWord ++ tailWord_1249418) baseStart_1249418 baseEnd_1249418 := by
    simpa [prefixWord, tailWord_1249418, baseEnd_1249418] using wordTrace_append hprefix tailTrace_1249418
  have hstable : (prefixWord ++ tailWord_1249418).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249418).length < 2 ^ (prefixWord ++ tailWord_1249418).sum := by decide
  have hdescent : baseEnd_1249418 < baseStart_1249418 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249418) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249422 : List Nat := [4, 1, 1, 3, 4, 1, 1, 8]
def baseStart_1249422 : Nat := 118140960795 + 1249422 * 2 ^ 59
def prefixEnd_1249422 : Nat := 4983230072969 + 3 ^ 40 * 1249422 * 2
def baseEnd_1249422 : Nat := 23761260233404291273297

theorem tailTrace_1249422 : CollatzResearch.WordTrace tailWord_1249422 prefixEnd_1249422 23761260233404291273297 := by
  unfold tailWord_1249422
  simp only [CollatzResearch.WordTrace]
  refine ⟨5696270509945619141789815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30380109386376635422879013 5696270509945619141789815)
  ·
    refine ⟨8544405764918428712684723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5696270509945619141789815 8544405764918428712684723)
    ·
      refine ⟨12816608647377643069027085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8544405764918428712684723 12816608647377643069027085)
      ·
        refine ⟨4806228242766616150885157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12816608647377643069027085 4806228242766616150885157)
        ·
          refine ⟨901167795518740528290967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4806228242766616150885157 901167795518740528290967)
          ·
            refine ⟨1351751693278110792436451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901167795518740528290967 1351751693278110792436451)
            ·
              refine ⟨2027627539917166188654677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351751693278110792436451 2027627539917166188654677)
              ·
                refine ⟨23761260233404291273297, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2027627539917166188654677 23761260233404291273297)
                ·
                  rfl

theorem cell23_1249422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 4, 1, 1, 8].length) (baseStart_1249422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249422 prefixEnd_1249422 := by exact prefixLift 1249422
  have htrace : WordTrace (prefixWord ++ tailWord_1249422) baseStart_1249422 baseEnd_1249422 := by
    simpa [prefixWord, tailWord_1249422, baseEnd_1249422] using wordTrace_append hprefix tailTrace_1249422
  have hstable : (prefixWord ++ tailWord_1249422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249422).length < 2 ^ (prefixWord ++ tailWord_1249422).sum := by decide
  have hdescent : baseEnd_1249422 < baseStart_1249422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249432 : List Nat := [2, 1, 2, 4, 3, 1, 2, 1, 1, 3, 3]
def baseStart_1249432 : Nat := 118140960795 + 1249432 * 2 ^ 59
def prefixEnd_1249432 : Nat := 4983230072969 + 3 ^ 40 * 1249432 * 2
def baseEnd_1249432 : Nat := 641559161108460825253973

theorem tailTrace_1249432 : CollatzResearch.WordTrace tailWord_1249432 prefixEnd_1249432 641559161108460825253973 := by
  unfold tailWord_1249432
  simp only [CollatzResearch.WordTrace]
  refine ⟨22785264404764362421091275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30380352539685816561455033 22785264404764362421091275)
  ·
    refine ⟨34177896607146543631636913, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22785264404764362421091275 34177896607146543631636913)
    ·
      refine ⟨25633422455359907723727685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34177896607146543631636913 25633422455359907723727685)
      ·
        refine ⟨4806266710379982698198941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25633422455359907723727685 4806266710379982698198941)
        ·
          refine ⟨1802350016392493511824603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4806266710379982698198941 1802350016392493511824603)
          ·
            refine ⟨2703525024588740267736905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802350016392493511824603 2703525024588740267736905)
            ·
              refine ⟨2027643768441555200802679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2703525024588740267736905 2027643768441555200802679)
              ·
                refine ⟨3041465652662332801204019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2027643768441555200802679 3041465652662332801204019)
                ·
                  refine ⟨4562198478993499201806029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3041465652662332801204019 4562198478993499201806029)
                  ·
                    refine ⟨1710824429622562200677261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4562198478993499201806029 1710824429622562200677261)
                    ·
                      refine ⟨641559161108460825253973, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1710824429622562200677261 641559161108460825253973)
                      ·
                        rfl

theorem cell23_1249432_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 3, 1, 2, 1, 1, 3, 3].length) (baseStart_1249432 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249432 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249432 prefixEnd_1249432 := by exact prefixLift 1249432
  have htrace : WordTrace (prefixWord ++ tailWord_1249432) baseStart_1249432 baseEnd_1249432 := by
    simpa [prefixWord, tailWord_1249432, baseEnd_1249432] using wordTrace_append hprefix tailTrace_1249432
  have hstable : (prefixWord ++ tailWord_1249432).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249432).length < 2 ^ (prefixWord ++ tailWord_1249432).sum := by decide
  have hdescent : baseEnd_1249432 < baseStart_1249432 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249432) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249458 : List Nat := [3, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5]
def baseStart_1249458 : Nat := 118140960795 + 1249458 * 2 ^ 59
def prefixEnd_1249458 : Nat := 4983230072969 + 3 ^ 40 * 1249458 * 2
def baseEnd_1249458 : Nat := 641572511605477723528853

theorem tailTrace_1249458 : CollatzResearch.WordTrace tailWord_1249458 prefixEnd_1249458 641572511605477723528853 := by
  unfold tailWord_1249458
  simp only [CollatzResearch.WordTrace]
  refine ⟨11392869276858632820657257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30380984738289687521752685 11392869276858632820657257)
  ·
    refine ⟨8544651957643974615492943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11392869276858632820657257 8544651957643974615492943)
    ·
      refine ⟨12816977936465961923239415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8544651957643974615492943 12816977936465961923239415)
      ·
        refine ⟨19225466904698942884859123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12816977936465961923239415 19225466904698942884859123)
        ·
          refine ⟨28838200357048414327288685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19225466904698942884859123 28838200357048414327288685)
          ·
            refine ⟨10814325133893155372733257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28838200357048414327288685 10814325133893155372733257)
            ·
              refine ⟨8110743850419866529549943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10814325133893155372733257 8110743850419866529549943)
              ·
                refine ⟨12166115775629799794324915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8110743850419866529549943 12166115775629799794324915)
                ·
                  refine ⟨18249173663444699691487373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12166115775629799794324915 18249173663444699691487373)
                  ·
                    refine ⟨6843440123791762384307765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18249173663444699691487373 6843440123791762384307765)
                    ·
                      refine ⟨641572511605477723528853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6843440123791762384307765 641572511605477723528853)
                      ·
                        rfl

theorem cell23_1249458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 2, 1, 1, 3, 5].length) (baseStart_1249458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249458 prefixEnd_1249458 := by exact prefixLift 1249458
  have htrace : WordTrace (prefixWord ++ tailWord_1249458) baseStart_1249458 baseEnd_1249458 := by
    simpa [prefixWord, tailWord_1249458, baseEnd_1249458] using wordTrace_append hprefix tailTrace_1249458
  have hstable : (prefixWord ++ tailWord_1249458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249458).length < 2 ^ (prefixWord ++ tailWord_1249458).sum := by decide
  have hdescent : baseEnd_1249458 < baseStart_1249458 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249460 : List Nat := [2, 5, 3, 1, 2, 1, 1, 2, 2, 4]
def baseStart_1249460 : Nat := 118140960795 + 1249460 * 2 ^ 59
def prefixEnd_1249460 : Nat := 4983230072969 + 3 ^ 40 * 1249460 * 2
def baseEnd_1249460 : Nat := 213857846188928905234615

theorem tailTrace_1249460 : CollatzResearch.WordTrace tailWord_1249460 prefixEnd_1249460 213857846188928905234615 := by
  unfold tailWord_1249460
  simp only [CollatzResearch.WordTrace]
  refine ⟨22785775026713642812100917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30381033368951523749467889 22785775026713642812100917)
  ·
    refine ⟨2136166408754404013634461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22785775026713642812100917 2136166408754404013634461)
    ·
      refine ⟨801062403282901505112923, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2136166408754404013634461 801062403282901505112923)
      ·
        refine ⟨1201593604924352257669385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 801062403282901505112923 1201593604924352257669385)
        ·
          refine ⟨901195203693264193252039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1201593604924352257669385 901195203693264193252039)
          ·
            refine ⟨1351792805539896289878059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901195203693264193252039 1351792805539896289878059)
            ·
              refine ⟨2027689208309844434817089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1351792805539896289878059 2027689208309844434817089)
              ·
                refine ⟨1520766906232383326112817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2027689208309844434817089 1520766906232383326112817)
                ·
                  refine ⟨1140575179674287494584613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1520766906232383326112817 1140575179674287494584613)
                  ·
                    refine ⟨213857846188928905234615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140575179674287494584613 213857846188928905234615)
                    ·
                      rfl

theorem cell23_1249460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 2, 1, 1, 2, 2, 4].length) (baseStart_1249460 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249460 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249460 prefixEnd_1249460 := by exact prefixLift 1249460
  have htrace : WordTrace (prefixWord ++ tailWord_1249460) baseStart_1249460 baseEnd_1249460 := by
    simpa [prefixWord, tailWord_1249460, baseEnd_1249460] using wordTrace_append hprefix tailTrace_1249460
  have hstable : (prefixWord ++ tailWord_1249460).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249460).length < 2 ^ (prefixWord ++ tailWord_1249460).sum := by decide
  have hdescent : baseEnd_1249460 < baseStart_1249460 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249512 : List Nat := [2, 1, 4, 1, 2, 2, 3, 3, 5]
def baseStart_1249512 : Nat := 118140960795 + 1249512 * 2 ^ 59
def prefixEnd_1249512 : Nat := 4983230072969 + 3 ^ 40 * 1249512 * 2
def baseEnd_1249512 : Nat := 71288915506757834694845

theorem tailTrace_1249512 : CollatzResearch.WordTrace tailWord_1249512 prefixEnd_1249512 71288915506757834694845 := by
  unfold tailWord_1249512
  simp only [CollatzResearch.WordTrace]
  refine ⟨22786723324619449252547395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30382297766159265670063193 22786723324619449252547395)
  ·
    refine ⟨34180084986929173878821093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22786723324619449252547395 34180084986929173878821093)
    ·
      refine ⟨6408765935049220102278955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34180084986929173878821093 6408765935049220102278955)
      ·
        refine ⟨9613148902573830153418433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6408765935049220102278955 9613148902573830153418433)
        ·
          refine ⟨7209861676930372615063825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9613148902573830153418433 7209861676930372615063825)
          ·
            refine ⟨5407396257697779461297869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7209861676930372615063825 5407396257697779461297869)
            ·
              refine ⟨2027773596636667297986701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5407396257697779461297869 2027773596636667297986701)
              ·
                refine ⟨760415098738750236745013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2027773596636667297986701 760415098738750236745013)
                ·
                  refine ⟨71288915506757834694845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 760415098738750236745013 71288915506757834694845)
                  ·
                    rfl

theorem cell23_1249512_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 3, 3, 5].length) (baseStart_1249512 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249512 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249512 prefixEnd_1249512 := by exact prefixLift 1249512
  have htrace : WordTrace (prefixWord ++ tailWord_1249512) baseStart_1249512 baseEnd_1249512 := by
    simpa [prefixWord, tailWord_1249512, baseEnd_1249512] using wordTrace_append hprefix tailTrace_1249512
  have hstable : (prefixWord ++ tailWord_1249512).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249512).length < 2 ^ (prefixWord ++ tailWord_1249512).sum := by decide
  have hdescent : baseEnd_1249512 < baseStart_1249512 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249512) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249540 : List Nat := [2, 3, 2, 2, 4, 1, 2, 1, 2, 2, 2]
def baseStart_1249540 : Nat := 118140960795 + 1249540 * 2 ^ 59
def prefixEnd_1249540 : Nat := 4983230072969 + 3 ^ 40 * 1249540 * 2
def baseEnd_1249540 : Nat := 641614617019146402703477

theorem tailTrace_1249540 : CollatzResearch.WordTrace tailWord_1249540 prefixEnd_1249540 641614617019146402703477 := by
  unfold tailWord_1249540
  simp only [CollatzResearch.WordTrace]
  refine ⟨22787233946568729643557037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30382978595424972858076049 22787233946568729643557037)
  ·
    refine ⟨8545212729963273616333889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22787233946568729643557037 8545212729963273616333889)
    ·
      refine ⟨6408909547472455212250417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8545212729963273616333889 6408909547472455212250417)
      ·
        refine ⟨4806682160604341409187813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6408909547472455212250417 4806682160604341409187813)
        ·
          refine ⟨901252905113314014222715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4806682160604341409187813 901252905113314014222715)
          ·
            refine ⟨1351879357669971021334073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 901252905113314014222715 1351879357669971021334073)
            ·
              refine ⟨1013909518252478266000555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1351879357669971021334073 1013909518252478266000555)
              ·
                refine ⟨1520864277378717399000833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1013909518252478266000555 1520864277378717399000833)
                ·
                  refine ⟨1140648208034038049250625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1520864277378717399000833 1140648208034038049250625)
                  ·
                    refine ⟨855486156025528536937969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1140648208034038049250625 855486156025528536937969)
                    ·
                      refine ⟨641614617019146402703477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855486156025528536937969 641614617019146402703477)
                      ·
                        rfl

theorem cell23_1249540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 4, 1, 2, 1, 2, 2, 2].length) (baseStart_1249540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249540 prefixEnd_1249540 := by exact prefixLift 1249540
  have htrace : WordTrace (prefixWord ++ tailWord_1249540) baseStart_1249540 baseEnd_1249540 := by
    simpa [prefixWord, tailWord_1249540, baseEnd_1249540] using wordTrace_append hprefix tailTrace_1249540
  have hstable : (prefixWord ++ tailWord_1249540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249540).length < 2 ^ (prefixWord ++ tailWord_1249540).sum := by decide
  have hdescent : baseEnd_1249540 < baseStart_1249540 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249555 : List Nat := [1, 1, 1, 2, 1, 3, 1, 6, 3, 4]
def baseStart_1249555 : Nat := 118140960795 + 1249555 * 2 ^ 59
def prefixEnd_1249555 : Nat := 4983230072969 + 3 ^ 40 * 1249555 * 2
def baseEnd_1249555 : Nat := 213874106409654614671969

theorem tailTrace_1249555 : CollatzResearch.WordTrace tailWord_1249555 prefixEnd_1249555 213874106409654614671969 := by
  unfold tailWord_1249555
  simp only [CollatzResearch.WordTrace]
  refine ⟨45575014988083116848910119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30383343325388744565940079 45575014988083116848910119)
  ·
    refine ⟨68362522482124675273365179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45575014988083116848910119 68362522482124675273365179)
    ·
      refine ⟨102543783723187012910047769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68362522482124675273365179 102543783723187012910047769)
      ·
        refine ⟨76907837792390259682535827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102543783723187012910047769 76907837792390259682535827)
        ·
          refine ⟨115361756688585389523803741, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 76907837792390259682535827 115361756688585389523803741)
          ·
            refine ⟨43260658758219521071426403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115361756688585389523803741 43260658758219521071426403)
            ·
              refine ⟨64890988137329281607139605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43260658758219521071426403 64890988137329281607139605)
              ·
                refine ⟨3041765068937310075334669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 64890988137329281607139605 3041765068937310075334669)
                ·
                  refine ⟨1140661900851491278250501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3041765068937310075334669 1140661900851491278250501)
                  ·
                    refine ⟨213874106409654614671969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140661900851491278250501 213874106409654614671969)
                    ·
                      rfl

theorem cell23_1249555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 6, 3, 4].length) (baseStart_1249555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249555 prefixEnd_1249555 := by exact prefixLift 1249555
  have htrace : WordTrace (prefixWord ++ tailWord_1249555) baseStart_1249555 baseEnd_1249555 := by
    simpa [prefixWord, tailWord_1249555, baseEnd_1249555] using wordTrace_append hprefix tailTrace_1249555
  have hstable : (prefixWord ++ tailWord_1249555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249555).length < 2 ^ (prefixWord ++ tailWord_1249555).sum := by decide
  have hdescent : baseEnd_1249555 < baseStart_1249555 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249589 : List Nat := [1, 3, 3, 1, 2, 1, 3, 4, 1, 4]
def baseStart_1249589 : Nat := 118140960795 + 1249589 * 2 ^ 59
def prefixEnd_1249589 : Nat := 4983230072969 + 3 ^ 40 * 1249589 * 2
def baseEnd_1249589 : Nat := 213879925857072236996917

theorem tailTrace_1249589 : CollatzResearch.WordTrace tailWord_1249589 prefixEnd_1249589 213879925857072236996917 := by
  unfold tailWord_1249589
  simp only [CollatzResearch.WordTrace]
  refine ⟨45576255069959940655647821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30384170046639960437098547 45576255069959940655647821)
  ·
    refine ⟨17091095651234977745867933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45576255069959940655647821 17091095651234977745867933)
    ·
      refine ⟨6409160869213116654700475, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17091095651234977745867933 6409160869213116654700475)
      ·
        refine ⟨9613741303819674982050713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6409160869213116654700475 9613741303819674982050713)
        ·
          refine ⟨7210305977864756236538035, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9613741303819674982050713 7210305977864756236538035)
          ·
            refine ⟨10815458966797134354807053, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7210305977864756236538035 10815458966797134354807053)
            ·
              refine ⟨4055797112548925383052645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10815458966797134354807053 4055797112548925383052645)
              ·
                refine ⟨760461958602923509322371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4055797112548925383052645 760461958602923509322371)
                ·
                  refine ⟨1140692937904385263983557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760461958602923509322371 1140692937904385263983557)
                  ·
                    refine ⟨213879925857072236996917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140692937904385263983557 213879925857072236996917)
                    ·
                      rfl

theorem cell23_1249589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 3, 4, 1, 4].length) (baseStart_1249589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249589 prefixEnd_1249589 := by exact prefixLift 1249589
  have htrace : WordTrace (prefixWord ++ tailWord_1249589) baseStart_1249589 baseEnd_1249589 := by
    simpa [prefixWord, tailWord_1249589, baseEnd_1249589] using wordTrace_append hprefix tailTrace_1249589
  have hstable : (prefixWord ++ tailWord_1249589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249589).length < 2 ^ (prefixWord ++ tailWord_1249589).sum := by decide
  have hdescent : baseEnd_1249589 < baseStart_1249589 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249655 : List Nat := [1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 3]
def baseStart_1249655 : Nat := 118140960795 + 1249655 * 2 ^ 59
def prefixEnd_1249655 : Nat := 4983230072969 + 3 ^ 40 * 1249655 * 2
def baseEnd_1249655 : Nat := 641673667294413452765447

theorem tailTrace_1249655 : CollatzResearch.WordTrace tailWord_1249655 prefixEnd_1249655 641673667294413452765447 := by
  unfold tailWord_1249655
  simp only [CollatzResearch.WordTrace]
  refine ⟨45578662287720833927550419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30385774858480555951700279 45578662287720833927550419)
  ·
    refine ⟨68367993431581250891325629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45578662287720833927550419 68367993431581250891325629)
    ·
      refine ⟨25637997536842969084247111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68367993431581250891325629 25637997536842969084247111)
      ·
        refine ⟨38456996305264453626370667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25637997536842969084247111 38456996305264453626370667)
        ·
          refine ⟨57685494457896680439556001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38456996305264453626370667 57685494457896680439556001)
          ·
            refine ⟨43264120843422510329667001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57685494457896680439556001 43264120843422510329667001)
            ·
              refine ⟨32448090632566882747250251, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43264120843422510329667001 32448090632566882747250251)
              ·
                refine ⟨48672135948850324120875377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32448090632566882747250251 48672135948850324120875377)
                ·
                  refine ⟨36504101961637743090656533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48672135948850324120875377 36504101961637743090656533)
                  ·
                    refine ⟨1711129779451769207374525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 36504101961637743090656533 1711129779451769207374525)
                    ·
                      refine ⟨641673667294413452765447, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1711129779451769207374525 641673667294413452765447)
                      ·
                        rfl

theorem cell23_1249655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 2, 2, 1, 2, 6, 3].length) (baseStart_1249655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249655 prefixEnd_1249655 := by exact prefixLift 1249655
  have htrace : WordTrace (prefixWord ++ tailWord_1249655) baseStart_1249655 baseEnd_1249655 := by
    simpa [prefixWord, tailWord_1249655, baseEnd_1249655] using wordTrace_append hprefix tailTrace_1249655
  have hstable : (prefixWord ++ tailWord_1249655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249655).length < 2 ^ (prefixWord ++ tailWord_1249655).sum := by decide
  have hdescent : baseEnd_1249655 < baseStart_1249655 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249675 : List Nat := [1, 1, 1, 1, 4, 5, 1, 9]
def baseStart_1249675 : Nat := 118140960795 + 1249675 * 2 ^ 59
def prefixEnd_1249675 : Nat := 4983230072969 + 3 ^ 40 * 1249675 * 2
def baseEnd_1249675 : Nat := 23766071737314939796865

theorem tailTrace_1249675 : CollatzResearch.WordTrace tailWord_1249675 prefixEnd_1249675 23766071737314939796865 := by
  unfold tailWord_1249675
  simp only [CollatzResearch.WordTrace]
  refine ⟨45579391747648377343278479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30386261165098918228852319 45579391747648377343278479)
  ·
    refine ⟨68369087621472566014917719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45579391747648377343278479 68369087621472566014917719)
    ·
      refine ⟨102553631432208849022376579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68369087621472566014917719 102553631432208849022376579)
      ·
        refine ⟨153830447148313273533564869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102553631432208849022376579 153830447148313273533564869)
        ·
          refine ⟨28843208840308738787543413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 153830447148313273533564869 28843208840308738787543413)
          ·
            refine ⟨2704050828778944261332195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28843208840308738787543413 2704050828778944261332195)
            ·
              refine ⟨4056076243168416391998293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704050828778944261332195 4056076243168416391998293)
              ·
                refine ⟨23766071737314939796865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4056076243168416391998293 23766071737314939796865)
                ·
                  rfl

theorem cell23_1249675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 5, 1, 9].length) (baseStart_1249675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249675 prefixEnd_1249675 := by exact prefixLift 1249675
  have htrace : WordTrace (prefixWord ++ tailWord_1249675) baseStart_1249675 baseEnd_1249675 := by
    simpa [prefixWord, tailWord_1249675, baseEnd_1249675] using wordTrace_append hprefix tailTrace_1249675
  have hstable : (prefixWord ++ tailWord_1249675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249675).length < 2 ^ (prefixWord ++ tailWord_1249675).sum := by decide
  have hdescent : baseEnd_1249675 < baseStart_1249675 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249703 : List Nat := [1, 1, 6, 1, 1, 4, 1, 1, 3, 2, 2]
def baseStart_1249703 : Nat := 118140960795 + 1249703 * 2 ^ 59
def prefixEnd_1249703 : Nat := 4983230072969 + 3 ^ 40 * 1249703 * 2
def baseEnd_1249703 : Nat := 641698314365829264965227

theorem tailTrace_1249703 : CollatzResearch.WordTrace tailWord_1249703 prefixEnd_1249703 641698314365829264965227 := by
  unfold tailWord_1249703
  simp only [CollatzResearch.WordTrace]
  refine ⟨45580412991546938125297763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30386941994364625416865175 45580412991546938125297763)
  ·
    refine ⟨68370619487320407187946645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45580412991546938125297763 68370619487320407187946645)
    ·
      refine ⟨3204872788468144086934999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 68370619487320407187946645 3204872788468144086934999)
      ·
        refine ⟨4807309182702216130402499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3204872788468144086934999 4807309182702216130402499)
        ·
          refine ⟨7210963774053324195603749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4807309182702216130402499 7210963774053324195603749)
          ·
            refine ⟨1352055707634998286675703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7210963774053324195603749 1352055707634998286675703)
            ·
              refine ⟨2028083561452497430013555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352055707634998286675703 2028083561452497430013555)
              ·
                refine ⟨3042125342178746145020333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028083561452497430013555 3042125342178746145020333)
                ·
                  refine ⟨1140797003317029804382625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3042125342178746145020333 1140797003317029804382625)
                  ·
                    refine ⟨855597752487772353286969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1140797003317029804382625 855597752487772353286969)
                    ·
                      refine ⟨641698314365829264965227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855597752487772353286969 641698314365829264965227)
                      ·
                        rfl

theorem cell23_1249703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 4, 1, 1, 3, 2, 2].length) (baseStart_1249703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249703 prefixEnd_1249703 := by exact prefixLift 1249703
  have htrace : WordTrace (prefixWord ++ tailWord_1249703) baseStart_1249703 baseEnd_1249703 := by
    simpa [prefixWord, tailWord_1249703, baseEnd_1249703] using wordTrace_append hprefix tailTrace_1249703
  have hstable : (prefixWord ++ tailWord_1249703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249703).length < 2 ^ (prefixWord ++ tailWord_1249703).sum := by decide
  have hdescent : baseEnd_1249703 < baseStart_1249703 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249709 : List Nat := [1, 5, 2, 2, 2, 1, 2, 8]
def baseStart_1249709 : Nat := 118140960795 + 1249709 * 2 ^ 59
def prefixEnd_1249709 : Nat := 4983230072969 + 3 ^ 40 * 1249709 * 2
def baseEnd_1249709 : Nat := 23766718342583564499637

theorem tailTrace_1249709 : CollatzResearch.WordTrace tailWord_1249709 prefixEnd_1249709 23766718342583564499637 := by
  unfold tailWord_1249709
  simp only [CollatzResearch.WordTrace]
  refine ⟨45580631829525201150016181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30387087886350134100010787 45580631829525201150016181)
  ·
    refine ⟨4273184234017987607814017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45580631829525201150016181 4273184234017987607814017)
    ·
      refine ⟨3204888175513490705860513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4273184234017987607814017 3204888175513490705860513)
      ·
        refine ⟨2403666131635118029395385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3204888175513490705860513 2403666131635118029395385)
        ·
          refine ⟨1802749598726338522046539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2403666131635118029395385 1802749598726338522046539)
          ·
            refine ⟨2704124398089507783069809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1802749598726338522046539 2704124398089507783069809)
            ·
              refine ⟨2028093298567130837302357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2704124398089507783069809 2028093298567130837302357)
              ·
                refine ⟨23766718342583564499637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2028093298567130837302357 23766718342583564499637)
                ·
                  rfl

theorem cell23_1249709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 2, 1, 2, 8].length) (baseStart_1249709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249709 prefixEnd_1249709 := by exact prefixLift 1249709
  have htrace : WordTrace (prefixWord ++ tailWord_1249709) baseStart_1249709 baseEnd_1249709 := by
    simpa [prefixWord, tailWord_1249709, baseEnd_1249709] using wordTrace_append hprefix tailTrace_1249709
  have hstable : (prefixWord ++ tailWord_1249709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249709).length < 2 ^ (prefixWord ++ tailWord_1249709).sum := by decide
  have hdescent : baseEnd_1249709 < baseStart_1249709 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249772 : List Nat := [2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 4]
def baseStart_1249772 : Nat := 118140960795 + 1249772 * 2 ^ 59
def prefixEnd_1249772 : Nat := 4983230072969 + 3 ^ 40 * 1249772 * 2
def baseEnd_1249772 : Nat := 641733744530989495002409

theorem tailTrace_1249772 : CollatzResearch.WordTrace tailWord_1249772 prefixEnd_1249772 641733744530989495002409 := by
  unfold tailWord_1249772
  simp only [CollatzResearch.WordTrace]
  refine ⟨22791464814148481454779785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30388619752197975273039713 22791464814148481454779785)
  ·
    refine ⟨17093598610611361091084839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22791464814148481454779785 17093598610611361091084839)
    ·
      refine ⟨25640397915917041636627259, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17093598610611361091084839 25640397915917041636627259)
      ·
        refine ⟨38460596873875562454940889, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25640397915917041636627259 38460596873875562454940889)
        ·
          refine ⟨28845447655406671841205667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38460596873875562454940889 28845447655406671841205667)
          ·
            refine ⟨43268171483110007761808501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28845447655406671841205667 43268171483110007761808501)
            ·
              refine ⟨4056391076541563227669547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 43268171483110007761808501 4056391076541563227669547)
              ·
                refine ⟨6084586614812344841504321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4056391076541563227669547 6084586614812344841504321)
                ·
                  refine ⟨4563439961109258631128241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6084586614812344841504321 4563439961109258631128241)
                  ·
                    refine ⟨3422579970831943973346181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4563439961109258631128241 3422579970831943973346181)
                    ·
                      refine ⟨641733744530989495002409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3422579970831943973346181 641733744530989495002409)
                      ·
                        rfl

theorem cell23_1249772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 2, 2, 4].length) (baseStart_1249772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249772 prefixEnd_1249772 := by exact prefixLift 1249772
  have htrace : WordTrace (prefixWord ++ tailWord_1249772) baseStart_1249772 baseEnd_1249772 := by
    simpa [prefixWord, tailWord_1249772, baseEnd_1249772] using wordTrace_append hprefix tailTrace_1249772
  have hstable : (prefixWord ++ tailWord_1249772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249772).length < 2 ^ (prefixWord ++ tailWord_1249772).sum := by decide
  have hdescent : baseEnd_1249772 < baseStart_1249772 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249776 : List Nat := [2, 1, 1, 1, 3, 3, 1, 5, 2, 2, 2]
def baseStart_1249776 : Nat := 118140960795 + 1249776 * 2 ^ 59
def prefixEnd_1249776 : Nat := 4983230072969 + 3 ^ 40 * 1249776 * 2
def baseEnd_1249776 : Nat := 641735798453607479352391

theorem tailTrace_1249776 : CollatzResearch.WordTrace tailWord_1249776 prefixEnd_1249776 641735798453607479352391 := by
  unfold tailWord_1249776
  simp only [CollatzResearch.WordTrace]
  refine ⟨22791537760141235796352591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30388717013521647728470121 22791537760141235796352591)
  ·
    refine ⟨34187306640211853694528887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22791537760141235796352591 34187306640211853694528887)
    ·
      refine ⟨51280959960317780541793331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34187306640211853694528887 51280959960317780541793331)
      ·
        refine ⟨76921439940476670812689997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51280959960317780541793331 76921439940476670812689997)
        ·
          refine ⟨28845539977678751554758749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 76921439940476670812689997 28845539977678751554758749)
          ·
            refine ⟨10817077491629531833034531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28845539977678751554758749 10817077491629531833034531)
            ·
              refine ⟨16225616237444297749551797, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10817077491629531833034531 16225616237444297749551797)
              ·
                refine ⟨1521151522260402914020481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16225616237444297749551797 1521151522260402914020481)
                ·
                  refine ⟨1140863641695302185515361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1521151522260402914020481 1140863641695302185515361)
                  ·
                    refine ⟨855647731271476639136521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1140863641695302185515361 855647731271476639136521)
                    ·
                      refine ⟨641735798453607479352391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855647731271476639136521 641735798453607479352391)
                      ·
                        rfl

theorem cell23_1249776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 3, 1, 5, 2, 2, 2].length) (baseStart_1249776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249776 prefixEnd_1249776 := by exact prefixLift 1249776
  have htrace : WordTrace (prefixWord ++ tailWord_1249776) baseStart_1249776 baseEnd_1249776 := by
    simpa [prefixWord, tailWord_1249776, baseEnd_1249776] using wordTrace_append hprefix tailTrace_1249776
  have hstable : (prefixWord ++ tailWord_1249776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249776).length < 2 ^ (prefixWord ++ tailWord_1249776).sum := by decide
  have hdescent : baseEnd_1249776 < baseStart_1249776 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249849 : List Nat := [1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1249849 : Nat := 118140960795 + 1249849 * 2 ^ 59
def prefixEnd_1249849 : Nat := 4983230072969 + 3 ^ 40 * 1249849 * 2
def baseEnd_1249849 : Nat := 641773282541385693739555

theorem tailTrace_1249849 : CollatzResearch.WordTrace tailWord_1249849 prefixEnd_1249849 641773282541385693739555 := by
  unfold tailWord_1249849
  simp only [CollatzResearch.WordTrace]
  refine ⟨45585738049018005060112601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30390492032678670040075067 45585738049018005060112601)
  ·
    refine ⟨34189303536763503795084451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45585738049018005060112601 34189303536763503795084451)
    ·
      refine ⟨51283955305145255692626677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34189303536763503795084451 51283955305145255692626677)
      ·
        refine ⟨4807870809857367721183751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 51283955305145255692626677 4807870809857367721183751)
        ·
          refine ⟨7211806214786051581775627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4807870809857367721183751 7211806214786051581775627)
          ·
            refine ⟨10817709322179077372663441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7211806214786051581775627 10817709322179077372663441)
            ·
              refine ⟨8113281991634308029497581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10817709322179077372663441 8113281991634308029497581)
              ·
                refine ⟨3042480746862865511061593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8113281991634308029497581 3042480746862865511061593)
                ·
                  refine ⟨2281860560147149133296195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3042480746862865511061593 2281860560147149133296195)
                  ·
                    refine ⟨3422790840220723699944293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2281860560147149133296195 3422790840220723699944293)
                    ·
                      refine ⟨641773282541385693739555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3422790840220723699944293 641773282541385693739555)
                      ·
                        rfl

theorem cell23_1249849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1249849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249849 prefixEnd_1249849 := by exact prefixLift 1249849
  have htrace : WordTrace (prefixWord ++ tailWord_1249849) baseStart_1249849 baseEnd_1249849 := by
    simpa [prefixWord, tailWord_1249849, baseEnd_1249849] using wordTrace_append hprefix tailTrace_1249849
  have hstable : (prefixWord ++ tailWord_1249849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249849).length < 2 ^ (prefixWord ++ tailWord_1249849).sum := by decide
  have hdescent : baseEnd_1249849 < baseStart_1249849 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249876 : List Nat := [2, 4, 1, 1, 1, 3, 3, 1, 3, 4]
def baseStart_1249876 : Nat := 118140960795 + 1249876 * 2 ^ 59
def prefixEnd_1249876 : Nat := 4983230072969 + 3 ^ 40 * 1249876 * 2
def baseEnd_1249876 : Nat := 213929048839685696033977

theorem tailTrace_1249876 : CollatzResearch.WordTrace tailWord_1249876 prefixEnd_1249876 213929048839685696033977 := by
  unfold tailWord_1249876
  simp only [CollatzResearch.WordTrace]
  refine ⟨22793361409960094335672741, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30391148546613459114230321 22793361409960094335672741)
  ·
    refine ⟨4273755264367517687938639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22793361409960094335672741 4273755264367517687938639)
    ·
      refine ⟨6410632896551276531907959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4273755264367517687938639 6410632896551276531907959)
      ·
        refine ⟨9615949344826914797861939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6410632896551276531907959 9615949344826914797861939)
        ·
          refine ⟨14423924017240372196792909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9615949344826914797861939 14423924017240372196792909)
          ·
            refine ⟨5408971506465139573797341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14423924017240372196792909 5408971506465139573797341)
            ·
              refine ⟨2028364314924427340174003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5408971506465139573797341 2028364314924427340174003)
              ·
                refine ⟨3042546472386641010261005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2028364314924427340174003 3042546472386641010261005)
                ·
                  refine ⟨1140954927144990378847877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3042546472386641010261005 1140954927144990378847877)
                  ·
                    refine ⟨213929048839685696033977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1140954927144990378847877 213929048839685696033977)
                    ·
                      rfl

theorem cell23_1249876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 3, 3, 1, 3, 4].length) (baseStart_1249876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249876 prefixEnd_1249876 := by exact prefixLift 1249876
  have htrace : WordTrace (prefixWord ++ tailWord_1249876) baseStart_1249876 baseEnd_1249876 := by
    simpa [prefixWord, tailWord_1249876, baseEnd_1249876] using wordTrace_append hprefix tailTrace_1249876
  have hstable : (prefixWord ++ tailWord_1249876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249876).length < 2 ^ (prefixWord ++ tailWord_1249876).sum := by decide
  have hdescent : baseEnd_1249876 < baseStart_1249876 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249889 : List Nat := [1, 2, 3, 1, 1, 5, 1, 3, 6]
def baseStart_1249889 : Nat := 118140960795 + 1249889 * 2 ^ 59
def prefixEnd_1249889 : Nat := 4983230072969 + 3 ^ 40 * 1249889 * 2
def baseEnd_1249889 : Nat := 71310424640840615248819

theorem tailTrace_1249889 : CollatzResearch.WordTrace tailWord_1249889 prefixEnd_1249889 71310424640840615248819 := by
  unfold tailWord_1249889
  simp only [CollatzResearch.WordTrace]
  refine ⟨45587196968873091891568721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30391464645915394594379147 45587196968873091891568721)
  ·
    refine ⟨34190397726654818918676541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45587196968873091891568721 34190397726654818918676541)
    ·
      refine ⟨12821399147495557094503703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34190397726654818918676541 12821399147495557094503703)
      ·
        refine ⟨19232098721243335641755555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12821399147495557094503703 19232098721243335641755555)
        ·
          refine ⟨28848148081865003462633333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19232098721243335641755555 28848148081865003462633333)
          ·
            refine ⟨2704513882674844074621875, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28848148081865003462633333 2704513882674844074621875)
            ·
              refine ⟨4056770824012266111932813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704513882674844074621875 4056770824012266111932813)
              ·
                refine ⟨1521289059004599791974805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4056770824012266111932813 1521289059004599791974805)
                ·
                  refine ⟨71310424640840615248819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1521289059004599791974805 71310424640840615248819)
                  ·
                    rfl

theorem cell23_1249889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 5, 1, 3, 6].length) (baseStart_1249889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249889 prefixEnd_1249889 := by exact prefixLift 1249889
  have htrace : WordTrace (prefixWord ++ tailWord_1249889) baseStart_1249889 baseEnd_1249889 := by
    simpa [prefixWord, tailWord_1249889, baseEnd_1249889] using wordTrace_append hprefix tailTrace_1249889
  have hstable : (prefixWord ++ tailWord_1249889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249889).length < 2 ^ (prefixWord ++ tailWord_1249889).sum := by decide
  have hdescent : baseEnd_1249889 < baseStart_1249889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249949 : List Nat := [1, 4, 2, 1, 1, 1, 3, 3, 1, 6]
def baseStart_1249949 : Nat := 118140960795 + 1249949 * 2 ^ 59
def prefixEnd_1249949 : Nat := 4983230072969 + 3 ^ 40 * 1249949 * 2
def baseEnd_1249949 : Nat := 213941543535611767496365

theorem tailTrace_1249949 : CollatzResearch.WordTrace tailWord_1249949 prefixEnd_1249949 213941543535611767496365 := by
  unfold tailWord_1249949
  simp only [CollatzResearch.WordTrace]
  refine ⟨45589385348655722138752901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30392923565770481425835267 45589385348655722138752901)
  ·
    refine ⟨8548009752872947901016169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45589385348655722138752901 8548009752872947901016169)
    ·
      refine ⟨6411007314654710925762127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8548009752872947901016169 6411007314654710925762127)
      ·
        refine ⟨9616510971982066388643191, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411007314654710925762127 9616510971982066388643191)
        ·
          refine ⟨14424766457973099582964787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9616510971982066388643191 14424766457973099582964787)
          ·
            refine ⟨21637149686959649374447181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14424766457973099582964787 21637149686959649374447181)
            ·
              refine ⟨8113931132609868515417693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21637149686959649374447181 8113931132609868515417693)
              ·
                refine ⟨3042724174728700693281635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8113931132609868515417693 3042724174728700693281635)
                ·
                  refine ⟨4564086262093051039922453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3042724174728700693281635 4564086262093051039922453)
                  ·
                    refine ⟨213941543535611767496365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4564086262093051039922453 213941543535611767496365)
                    ·
                      rfl

theorem cell23_1249949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 3, 3, 1, 6].length) (baseStart_1249949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249949 prefixEnd_1249949 := by exact prefixLift 1249949
  have htrace : WordTrace (prefixWord ++ tailWord_1249949) baseStart_1249949 baseEnd_1249949 := by
    simpa [prefixWord, tailWord_1249949, baseEnd_1249949] using wordTrace_append hprefix tailTrace_1249949
  have hstable : (prefixWord ++ tailWord_1249949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249949).length < 2 ^ (prefixWord ++ tailWord_1249949).sum := by decide
  have hdescent : baseEnd_1249949 < baseStart_1249949 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249956 : List Nat := [2, 3, 1, 2, 2, 1, 2, 4, 1, 1, 4]
def baseStart_1249956 : Nat := 118140960795 + 1249956 * 2 ^ 59
def prefixEnd_1249956 : Nat := 4983230072969 + 3 ^ 40 * 1249956 * 2
def baseEnd_1249956 : Nat := 641828224971416775101563

theorem tailTrace_1249956 : CollatzResearch.WordTrace tailWord_1249956 prefixEnd_1249956 641828224971416775101563 := by
  unfold tailWord_1249956
  simp only [CollatzResearch.WordTrace]
  refine ⟨22794820329815181167128861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30393093773086908222838481 22794820329815181167128861)
  ·
    refine ⟨8548057623680692937673323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22794820329815181167128861 8548057623680692937673323)
    ·
      refine ⟨12822086435521039406509985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8548057623680692937673323 12822086435521039406509985)
      ·
        refine ⟨9616564826640779554882489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12822086435521039406509985 9616564826640779554882489)
        ·
          refine ⟨7212423619980584666161867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9616564826640779554882489 7212423619980584666161867)
          ·
            refine ⟨10818635429970876999242801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7212423619980584666161867 10818635429970876999242801)
            ·
              refine ⟨8113976572478157749432101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10818635429970876999242801 8113976572478157749432101)
              ·
                refine ⟨1521370607339654578018519, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8113976572478157749432101 1521370607339654578018519)
                ·
                  refine ⟨2282055911009481867027779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521370607339654578018519 2282055911009481867027779)
                  ·
                    refine ⟨3423083866514222800541669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2282055911009481867027779 3423083866514222800541669)
                    ·
                      refine ⟨641828224971416775101563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3423083866514222800541669 641828224971416775101563)
                      ·
                        rfl

theorem cell23_1249956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 1, 2, 4, 1, 1, 4].length) (baseStart_1249956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249956 prefixEnd_1249956 := by exact prefixLift 1249956
  have htrace : WordTrace (prefixWord ++ tailWord_1249956) baseStart_1249956 baseEnd_1249956 := by
    simpa [prefixWord, tailWord_1249956, baseEnd_1249956] using wordTrace_append hprefix tailTrace_1249956
  have hstable : (prefixWord ++ tailWord_1249956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249956).length < 2 ^ (prefixWord ++ tailWord_1249956).sum := by decide
  have hdescent : baseEnd_1249956 < baseStart_1249956 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249973 : List Nat := [1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1249973 : Nat := 118140960795 + 1249973 * 2 ^ 59
def prefixEnd_1249973 : Nat := 4983230072969 + 3 ^ 40 * 1249973 * 2
def baseEnd_1249973 : Nat := 641836954142543208588985

theorem tailTrace_1249973 : CollatzResearch.WordTrace tailWord_1249973 prefixEnd_1249973 641836954142543208588985 := by
  unfold tailWord_1249973
  simp only [CollatzResearch.WordTrace]
  refine ⟨45590260700568774237626573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30393507133712516158417715 45590260700568774237626573)
  ·
    refine ⟨17096347762713290339109965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45590260700568774237626573 17096347762713290339109965)
    ·
      refine ⟨6411130411017483877166237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17096347762713290339109965 6411130411017483877166237)
      ·
        refine ⟨2404173904131556453937339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6411130411017483877166237 2404173904131556453937339)
        ·
          refine ⟨3606260856197334680906009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404173904131556453937339 3606260856197334680906009)
          ·
            refine ⟨2704695642148001010679507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3606260856197334680906009 2704695642148001010679507)
            ·
              refine ⟨4057043463222001516019261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2704695642148001010679507 4057043463222001516019261)
              ·
                refine ⟨1521391298708250568507223, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4057043463222001516019261 1521391298708250568507223)
                ·
                  refine ⟨2282086948062375852760835, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521391298708250568507223 2282086948062375852760835)
                  ·
                    refine ⟨3423130422093563779141253, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2282086948062375852760835 3423130422093563779141253)
                    ·
                      refine ⟨641836954142543208588985, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3423130422093563779141253 641836954142543208588985)
                      ·
                        rfl

theorem cell23_1249973_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1249973 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249973 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249973 prefixEnd_1249973 := by exact prefixLift 1249973
  have htrace : WordTrace (prefixWord ++ tailWord_1249973) baseStart_1249973 baseEnd_1249973 := by
    simpa [prefixWord, tailWord_1249973, baseEnd_1249973] using wordTrace_append hprefix tailTrace_1249973
  have hstable : (prefixWord ++ tailWord_1249973).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249973).length < 2 ^ (prefixWord ++ tailWord_1249973).sum := by decide
  have hdescent : baseEnd_1249973 < baseStart_1249973 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249973) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1249983 : List Nat := [1, 1, 2, 2, 2, 6, 1, 2, 2, 4]
def baseStart_1249983 : Nat := 118140960795 + 1249983 * 2 ^ 59
def prefixEnd_1249983 : Nat := 4983230072969 + 3 ^ 40 * 1249983 * 2
def baseEnd_1249983 : Nat := 213947362983029389821313

theorem tailTrace_1249983 : CollatzResearch.WordTrace tailWord_1249983 prefixEnd_1249983 213947362983029389821313 := by
  unfold tailWord_1249983
  simp only [CollatzResearch.WordTrace]
  refine ⟨45590625430532545945490603, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30393750287021697296993735 45590625430532545945490603)
  ·
    refine ⟨68385938145798818918235905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45590625430532545945490603 68385938145798818918235905)
    ·
      refine ⟨51289453609349114188676929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68385938145798818918235905 51289453609349114188676929)
      ·
        refine ⟨38467090207011835641507697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51289453609349114188676929 38467090207011835641507697)
        ·
          refine ⟨28850317655258876731130773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38467090207011835641507697 28850317655258876731130773)
          ·
            refine ⟨1352358640090259846771755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28850317655258876731130773 1352358640090259846771755)
            ·
              refine ⟨2028537960135389770157633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352358640090259846771755 2028537960135389770157633)
              ·
                refine ⟨1521403470101542327618225, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028537960135389770157633 1521403470101542327618225)
                ·
                  refine ⟨1141052602576156745713669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1521403470101542327618225 1141052602576156745713669)
                  ·
                    refine ⟨213947362983029389821313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141052602576156745713669 213947362983029389821313)
                    ·
                      rfl

theorem cell23_1249983_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 6, 1, 2, 2, 4].length) (baseStart_1249983 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1249983 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1249983 prefixEnd_1249983 := by exact prefixLift 1249983
  have htrace : WordTrace (prefixWord ++ tailWord_1249983) baseStart_1249983 baseEnd_1249983 := by
    simpa [prefixWord, tailWord_1249983, baseEnd_1249983] using wordTrace_append hprefix tailTrace_1249983
  have hstable : (prefixWord ++ tailWord_1249983).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1249983).length < 2 ^ (prefixWord ++ tailWord_1249983).sum := by decide
  have hdescent : baseEnd_1249983 < baseStart_1249983 := by decide
  rcases family_descends (prefixWord ++ tailWord_1249983) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250024 : List Nat := [2, 1, 4, 1, 4, 2, 1, 3, 1, 2, 2]
def baseStart_1250024 : Nat := 118140960795 + 1250024 * 2 ^ 59
def prefixEnd_1250024 : Nat := 4983230072969 + 3 ^ 40 * 1250024 * 2
def baseEnd_1250024 : Nat := 641863141655922509051251

theorem tailTrace_1250024 : CollatzResearch.WordTrace tailWord_1250024 prefixEnd_1250024 641863141655922509051251 := by
  unfold tailWord_1250024
  simp only [CollatzResearch.WordTrace]
  refine ⟨22796060411692004973866563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30394747215589339965155417 22796060411692004973866563)
  ·
    refine ⟨34194090617538007460799845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22796060411692004973866563 34194090617538007460799845)
    ·
      refine ⟨6411391990788376398899971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34194090617538007460799845 6411391990788376398899971)
      ·
        refine ⟨9617087986182564598349957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411391990788376398899971 9617087986182564598349957)
        ·
          refine ⟨1803203997409230862190617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9617087986182564598349957 1803203997409230862190617)
          ·
            refine ⟨1352402998056923146642963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803203997409230862190617 1352402998056923146642963)
            ·
              refine ⟨2028604497085384719964445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352402998056923146642963 2028604497085384719964445)
              ·
                refine ⟨760726686407019269986667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2028604497085384719964445 760726686407019269986667)
                ·
                  refine ⟨1141090029610528904980001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760726686407019269986667 1141090029610528904980001)
                  ·
                    refine ⟨855817522207896678735001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1141090029610528904980001 855817522207896678735001)
                    ·
                      refine ⟨641863141655922509051251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855817522207896678735001 641863141655922509051251)
                      ·
                        rfl

theorem cell23_1250024_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 4, 2, 1, 3, 1, 2, 2].length) (baseStart_1250024 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250024 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250024 prefixEnd_1250024 := by exact prefixLift 1250024
  have htrace : WordTrace (prefixWord ++ tailWord_1250024) baseStart_1250024 baseEnd_1250024 := by
    simpa [prefixWord, tailWord_1250024, baseEnd_1250024] using wordTrace_append hprefix tailTrace_1250024
  have hstable : (prefixWord ++ tailWord_1250024).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250024).length < 2 ^ (prefixWord ++ tailWord_1250024).sum := by decide
  have hdescent : baseEnd_1250024 < baseStart_1250024 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250024) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250033 : List Nat := [1, 2, 2, 2, 2, 2, 1, 5, 1, 3, 2]
def baseStart_1250033 : Nat := 118140960795 + 1250033 * 2 ^ 59
def prefixEnd_1250033 : Nat := 4983230072969 + 3 ^ 40 * 1250033 * 2
def baseEnd_1250033 : Nat := 641867762981812973838709

theorem tailTrace_1250033 : CollatzResearch.WordTrace tailWord_1250033 prefixEnd_1250033 641867762981812973838709 := by
  unfold tailWord_1250033
  simp only [CollatzResearch.WordTrace]
  refine ⟨45592449080351404484810753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30394966053567602989873835 45592449080351404484810753)
  ·
    refine ⟨34194336810263553363608065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45592449080351404484810753 34194336810263553363608065)
    ·
      refine ⟨25645752607697665022706049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34194336810263553363608065 25645752607697665022706049)
      ·
        refine ⟨19234314455773248767029537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25645752607697665022706049 19234314455773248767029537)
        ·
          refine ⟨14425735841829936575272153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19234314455773248767029537 14425735841829936575272153)
          ·
            refine ⟨10819301881372452431454115, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14425735841829936575272153 10819301881372452431454115)
            ·
              refine ⟨16228952822058678647181173, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10819301881372452431454115 16228952822058678647181173)
              ·
                refine ⟨1521464327068001123173235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16228952822058678647181173 1521464327068001123173235)
                ·
                  refine ⟨2282196490602001684759853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521464327068001123173235 2282196490602001684759853)
                  ·
                    refine ⟨855823683975750631784945, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2282196490602001684759853 855823683975750631784945)
                    ·
                      refine ⟨641867762981812973838709, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 855823683975750631784945 641867762981812973838709)
                      ·
                        rfl

theorem cell23_1250033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 5, 1, 3, 2].length) (baseStart_1250033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250033 prefixEnd_1250033 := by exact prefixLift 1250033
  have htrace : WordTrace (prefixWord ++ tailWord_1250033) baseStart_1250033 baseEnd_1250033 := by
    simpa [prefixWord, tailWord_1250033, baseEnd_1250033] using wordTrace_append hprefix tailTrace_1250033
  have hstable : (prefixWord ++ tailWord_1250033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250033).length < 2 ^ (prefixWord ++ tailWord_1250033).sum := by decide
  have hdescent : baseEnd_1250033 < baseStart_1250033 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250049 : List Nat := [1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 5]
def baseStart_1250049 : Nat := 118140960795 + 1250049 * 2 ^ 59
def prefixEnd_1250049 : Nat := 4983230072969 + 3 ^ 40 * 1250049 * 2
def baseEnd_1250049 : Nat := 641875978672284911238635

theorem tailTrace_1250049 : CollatzResearch.WordTrace tailWord_1250049 prefixEnd_1250049 641875978672284911238635 := by
  unfold tailWord_1250049
  simp only [CollatzResearch.WordTrace]
  refine ⟨45593032648293439217393201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30395355098862292811595467 45593032648293439217393201)
  ·
    refine ⟨34194774486220079413044901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45593032648293439217393201 34194774486220079413044901)
    ·
      refine ⟨6411520216166264889945919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34194774486220079413044901 6411520216166264889945919)
      ·
        refine ⟨9617280324249397334918879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6411520216166264889945919 9617280324249397334918879)
        ·
          refine ⟨14425920486374096002378319, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9617280324249397334918879 14425920486374096002378319)
          ·
            refine ⟨21638880729561144003567479, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14425920486374096002378319 21638880729561144003567479)
            ·
              refine ⟨32458321094341716005351219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21638880729561144003567479 32458321094341716005351219)
              ·
                refine ⟨48687481641512574008026829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32458321094341716005351219 48687481641512574008026829)
                ·
                  refine ⟨18257805615567215253010061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48687481641512574008026829 18257805615567215253010061)
                  ·
                    refine ⟨6846677105837705719878773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 18257805615567215253010061 6846677105837705719878773)
                    ·
                      refine ⟨641875978672284911238635, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6846677105837705719878773 641875978672284911238635)
                      ·
                        rfl

theorem cell23_1250049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_1250049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250049 prefixEnd_1250049 := by exact prefixLift 1250049
  have htrace : WordTrace (prefixWord ++ tailWord_1250049) baseStart_1250049 baseEnd_1250049 := by
    simpa [prefixWord, tailWord_1250049, baseEnd_1250049] using wordTrace_append hprefix tailTrace_1250049
  have hstable : (prefixWord ++ tailWord_1250049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250049).length < 2 ^ (prefixWord ++ tailWord_1250049).sum := by decide
  have hdescent : baseEnd_1250049 < baseStart_1250049 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250059 : List Nat := [1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4]
def baseStart_1250059 : Nat := 118140960795 + 1250059 * 2 ^ 59
def prefixEnd_1250059 : Nat := 4983230072969 + 3 ^ 40 * 1250059 * 2
def baseEnd_1250059 : Nat := 641881113478829872113589

theorem tailTrace_1250059 : CollatzResearch.WordTrace tailWord_1250059 prefixEnd_1250059 641881113478829872113589 := by
  unfold tailWord_1250059
  simp only [CollatzResearch.WordTrace]
  refine ⟨45593397378257210925257231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30395598252171473950171487 45593397378257210925257231)
  ·
    refine ⟨68390096067385816387885847, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45593397378257210925257231 68390096067385816387885847)
    ·
      refine ⟨102585144101078724581828771, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68390096067385816387885847 102585144101078724581828771)
      ·
        refine ⟨153877716151618086872743157, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102585144101078724581828771 153877716151618086872743157)
        ·
          refine ⟨14426035889214195644319671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 153877716151618086872743157 14426035889214195644319671)
          ·
            refine ⟨21639053833821293466479507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14426035889214195644319671 21639053833821293466479507)
            ·
              refine ⟨32458580750731940199719261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21639053833821293466479507 32458580750731940199719261)
              ·
                refine ⟨12171967781524477574894723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32458580750731940199719261 12171967781524477574894723)
                ·
                  refine ⟨18257951672286716362342085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 12171967781524477574894723 18257951672286716362342085)
                  ·
                    refine ⟨3423365938553759317939141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 18257951672286716362342085 3423365938553759317939141)
                    ·
                      refine ⟨641881113478829872113589, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3423365938553759317939141 641881113478829872113589)
                      ·
                        rfl

theorem cell23_1250059_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 3, 1, 4, 4].length) (baseStart_1250059 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250059 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250059 prefixEnd_1250059 := by exact prefixLift 1250059
  have htrace : WordTrace (prefixWord ++ tailWord_1250059) baseStart_1250059 baseEnd_1250059 := by
    simpa [prefixWord, tailWord_1250059, baseEnd_1250059] using wordTrace_append hprefix tailTrace_1250059
  have hstable : (prefixWord ++ tailWord_1250059).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250059).length < 2 ^ (prefixWord ++ tailWord_1250059).sum := by decide
  have hdescent : baseEnd_1250059 < baseStart_1250059 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250059) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250069 : List Nat := [1, 3, 2, 1, 2, 2, 2, 1, 9]
def baseStart_1250069 : Nat := 118140960795 + 1250069 * 2 ^ 59
def prefixEnd_1250069 : Nat := 4983230072969 + 3 ^ 40 * 1250069 * 2
def baseEnd_1250069 : Nat := 71320694253930536998727

theorem tailTrace_1250069 : CollatzResearch.WordTrace tailWord_1250069 prefixEnd_1250069 71320694253930536998727 := by
  unfold tailWord_1250069
  simp only [CollatzResearch.WordTrace]
  refine ⟨45593762108220982633121261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30395841405480655088747507 45593762108220982633121261)
  ·
    refine ⟨17097660790582868487420473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45593762108220982633121261 17097660790582868487420473)
    ·
      refine ⟨12823245592937151365565355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17097660790582868487420473 12823245592937151365565355)
      ·
        refine ⟨19234868389405727048348033, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12823245592937151365565355 19234868389405727048348033)
        ·
          refine ⟨14426151292054295286261025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19234868389405727048348033 14426151292054295286261025)
          ·
            refine ⟨10819613469040721464695769, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14426151292054295286261025 10819613469040721464695769)
            ·
              refine ⟨8114710101780541098521827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10819613469040721464695769 8114710101780541098521827)
              ·
                refine ⟨12172065152670811647782741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8114710101780541098521827 12172065152670811647782741)
                ·
                  refine ⟨71320694253930536998727, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12172065152670811647782741 71320694253930536998727)
                  ·
                    rfl

theorem cell23_1250069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 2, 1, 9].length) (baseStart_1250069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250069 prefixEnd_1250069 := by exact prefixLift 1250069
  have htrace : WordTrace (prefixWord ++ tailWord_1250069) baseStart_1250069 baseEnd_1250069 := by
    simpa [prefixWord, tailWord_1250069, baseEnd_1250069] using wordTrace_append hprefix tailTrace_1250069
  have hstable : (prefixWord ++ tailWord_1250069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250069).length < 2 ^ (prefixWord ++ tailWord_1250069).sum := by decide
  have hdescent : baseEnd_1250069 < baseStart_1250069 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250139 : List Nat := [1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5]
def baseStart_1250139 : Nat := 118140960795 + 1250139 * 2 ^ 59
def prefixEnd_1250139 : Nat := 4983230072969 + 3 ^ 40 * 1250139 * 2
def baseEnd_1250139 : Nat := 641922191931189559113221

theorem tailTrace_1250139 : CollatzResearch.WordTrace tailWord_1250139 prefixEnd_1250139 641922191931189559113221 := by
  unfold tailWord_1250139
  simp only [CollatzResearch.WordTrace]
  refine ⟨45596315217967384588169471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30397543478644923058779647 45596315217967384588169471)
  ·
    refine ⟨68394472826951076882254207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45596315217967384588169471 68394472826951076882254207)
    ·
      refine ⟨102591709240426615323381311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68394472826951076882254207 102591709240426615323381311)
      ·
        refine ⟨153887563860639922985071967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102591709240426615323381311 153887563860639922985071967)
        ·
          refine ⟨230831345790959884477607951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 153887563860639922985071967 230831345790959884477607951)
          ·
            refine ⟨346247018686439826716411927, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 230831345790959884477607951 346247018686439826716411927)
            ·
              refine ⟨519370528029659740074617891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 346247018686439826716411927 519370528029659740074617891)
              ·
                refine ⟨779055792044489610111926837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 519370528029659740074617891 779055792044489610111926837)
                ·
                  refine ⟨73036480504170900947993141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 779055792044489610111926837 73036480504170900947993141)
                  ·
                    refine ⟨6847170047266021963874357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 73036480504170900947993141 6847170047266021963874357)
                    ·
                      refine ⟨641922191931189559113221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6847170047266021963874357 641922191931189559113221)
                      ·
                        rfl

theorem cell23_1250139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 5, 5, 5].length) (baseStart_1250139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250139 prefixEnd_1250139 := by exact prefixLift 1250139
  have htrace : WordTrace (prefixWord ++ tailWord_1250139) baseStart_1250139 baseEnd_1250139 := by
    simpa [prefixWord, tailWord_1250139, baseEnd_1250139] using wordTrace_append hprefix tailTrace_1250139
  have hstable : (prefixWord ++ tailWord_1250139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250139).length < 2 ^ (prefixWord ++ tailWord_1250139).sum := by decide
  have hdescent : baseEnd_1250139 < baseStart_1250139 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250197 : List Nat := [1, 3, 2, 1, 1, 6, 1, 3, 1, 4]
def baseStart_1250197 : Nat := 118140960795 + 1250197 * 2 ^ 59
def prefixEnd_1250197 : Nat := 4983230072969 + 3 ^ 40 * 1250197 * 2
def baseEnd_1250197 : Nat := 213983991269716777395985

theorem tailTrace_1250197 : CollatzResearch.WordTrace tailWord_1250197 prefixEnd_1250197 213983991269716777395985 := by
  unfold tailWord_1250197
  simp only [CollatzResearch.WordTrace]
  refine ⟨45598430651757260493780845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30398953767838173662520563 45598430651757260493780845)
  ·
    refine ⟨17099411494408972685167817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45598430651757260493780845 17099411494408972685167817)
    ·
      refine ⟨12824558620806729513875863, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17099411494408972685167817 12824558620806729513875863)
      ·
        refine ⟨19236837931210094270813795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12824558620806729513875863 19236837931210094270813795)
        ·
          refine ⟨28855256896815141406220693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19236837931210094270813795 28855256896815141406220693)
          ·
            refine ⟨1352590167038209753416595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28855256896815141406220693 1352590167038209753416595)
            ·
              refine ⟨2028885250557314630124893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352590167038209753416595 2028885250557314630124893)
              ·
                refine ⟨760831968958992986296835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2028885250557314630124893 760831968958992986296835)
                ·
                  refine ⟨1141247953438489479445253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760831968958992986296835 1141247953438489479445253)
                  ·
                    refine ⟨213983991269716777395985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141247953438489479445253 213983991269716777395985)
                    ·
                      rfl

theorem cell23_1250197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 6, 1, 3, 1, 4].length) (baseStart_1250197 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250197 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250197 prefixEnd_1250197 := by exact prefixLift 1250197
  have htrace : WordTrace (prefixWord ++ tailWord_1250197) baseStart_1250197 baseEnd_1250197 := by
    simpa [prefixWord, tailWord_1250197, baseEnd_1250197] using wordTrace_append hprefix tailTrace_1250197
  have hstable : (prefixWord ++ tailWord_1250197).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250197).length < 2 ^ (prefixWord ++ tailWord_1250197).sum := by decide
  have hdescent : baseEnd_1250197 < baseStart_1250197 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250226 : List Nat := [3, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4]
def baseStart_1250226 : Nat := 118140960795 + 1250226 * 2 ^ 59
def prefixEnd_1250226 : Nat := 4983230072969 + 3 ^ 40 * 1250226 * 2
def baseEnd_1250226 : Nat := 641966864748130718725321

theorem tailTrace_1250226 : CollatzResearch.WordTrace tailWord_1250226 prefixEnd_1250226 641966864748130718725321 := by
  unfold tailWord_1250226
  simp only [CollatzResearch.WordTrace]
  refine ⟨11399872092163049611646633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30399658912434798964391021 11399872092163049611646633)
  ·
    refine ⟨8549904069122287208734975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11399872092163049611646633 8549904069122287208734975)
    ·
      refine ⟨12824856103683430813102463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8549904069122287208734975 12824856103683430813102463)
      ·
        refine ⟨19237284155525146219653695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12824856103683430813102463 19237284155525146219653695)
        ·
          refine ⟨28855926233287719329480543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19237284155525146219653695 28855926233287719329480543)
          ·
            refine ⟨43283889349931578994220815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28855926233287719329480543 43283889349931578994220815)
            ·
              refine ⟨64925834024897368491331223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43283889349931578994220815 64925834024897368491331223)
              ·
                refine ⟨97388751037346052736996835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 64925834024897368491331223 97388751037346052736996835)
                ·
                  refine ⟨146083126556019079105495253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97388751037346052736996835 146083126556019079105495253)
                  ·
                    refine ⟨3423823278656697166535045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 146083126556019079105495253 3423823278656697166535045)
                    ·
                      refine ⟨641966864748130718725321, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3423823278656697166535045 641966864748130718725321)
                      ·
                        rfl

theorem cell23_1250226_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 1, 1, 1, 7, 4].length) (baseStart_1250226 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250226 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250226 prefixEnd_1250226 := by exact prefixLift 1250226
  have htrace : WordTrace (prefixWord ++ tailWord_1250226) baseStart_1250226 baseEnd_1250226 := by
    simpa [prefixWord, tailWord_1250226, baseEnd_1250226] using wordTrace_append hprefix tailTrace_1250226
  have hstable : (prefixWord ++ tailWord_1250226).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250226).length < 2 ^ (prefixWord ++ tailWord_1250226).sum := by decide
  have hdescent : baseEnd_1250226 < baseStart_1250226 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250226) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250240 : List Nat := [2, 1, 1, 2, 3, 5, 1, 2, 1, 5]
def baseStart_1250240 : Nat := 118140960795 + 1250240 * 2 ^ 59
def prefixEnd_1250240 : Nat := 4983230072969 + 3 ^ 40 * 1250240 * 2
def baseEnd_1250240 : Nat := 213991351159097887983419

theorem tailTrace_1250240 : CollatzResearch.WordTrace tailWord_1250240 prefixEnd_1250240 213991351159097887983419 := by
  unfold tailWord_1250240
  simp only [CollatzResearch.WordTrace]
  refine ⟨22799999495300739418798087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30399999327067652558397449 22799999495300739418798087)
  ·
    refine ⟨34199999242951109128197131, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22799999495300739418798087 34199999242951109128197131)
    ·
      refine ⟨51299998864426663692295697, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34199999242951109128197131 51299998864426663692295697)
      ·
        refine ⟨38474999148319997769221773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51299998864426663692295697 38474999148319997769221773)
        ·
          refine ⟨14428124680619999163458165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38474999148319997769221773 14428124680619999163458165)
          ·
            refine ⟨1352636688808124921574203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14428124680619999163458165 1352636688808124921574203)
            ·
              refine ⟨2028955033212187382361305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1352636688808124921574203 2028955033212187382361305)
              ·
                refine ⟨1521716274909140536770979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2028955033212187382361305 1521716274909140536770979)
                ·
                  refine ⟨2282574412363710805156469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521716274909140536770979 2282574412363710805156469)
                  ·
                    refine ⟨213991351159097887983419, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2282574412363710805156469 213991351159097887983419)
                    ·
                      rfl

theorem cell23_1250240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 5, 1, 2, 1, 5].length) (baseStart_1250240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250240 prefixEnd_1250240 := by exact prefixLift 1250240
  have htrace : WordTrace (prefixWord ++ tailWord_1250240) baseStart_1250240 baseEnd_1250240 := by
    simpa [prefixWord, tailWord_1250240, baseEnd_1250240] using wordTrace_append hprefix tailTrace_1250240
  have hstable : (prefixWord ++ tailWord_1250240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250240).length < 2 ^ (prefixWord ++ tailWord_1250240).sum := by decide
  have hdescent : baseEnd_1250240 < baseStart_1250240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250266 : List Nat := [3, 1, 1, 2, 4, 12]
def baseStart_1250266 : Nat := 118140960795 + 1250266 * 2 ^ 59
def prefixEnd_1250266 : Nat := 4983230072969 + 3 ^ 40 * 1250266 * 2
def baseEnd_1250266 : Nat := 2641923473145310955659

theorem tailTrace_1250266 : CollatzResearch.WordTrace tailWord_1250266 prefixEnd_1250266 2641923473145310955659 := by
  unfold tailWord_1250266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400236822126821319510663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30400631525671523518695101 11400236822126821319510663)
  ·
    refine ⟨17100355233190231979265995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11400236822126821319510663 17100355233190231979265995)
    ·
      refine ⟨25650532849785347968898993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17100355233190231979265995 25650532849785347968898993)
      ·
        refine ⟨19237899637339010976674245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25650532849785347968898993 19237899637339010976674245)
        ·
          refine ⟨3607106182001064558126421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19237899637339010976674245 3607106182001064558126421)
          ·
            refine ⟨2641923473145310955659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 12 3607106182001064558126421 2641923473145310955659)
            ·
              rfl

theorem cell23_1250266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 4, 12].length) (baseStart_1250266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250266 prefixEnd_1250266 := by exact prefixLift 1250266
  have htrace : WordTrace (prefixWord ++ tailWord_1250266) baseStart_1250266 baseEnd_1250266 := by
    simpa [prefixWord, tailWord_1250266, baseEnd_1250266] using wordTrace_append hprefix tailTrace_1250266
  have hstable : (prefixWord ++ tailWord_1250266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250266).length < 2 ^ (prefixWord ++ tailWord_1250266).sum := by decide
  have hdescent : baseEnd_1250266 < baseStart_1250266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250271 : List Nat := [1, 1, 2, 3, 5, 2, 2, 2, 1, 1, 3]
def baseStart_1250271 : Nat := 118140960795 + 1250271 * 2 ^ 59
def prefixEnd_1250271 : Nat := 4983230072969 + 3 ^ 40 * 1250271 * 2
def baseEnd_1250271 : Nat := 641989971377583042662615

theorem tailTrace_1250271 : CollatzResearch.WordTrace tailWord_1250271 prefixEnd_1250271 641989971377583042662615 := by
  unfold tailWord_1250271
  simp only [CollatzResearch.WordTrace]
  refine ⟨45601129653489171131974667, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30400753102326114087983111 45601129653489171131974667)
  ·
    refine ⟨68401694480233756697962001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45601129653489171131974667 68401694480233756697962001)
    ·
      refine ⟨51301270860175317523471501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68401694480233756697962001 51301270860175317523471501)
      ·
        refine ⟨19237976572565744071301813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51301270860175317523471501 19237976572565744071301813)
        ·
          refine ⟨1803560303678038506684545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 19237976572565744071301813 1803560303678038506684545)
          ·
            refine ⟨1352670227758528880013409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1803560303678038506684545 1352670227758528880013409)
            ·
              refine ⟨1014502670818896660010057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352670227758528880013409 1014502670818896660010057)
              ·
                refine ⟨760877003114172495007543, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1014502670818896660010057 760877003114172495007543)
                ·
                  refine ⟨1141315504671258742511315, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 760877003114172495007543 1141315504671258742511315)
                  ·
                    refine ⟨1711973257006888113766973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1141315504671258742511315 1711973257006888113766973)
                    ·
                      refine ⟨641989971377583042662615, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1711973257006888113766973 641989971377583042662615)
                      ·
                        rfl

theorem cell23_1250271_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 2, 2, 1, 1, 3].length) (baseStart_1250271 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250271 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250271 prefixEnd_1250271 := by exact prefixLift 1250271
  have htrace : WordTrace (prefixWord ++ tailWord_1250271) baseStart_1250271 baseEnd_1250271 := by
    simpa [prefixWord, tailWord_1250271, baseEnd_1250271] using wordTrace_append hprefix tailTrace_1250271
  have hstable : (prefixWord ++ tailWord_1250271).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250271).length < 2 ^ (prefixWord ++ tailWord_1250271).sum := by decide
  have hdescent : baseEnd_1250271 < baseStart_1250271 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250271) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250276 : List Nat := [2, 3, 1, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_1250276 : Nat := 118140960795 + 1250276 * 2 ^ 59
def prefixEnd_1250276 : Nat := 4983230072969 + 3 ^ 40 * 1250276 * 2
def baseEnd_1250276 : Nat := 641992538780855523100091

theorem tailTrace_1250276 : CollatzResearch.WordTrace tailWord_1250276 prefixEnd_1250276 641992538780855523100091 := by
  unfold tailWord_1250276
  simp only [CollatzResearch.WordTrace]
  refine ⟨22800656009235528492953341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30400874678980704657271121 22800656009235528492953341)
  ·
    refine ⟨8550246003463323184857503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22800656009235528492953341 8550246003463323184857503)
    ·
      refine ⟨12825369005194984777286255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8550246003463323184857503 12825369005194984777286255)
      ·
        refine ⟨19238053507792477165929383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12825369005194984777286255 19238053507792477165929383)
        ·
          refine ⟨28857080261688715748894075, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19238053507792477165929383 28857080261688715748894075)
          ·
            refine ⟨43285620392533073623341113, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28857080261688715748894075 43285620392533073623341113)
            ·
              refine ⟨32464215294399805217505835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43285620392533073623341113 32464215294399805217505835)
              ·
                refine ⟨48696322941599707826258753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32464215294399805217505835 48696322941599707826258753)
                ·
                  refine ⟨36522242206199780869694065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48696322941599707826258753 36522242206199780869694065)
                  ·
                    refine ⟨27391681654649835652270549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36522242206199780869694065 27391681654649835652270549)
                    ·
                      refine ⟨641992538780855523100091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27391681654649835652270549 641992538780855523100091)
                      ·
                        rfl

theorem cell23_1250276_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_1250276 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250276 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250276 prefixEnd_1250276 := by exact prefixLift 1250276
  have htrace : WordTrace (prefixWord ++ tailWord_1250276) baseStart_1250276 baseEnd_1250276 := by
    simpa [prefixWord, tailWord_1250276, baseEnd_1250276] using wordTrace_append hprefix tailTrace_1250276
  have hstable : (prefixWord ++ tailWord_1250276).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250276).length < 2 ^ (prefixWord ++ tailWord_1250276).sum := by decide
  have hdescent : baseEnd_1250276 < baseStart_1250276 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250276) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250294 : List Nat := [5, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2]
def baseStart_1250294 : Nat := 118140960795 + 1250294 * 2 ^ 59
def prefixEnd_1250294 : Nat := 4983230072969 + 3 ^ 40 * 1250294 * 2
def baseEnd_1250294 : Nat := 642001781432636452675009

theorem tailTrace_1250294 : CollatzResearch.WordTrace tailWord_1250294 prefixEnd_1250294 642001781432636452675009 := by
  unfold tailWord_1250294
  simp only [CollatzResearch.WordTrace]
  refine ⟨2850123033275365378753871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30401312354937230706707957 2850123033275365378753871)
  ·
    refine ⟨4275184549913048068130807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2850123033275365378753871 4275184549913048068130807)
    ·
      refine ⟨6412776824869572102196211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4275184549913048068130807 6412776824869572102196211)
      ·
        refine ⟨9619165237304358153294317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6412776824869572102196211 9619165237304358153294317)
        ·
          refine ⟨3607186963989134307485369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9619165237304358153294317 3607186963989134307485369)
          ·
            refine ⟨2705390222991850730614027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3607186963989134307485369 2705390222991850730614027)
            ·
              refine ⟨4058085334487776095921041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705390222991850730614027 4058085334487776095921041)
              ·
                refine ⟨3043564000865832071940781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4058085334487776095921041 3043564000865832071940781)
                ·
                  refine ⟨1141336500324687026977793, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3043564000865832071940781 1141336500324687026977793)
                  ·
                    refine ⟨856002375243515270233345, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1141336500324687026977793 856002375243515270233345)
                    ·
                      refine ⟨642001781432636452675009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856002375243515270233345 642001781432636452675009)
                      ·
                        rfl

theorem cell23_1250294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 3, 2, 1, 2, 3, 2, 2].length) (baseStart_1250294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250294 prefixEnd_1250294 := by exact prefixLift 1250294
  have htrace : WordTrace (prefixWord ++ tailWord_1250294) baseStart_1250294 baseEnd_1250294 := by
    simpa [prefixWord, tailWord_1250294, baseEnd_1250294] using wordTrace_append hprefix tailTrace_1250294
  have hstable : (prefixWord ++ tailWord_1250294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250294).length < 2 ^ (prefixWord ++ tailWord_1250294).sum := by decide
  have hdescent : baseEnd_1250294 < baseStart_1250294 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250296 : List Nat := [2, 1, 2, 1, 1, 3, 1, 1, 4, 7]
def baseStart_1250296 : Nat := 118140960795 + 1250296 * 2 ^ 59
def prefixEnd_1250296 : Nat := 4983230072969 + 3 ^ 40 * 1250296 * 2
def baseEnd_1250296 : Nat := 214000936131315148283333

theorem tailTrace_1250296 : CollatzResearch.WordTrace tailWord_1250296 prefixEnd_1250296 214000936131315148283333 := by
  unfold tailWord_1250296
  simp only [CollatzResearch.WordTrace]
  refine ⟨22801020739199300200817371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30401360985599066934423161 22801020739199300200817371)
  ·
    refine ⟨34201531108798950301226057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22801020739199300200817371 34201531108798950301226057)
    ·
      refine ⟨25651148331599212725919543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34201531108798950301226057 25651148331599212725919543)
      ·
        refine ⟨38476722497398819088879315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25651148331599212725919543 38476722497398819088879315)
        ·
          refine ⟨57715083746098228633318973, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38476722497398819088879315 57715083746098228633318973)
          ·
            refine ⟨21643156404786835737494615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57715083746098228633318973 21643156404786835737494615)
            ·
              refine ⟨32464734607180253606241923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21643156404786835737494615 32464734607180253606241923)
              ·
                refine ⟨48697101910770380409362885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32464734607180253606241923 48697101910770380409362885)
                ·
                  refine ⟨9130706608269446326755541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48697101910770380409362885 9130706608269446326755541)
                  ·
                    refine ⟨214000936131315148283333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9130706608269446326755541 214000936131315148283333)
                    ·
                      rfl

theorem cell23_1250296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 1, 1, 4, 7].length) (baseStart_1250296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250296 prefixEnd_1250296 := by exact prefixLift 1250296
  have htrace : WordTrace (prefixWord ++ tailWord_1250296) baseStart_1250296 baseEnd_1250296 := by
    simpa [prefixWord, tailWord_1250296, baseEnd_1250296] using wordTrace_append hprefix tailTrace_1250296
  have hstable : (prefixWord ++ tailWord_1250296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250296).length < 2 ^ (prefixWord ++ tailWord_1250296).sum := by decide
  have hdescent : baseEnd_1250296 < baseStart_1250296 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250314 : List Nat := [3, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3]
def baseStart_1250314 : Nat := 118140960795 + 1250314 * 2 ^ 59
def prefixEnd_1250314 : Nat := 4983230072969 + 3 ^ 40 * 1250314 * 2
def baseEnd_1250314 : Nat := 642012051045726374424917

theorem tailTrace_1250314 : CollatzResearch.WordTrace tailWord_1250314 prefixEnd_1250314 642012051045726374424917 := by
  unfold tailWord_1250314
  simp only [CollatzResearch.WordTrace]
  refine ⟨11400674498083347368947499, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30401798661555592983859997 11400674498083347368947499)
  ·
    refine ⟨17101011747125021053421249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11400674498083347368947499 17101011747125021053421249)
    ·
      refine ⟨12825758810343765790065937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17101011747125021053421249 12825758810343765790065937)
      ·
        refine ⟨9619319107757824342549453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12825758810343765790065937 9619319107757824342549453)
        ·
          refine ⟨3607244665409184128456045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9619319107757824342549453 3607244665409184128456045)
          ·
            refine ⟨1352716749528444048171017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3607244665409184128456045 1352716749528444048171017)
            ·
              refine ⟨1014537562146333036128263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1352716749528444048171017 1014537562146333036128263)
              ·
                refine ⟨1521806343219499554192395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1014537562146333036128263 1521806343219499554192395)
                ·
                  refine ⟨2282709514829249331288593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1521806343219499554192395 2282709514829249331288593)
                  ·
                    refine ⟨1712032136121936998466445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2282709514829249331288593 1712032136121936998466445)
                    ·
                      refine ⟨642012051045726374424917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1712032136121936998466445 642012051045726374424917)
                      ·
                        rfl

theorem cell23_1250314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 3, 2, 1, 1, 2, 3].length) (baseStart_1250314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250314 prefixEnd_1250314 := by exact prefixLift 1250314
  have htrace : WordTrace (prefixWord ++ tailWord_1250314) baseStart_1250314 baseEnd_1250314 := by
    simpa [prefixWord, tailWord_1250314, baseEnd_1250314] using wordTrace_append hprefix tailTrace_1250314
  have hstable : (prefixWord ++ tailWord_1250314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250314).length < 2 ^ (prefixWord ++ tailWord_1250314).sum := by decide
  have hdescent : baseEnd_1250314 < baseStart_1250314 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250327 : List Nat := [1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 3]
def baseStart_1250327 : Nat := 118140960795 + 1250327 * 2 ^ 59
def prefixEnd_1250327 : Nat := 4983230072969 + 3 ^ 40 * 1250327 * 2
def baseEnd_1250327 : Nat := 642018726294234823562357

theorem tailTrace_1250327 : CollatzResearch.WordTrace tailWord_1250327 prefixEnd_1250327 642018726294234823562357 := by
  unfold tailWord_1250327
  simp only [CollatzResearch.WordTrace]
  refine ⟨45603172141286292696013235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30402114760857528464008823 45603172141286292696013235)
  ·
    refine ⟨68404758211929439044019853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45603172141286292696013235 68404758211929439044019853)
    ·
      refine ⟨25651784329473539641507445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68404758211929439044019853 25651784329473539641507445)
      ·
        refine ⟨2404854780888144341391323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25651784329473539641507445 2404854780888144341391323)
        ·
          refine ⟨3607282171332216512086985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2404854780888144341391323 3607282171332216512086985)
          ·
            refine ⟨2705461628499162384065239, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3607282171332216512086985 2705461628499162384065239)
            ·
              refine ⟨4058192442748743576097859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705461628499162384065239 4058192442748743576097859)
              ·
                refine ⟨6087288664123115364146789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058192442748743576097859 6087288664123115364146789)
                ·
                  refine ⟨1141366624523084130777523, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6087288664123115364146789 1141366624523084130777523)
                  ·
                    refine ⟨1712049936784626196166285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1141366624523084130777523 1712049936784626196166285)
                    ·
                      refine ⟨642018726294234823562357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1712049936784626196166285 642018726294234823562357)
                      ·
                        rfl

theorem cell23_1250327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 1, 2, 1, 1, 4, 1, 3].length) (baseStart_1250327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250327 prefixEnd_1250327 := by exact prefixLift 1250327
  have htrace : WordTrace (prefixWord ++ tailWord_1250327) baseStart_1250327 baseEnd_1250327 := by
    simpa [prefixWord, tailWord_1250327, baseEnd_1250327] using wordTrace_append hprefix tailTrace_1250327
  have hstable : (prefixWord ++ tailWord_1250327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250327).length < 2 ^ (prefixWord ++ tailWord_1250327).sum := by decide
  have hdescent : baseEnd_1250327 < baseStart_1250327 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250353 : List Nat := [1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 5]
def baseStart_1250353 : Nat := 118140960795 + 1250353 * 2 ^ 59
def prefixEnd_1250353 : Nat := 4983230072969 + 3 ^ 40 * 1250353 * 2
def baseEnd_1250353 : Nat := 642032076791251721837237

theorem tailTrace_1250353 : CollatzResearch.WordTrace tailWord_1250353 prefixEnd_1250353 642032076791251721837237 := by
  unfold tailWord_1250353
  simp only [CollatzResearch.WordTrace]
  refine ⟨45604120439192099136459713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30402746959461399424306475 45604120439192099136459713)
  ·
    refine ⟨34203090329394074352344785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45604120439192099136459713 34203090329394074352344785)
    ·
      refine ⟨25652317747045555764258589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34203090329394074352344785 25652317747045555764258589)
      ·
        refine ⟨9619619155142083411596971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25652317747045555764258589 9619619155142083411596971)
        ·
          refine ⟨14429428732713125117395457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9619619155142083411596971 14429428732713125117395457)
          ·
            refine ⟨10822071549534843838046593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14429428732713125117395457 10822071549534843838046593)
            ·
              refine ⟨8116553662151132878534945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10822071549534843838046593 8116553662151132878534945)
              ·
                refine ⟨6087415246613349658901209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8116553662151132878534945 6087415246613349658901209)
                ·
                  refine ⟨4565561434960012244175907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6087415246613349658901209 4565561434960012244175907)
                  ·
                    refine ⟨6848342152440018366263861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4565561434960012244175907 6848342152440018366263861)
                    ·
                      refine ⟨642032076791251721837237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6848342152440018366263861 642032076791251721837237)
                      ·
                        rfl

theorem cell23_1250353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 2, 2, 2, 2, 1, 5].length) (baseStart_1250353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250353 prefixEnd_1250353 := by exact prefixLift 1250353
  have htrace : WordTrace (prefixWord ++ tailWord_1250353) baseStart_1250353 baseEnd_1250353 := by
    simpa [prefixWord, tailWord_1250353, baseEnd_1250353] using wordTrace_append hprefix tailTrace_1250353
  have hstable : (prefixWord ++ tailWord_1250353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250353).length < 2 ^ (prefixWord ++ tailWord_1250353).sum := by decide
  have hdescent : baseEnd_1250353 < baseStart_1250353 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250403 : List Nat := [1, 1, 1, 5, 1, 1, 1, 1, 6, 5]
def baseStart_1250403 : Nat := 118140960795 + 1250403 * 2 ^ 59
def prefixEnd_1250403 : Nat := 4983230072969 + 3 ^ 40 * 1250403 * 2
def baseEnd_1250403 : Nat := 214019250274658842070669

theorem tailTrace_1250403 : CollatzResearch.WordTrace tailWord_1250403 prefixEnd_1250403 214019250274658842070669 := by
  unfold tailWord_1250403
  simp only [CollatzResearch.WordTrace]
  refine ⟨45605944089010957675779863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30403962726007305117186575 45605944089010957675779863)
  ·
    refine ⟨68408916133516436513669795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45605944089010957675779863 68408916133516436513669795)
    ·
      refine ⟨102613374200274654770504693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68408916133516436513669795 102613374200274654770504693)
      ·
        refine ⟨9620003831275748884734815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 102613374200274654770504693 9620003831275748884734815)
        ·
          refine ⟨14430005746913623327102223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9620003831275748884734815 14430005746913623327102223)
          ·
            refine ⟨21645008620370434990653335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14430005746913623327102223 21645008620370434990653335)
            ·
              refine ⟨32467512930555652485980003, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21645008620370434990653335 32467512930555652485980003)
              ·
                refine ⟨48701269395833478728970005, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32467512930555652485980003 48701269395833478728970005)
                ·
                  refine ⟨2282872002929694315420469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 48701269395833478728970005 2282872002929694315420469)
                  ·
                    refine ⟨214019250274658842070669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2282872002929694315420469 214019250274658842070669)
                    ·
                      rfl

theorem cell23_1250403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 1, 1, 1, 6, 5].length) (baseStart_1250403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250403 prefixEnd_1250403 := by exact prefixLift 1250403
  have htrace : WordTrace (prefixWord ++ tailWord_1250403) baseStart_1250403 baseEnd_1250403 := by
    simpa [prefixWord, tailWord_1250403, baseEnd_1250403] using wordTrace_append hprefix tailTrace_1250403
  have hstable : (prefixWord ++ tailWord_1250403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250403).length < 2 ^ (prefixWord ++ tailWord_1250403).sum := by decide
  have hdescent : baseEnd_1250403 < baseStart_1250403 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250453 : List Nat := [1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 6]
def baseStart_1250453 : Nat := 118140960795 + 1250453 * 2 ^ 59
def prefixEnd_1250453 : Nat := 4983230072969 + 3 ^ 40 * 1250453 * 2
def baseEnd_1250453 : Nat := 642083424856701330586777

theorem tailTrace_1250453 : CollatzResearch.WordTrace tailWord_1250453 prefixEnd_1250453 642083424856701330586777 := by
  unfold tailWord_1250453
  simp only [CollatzResearch.WordTrace]
  refine ⟨45607767738829816215100013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30405178492553210810066675 45607767738829816215100013)
  ·
    refine ⟨17102912902061181080662505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45607767738829816215100013 17102912902061181080662505)
    ·
      refine ⟨12827184676545885810496879, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17102912902061181080662505 12827184676545885810496879)
      ·
        refine ⟨19240777014818828715745319, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12827184676545885810496879 19240777014818828715745319)
        ·
          refine ⟨28861165522228243073617979, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19240777014818828715745319 28861165522228243073617979)
          ·
            refine ⟨43291748283342364610426969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28861165522228243073617979 43291748283342364610426969)
            ·
              refine ⟨32468811212506773457820227, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43291748283342364610426969 32468811212506773457820227)
              ·
                refine ⟨48703216818760160186730341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32468811212506773457820227 48703216818760160186730341)
                ·
                  refine ⟨9131853153517530035011939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48703216818760160186730341 9131853153517530035011939)
                  ·
                    refine ⟨13697779730276295052517909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 9131853153517530035011939 13697779730276295052517909)
                    ·
                      refine ⟨642083424856701330586777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13697779730276295052517909 642083424856701330586777)
                      ·
                        rfl

theorem cell23_1250453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 1, 4, 1, 6].length) (baseStart_1250453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250453 prefixEnd_1250453 := by exact prefixLift 1250453
  have htrace : WordTrace (prefixWord ++ tailWord_1250453) baseStart_1250453 baseEnd_1250453 := by
    simpa [prefixWord, tailWord_1250453, baseEnd_1250453] using wordTrace_append hprefix tailTrace_1250453
  have hstable : (prefixWord ++ tailWord_1250453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250453).length < 2 ^ (prefixWord ++ tailWord_1250453).sum := by decide
  have hdescent : baseEnd_1250453 < baseStart_1250453 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250474 : List Nat := [3, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4]
def baseStart_1250474 : Nat := 118140960795 + 1250474 * 2 ^ 59
def prefixEnd_1250474 : Nat := 4983230072969 + 3 ^ 40 * 1250474 * 2
def baseEnd_1250474 : Nat := 642094207950445748424181

theorem tailTrace_1250474 : CollatzResearch.WordTrace tailWord_1250474 prefixEnd_1250474 642094207950445748424181 := by
  unfold tailWord_1250474
  simp only [CollatzResearch.WordTrace]
  refine ⟨11402133417938434200403619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30405689114502491201076317 11402133417938434200403619)
  ·
    refine ⟨17103200126907651300605429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11402133417938434200403619 17103200126907651300605429)
    ·
      refine ⟨1603425011897592309431759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17103200126907651300605429 1603425011897592309431759)
      ·
        refine ⟨2405137517846388464147639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603425011897592309431759 2405137517846388464147639)
        ·
          refine ⟨3607706276769582696221459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405137517846388464147639 3607706276769582696221459)
          ·
            refine ⟨5411559415154374044332189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3607706276769582696221459 5411559415154374044332189)
            ·
              refine ⟨2029334780682890266624571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5411559415154374044332189 2029334780682890266624571)
              ·
                refine ⟨3044002171024335399936857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029334780682890266624571 3044002171024335399936857)
                ·
                  refine ⟨2283001628268251549952643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044002171024335399936857 2283001628268251549952643)
                  ·
                    refine ⟨3424502442402377324928965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2283001628268251549952643 3424502442402377324928965)
                    ·
                      refine ⟨642094207950445748424181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3424502442402377324928965 642094207950445748424181)
                      ·
                        rfl

theorem cell23_1250474_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 1, 3, 1, 2, 1, 4].length) (baseStart_1250474 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250474 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250474 prefixEnd_1250474 := by exact prefixLift 1250474
  have htrace : WordTrace (prefixWord ++ tailWord_1250474) baseStart_1250474 baseEnd_1250474 := by
    simpa [prefixWord, tailWord_1250474, baseEnd_1250474] using wordTrace_append hprefix tailTrace_1250474
  have hstable : (prefixWord ++ tailWord_1250474).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250474).length < 2 ^ (prefixWord ++ tailWord_1250474).sum := by decide
  have hdescent : baseEnd_1250474 < baseStart_1250474 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250474) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250497 : List Nat := [1, 2, 6, 1, 1, 2, 1, 1, 8]
def baseStart_1250497 : Nat := 118140960795 + 1250497 * 2 ^ 59
def prefixEnd_1250497 : Nat := 4983230072969 + 3 ^ 40 * 1250497 * 2
def baseEnd_1250497 : Nat := 71345113111722128715175

theorem tailTrace_1250497 : CollatzResearch.WordTrace tailWord_1250497 prefixEnd_1250497 71345113111722128715175 := by
  unfold tailWord_1250497
  simp only [CollatzResearch.WordTrace]
  refine ⟨45609372550670411729701745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30406248367113607819801163 45609372550670411729701745)
  ·
    refine ⟨34207029413002808797276309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45609372550670411729701745 34207029413002808797276309)
    ·
      refine ⟨1603454503734506662372327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34207029413002808797276309 1603454503734506662372327)
      ·
        refine ⟨2405181755601759993558491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603454503734506662372327 2405181755601759993558491)
        ·
          refine ⟨3607772633402639990337737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2405181755601759993558491 3607772633402639990337737)
          ·
            refine ⟨2705829475051979992753303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3607772633402639990337737 2705829475051979992753303)
            ·
              refine ⟨4058744212577969989129955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705829475051979992753303 4058744212577969989129955)
              ·
                refine ⟨6088116318866954983694933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4058744212577969989129955 6088116318866954983694933)
                ·
                  refine ⟨71345113111722128715175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6088116318866954983694933 71345113111722128715175)
                  ·
                    rfl

theorem cell23_1250497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 2, 1, 1, 8].length) (baseStart_1250497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250497 prefixEnd_1250497 := by exact prefixLift 1250497
  have htrace : WordTrace (prefixWord ++ tailWord_1250497) baseStart_1250497 baseEnd_1250497 := by
    simpa [prefixWord, tailWord_1250497, baseEnd_1250497] using wordTrace_append hprefix tailTrace_1250497
  have hstable : (prefixWord ++ tailWord_1250497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250497).length < 2 ^ (prefixWord ++ tailWord_1250497).sum := by decide
  have hdescent : baseEnd_1250497 < baseStart_1250497 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250547 : List Nat := [1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 4]
def baseStart_1250547 : Nat := 118140960795 + 1250547 * 2 ^ 59
def prefixEnd_1250547 : Nat := 4983230072969 + 3 ^ 40 * 1250547 * 2
def baseEnd_1250547 : Nat := 642131692038223962811345

theorem tailTrace_1250547 : CollatzResearch.WordTrace tailWord_1250547 prefixEnd_1250547 642131692038223962811345 := by
  unfold tailWord_1250547
  simp only [CollatzResearch.WordTrace]
  refine ⟨45611196200489270269021895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30407464133659513512681263 45611196200489270269021895)
  ·
    refine ⟨68416794300733905403532843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45611196200489270269021895 68416794300733905403532843)
    ·
      refine ⟨102625191451100858105299265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68416794300733905403532843 102625191451100858105299265)
      ·
        refine ⟨76968893588325643578974449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102625191451100858105299265 76968893588325643578974449)
        ·
          refine ⟨57726670191244232684230837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 76968893588325643578974449 57726670191244232684230837)
          ·
            refine ⟨5411875330429146814146641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57726670191244232684230837 5411875330429146814146641)
            ·
              refine ⟨4058906497821860110609981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5411875330429146814146641 4058906497821860110609981)
              ·
                refine ⟨1522089936683197541478743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4058906497821860110609981 1522089936683197541478743)
                ·
                  refine ⟨2283134905024796312218115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522089936683197541478743 2283134905024796312218115)
                  ·
                    refine ⟨3424702357537194468327173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2283134905024796312218115 3424702357537194468327173)
                    ·
                      refine ⟨642131692038223962811345, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3424702357537194468327173 642131692038223962811345)
                      ·
                        rfl

theorem cell23_1250547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 5, 2, 3, 1, 1, 4].length) (baseStart_1250547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250547 prefixEnd_1250547 := by exact prefixLift 1250547
  have htrace : WordTrace (prefixWord ++ tailWord_1250547) baseStart_1250547 baseEnd_1250547 := by
    simpa [prefixWord, tailWord_1250547, baseEnd_1250547] using wordTrace_append hprefix tailTrace_1250547
  have hstable : (prefixWord ++ tailWord_1250547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250547).length < 2 ^ (prefixWord ++ tailWord_1250547).sum := by decide
  have hdescent : baseEnd_1250547 < baseStart_1250547 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250574 : List Nat := [4, 1, 1, 2, 1, 4, 1, 3, 2, 4]
def baseStart_1250574 : Nat := 118140960795 + 1250574 * 2 ^ 59
def prefixEnd_1250574 : Nat := 4983230072969 + 3 ^ 40 * 1250574 * 2
def baseEnd_1250574 : Nat := 214048518671965119057907

theorem tailTrace_1250574 : CollatzResearch.WordTrace tailWord_1250574 prefixEnd_1250574 214048518671965119057907 := by
  unfold tailWord_1250574
  simp only [CollatzResearch.WordTrace]
  refine ⟨5701522621423931735031847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30408120647594302586836517 5701522621423931735031847)
  ·
    refine ⟨8552283932135897602547771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5701522621423931735031847 8552283932135897602547771)
    ·
      refine ⟨12828425898203846403821657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8552283932135897602547771 12828425898203846403821657)
      ·
        refine ⟨9621319423652884802866243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12828425898203846403821657 9621319423652884802866243)
        ·
          refine ⟨14431979135479327204299365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621319423652884802866243 14431979135479327204299365)
          ·
            refine ⟨2705996087902373850806131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14431979135479327204299365 2705996087902373850806131)
            ·
              refine ⟨4058994131853560776209197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2705996087902373850806131 4058994131853560776209197)
              ·
                refine ⟨1522122799445085291078449, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4058994131853560776209197 1522122799445085291078449)
                ·
                  refine ⟨1141592099583813968308837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522122799445085291078449 1141592099583813968308837)
                  ·
                    refine ⟨214048518671965119057907, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1141592099583813968308837 214048518671965119057907)
                    ·
                      rfl

theorem cell23_1250574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 4, 1, 3, 2, 4].length) (baseStart_1250574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250574 prefixEnd_1250574 := by exact prefixLift 1250574
  have htrace : WordTrace (prefixWord ++ tailWord_1250574) baseStart_1250574 baseEnd_1250574 := by
    simpa [prefixWord, tailWord_1250574, baseEnd_1250574] using wordTrace_append hprefix tailTrace_1250574
  have hstable : (prefixWord ++ tailWord_1250574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250574).length < 2 ^ (prefixWord ++ tailWord_1250574).sum := by decide
  have hdescent : baseEnd_1250574 < baseStart_1250574 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250578 : List Nat := [3, 2, 4, 2, 1, 2, 1, 2, 1, 5]
def baseStart_1250578 : Nat := 118140960795 + 1250578 * 2 ^ 59
def prefixEnd_1250578 : Nat := 4983230072969 + 3 ^ 40 * 1250578 * 2
def baseEnd_1250578 : Nat := 214049203312837780507901

theorem tailTrace_1250578 : CollatzResearch.WordTrace tailWord_1250578 prefixEnd_1250578 214049203312837780507901 := by
  unfold tailWord_1250578
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403081715844240640850097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30408217908917975042266925 11403081715844240640850097)
  ·
    refine ⟨8552311286883180480637573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11403081715844240640850097 8552311286883180480637573)
    ·
      refine ⟨1603558366290596340119545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8552311286883180480637573 1603558366290596340119545)
      ·
        refine ⟨1202668774717947255089659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1603558366290596340119545 1202668774717947255089659)
        ·
          refine ⟨1804003162076920882634489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1202668774717947255089659 1804003162076920882634489)
          ·
            refine ⟨1353002371557690661975867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1804003162076920882634489 1353002371557690661975867)
            ·
              refine ⟨2029503557336535992963801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353002371557690661975867 2029503557336535992963801)
              ·
                refine ⟨1522127668002401994722851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029503557336535992963801 1522127668002401994722851)
                ·
                  refine ⟨2283191502003602992084277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522127668002401994722851 2283191502003602992084277)
                  ·
                    refine ⟨214049203312837780507901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2283191502003602992084277 214049203312837780507901)
                    ·
                      rfl

theorem cell23_1250578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 2, 1, 2, 1, 2, 1, 5].length) (baseStart_1250578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250578 prefixEnd_1250578 := by exact prefixLift 1250578
  have htrace : WordTrace (prefixWord ++ tailWord_1250578) baseStart_1250578 baseEnd_1250578 := by
    simpa [prefixWord, tailWord_1250578, baseEnd_1250578] using wordTrace_append hprefix tailTrace_1250578
  have hstable : (prefixWord ++ tailWord_1250578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250578).length < 2 ^ (prefixWord ++ tailWord_1250578).sum := by decide
  have hdescent : baseEnd_1250578 < baseStart_1250578 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250584 : List Nat := [2, 1, 2, 3, 1, 3, 3, 2, 1, 2, 3]
def baseStart_1250584 : Nat := 118140960795 + 1250584 * 2 ^ 59
def prefixEnd_1250584 : Nat := 4983230072969 + 3 ^ 40 * 1250584 * 2
def baseEnd_1250584 : Nat := 642150690822440318048675

theorem tailTrace_1250584 : CollatzResearch.WordTrace tailWord_1250584 prefixEnd_1250584 642150690822440318048675 := by
  unfold tailWord_1250584
  simp only [CollatzResearch.WordTrace]
  refine ⟨22806272850677612794059403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30408363800903483725412537 22806272850677612794059403)
  ·
    refine ⟨34209409276016419191089105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22806272850677612794059403 34209409276016419191089105)
    ·
      refine ⟨25657056957012314393316829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34209409276016419191089105 25657056957012314393316829)
      ·
        refine ⟨9621396358879617897493811, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25657056957012314393316829 9621396358879617897493811)
        ·
          refine ⟨14432094538319426846240717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9621396358879617897493811 14432094538319426846240717)
          ·
            refine ⟨5412035451869785067340269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14432094538319426846240717 5412035451869785067340269)
            ·
              refine ⟨2029513294451169400252601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5412035451869785067340269 2029513294451169400252601)
              ·
                refine ⟨1522134970838377050189451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2029513294451169400252601 1522134970838377050189451)
                ·
                  refine ⟨2283202456257565575284177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522134970838377050189451 2283202456257565575284177)
                  ·
                    refine ⟨1712401842193174181463133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283202456257565575284177 1712401842193174181463133)
                    ·
                      refine ⟨642150690822440318048675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1712401842193174181463133 642150690822440318048675)
                      ·
                        rfl

theorem cell23_1250584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 3, 3, 2, 1, 2, 3].length) (baseStart_1250584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250584 prefixEnd_1250584 := by exact prefixLift 1250584
  have htrace : WordTrace (prefixWord ++ tailWord_1250584) baseStart_1250584 baseEnd_1250584 := by
    simpa [prefixWord, tailWord_1250584, baseEnd_1250584] using wordTrace_append hprefix tailTrace_1250584
  have hstable : (prefixWord ++ tailWord_1250584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250584).length < 2 ^ (prefixWord ++ tailWord_1250584).sum := by decide
  have hdescent : baseEnd_1250584 < baseStart_1250584 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250594 : List Nat := [3, 3, 1, 1, 4, 1, 1, 2, 1, 2, 4]
def baseStart_1250594 : Nat := 118140960795 + 1250594 * 2 ^ 59
def prefixEnd_1250594 : Nat := 4983230072969 + 3 ^ 40 * 1250594 * 2
def baseEnd_1250594 : Nat := 642155825628985278923629

theorem tailTrace_1250594 : CollatzResearch.WordTrace tailWord_1250594 prefixEnd_1250594 642155825628985278923629 := by
  unfold tailWord_1250594
  simp only [CollatzResearch.WordTrace]
  refine ⟨11403227607829749323995709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30408606954212664863988557 11403227607829749323995709)
  ·
    refine ⟨4276210352936155996498391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11403227607829749323995709 4276210352936155996498391)
    ·
      refine ⟨6414315529404233994747587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4276210352936155996498391 6414315529404233994747587)
      ·
        refine ⟨9621473294106350992121381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6414315529404233994747587 9621473294106350992121381)
        ·
          refine ⟨1804026242644940811022759, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9621473294106350992121381 1804026242644940811022759)
          ·
            refine ⟨2706039363967411216534139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804026242644940811022759 2706039363967411216534139)
            ·
              refine ⟨4059059045951116824801209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706039363967411216534139 4059059045951116824801209)
              ·
                refine ⟨3044294284463337618600907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4059059045951116824801209 3044294284463337618600907)
                ·
                  refine ⟨4566441426695006427901361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3044294284463337618600907 4566441426695006427901361)
                  ·
                    refine ⟨3424831070021254820926021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4566441426695006427901361 3424831070021254820926021)
                    ·
                      refine ⟨642155825628985278923629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3424831070021254820926021 642155825628985278923629)
                      ·
                        rfl

theorem cell23_1250594_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 1, 2, 1, 2, 4].length) (baseStart_1250594 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250594 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250594 prefixEnd_1250594 := by exact prefixLift 1250594
  have htrace : WordTrace (prefixWord ++ tailWord_1250594) baseStart_1250594 baseEnd_1250594 := by
    simpa [prefixWord, tailWord_1250594, baseEnd_1250594] using wordTrace_append hprefix tailTrace_1250594
  have hstable : (prefixWord ++ tailWord_1250594).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250594).length < 2 ^ (prefixWord ++ tailWord_1250594).sum := by decide
  have hdescent : baseEnd_1250594 < baseStart_1250594 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250594) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250597 : List Nat := [1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 3]
def baseStart_1250597 : Nat := 118140960795 + 1250597 * 2 ^ 59
def prefixEnd_1250597 : Nat := 4983230072969 + 3 ^ 40 * 1250597 * 2
def baseEnd_1250597 : Nat := 642157366070948767186115

theorem tailTrace_1250597 : CollatzResearch.WordTrace tailWord_1250597 prefixEnd_1250597 642157366070948767186115 := by
  unfold tailWord_1250597
  simp only [CollatzResearch.WordTrace]
  refine ⟨45613019850308128808342045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30408679900205419205561363 45613019850308128808342045)
  ·
    refine ⟨17104882443865548303128267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45613019850308128808342045 17104882443865548303128267)
    ·
      refine ⟨25657323665798322454692401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17104882443865548303128267 25657323665798322454692401)
      ·
        refine ⟨19242992749348741841019301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25657323665798322454692401 19242992749348741841019301)
        ·
          refine ⟨3608061140502889095191119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19242992749348741841019301 3608061140502889095191119)
          ·
            refine ⟨5412091710754333642786679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3608061140502889095191119 5412091710754333642786679)
            ·
              refine ⟨8118137566131500464180019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5412091710754333642786679 8118137566131500464180019)
              ·
                refine ⟨12177206349197250696270029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8118137566131500464180019 12177206349197250696270029)
                ·
                  refine ⟨4566452380948969011101261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12177206349197250696270029 4566452380948969011101261)
                  ·
                    refine ⟨1712419642855863379162973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4566452380948969011101261 1712419642855863379162973)
                    ·
                      refine ⟨642157366070948767186115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1712419642855863379162973 642157366070948767186115)
                      ·
                        rfl

theorem cell23_1250597_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 4, 1, 1, 1, 3, 3, 3].length) (baseStart_1250597 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250597 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250597 prefixEnd_1250597 := by exact prefixLift 1250597
  have htrace : WordTrace (prefixWord ++ tailWord_1250597) baseStart_1250597 baseEnd_1250597 := by
    simpa [prefixWord, tailWord_1250597, baseEnd_1250597] using wordTrace_append hprefix tailTrace_1250597
  have hstable : (prefixWord ++ tailWord_1250597).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250597).length < 2 ^ (prefixWord ++ tailWord_1250597).sum := by decide
  have hdescent : baseEnd_1250597 < baseStart_1250597 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250597) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250621 : List Nat := [1, 4, 1, 5, 2, 1, 1, 8]
def baseStart_1250621 : Nat := 118140960795 + 1250621 * 2 ^ 59
def prefixEnd_1250621 : Nat := 4983230072969 + 3 ^ 40 * 1250621 * 2
def baseEnd_1250621 : Nat := 23784062578024321232815

theorem tailTrace_1250621 : CollatzResearch.WordTrace tailWord_1250621 prefixEnd_1250621 23784062578024321232815 := by
  unfold tailWord_1250621
  simp only [CollatzResearch.WordTrace]
  refine ⟨45613895202221180907215717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30409263468147453938143811 45613895202221180907215717)
  ·
    refine ⟨8552605350416471420102947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45613895202221180907215717 8552605350416471420102947)
    ·
      refine ⟨12828908025624707130154421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8552605350416471420102947 12828908025624707130154421)
      ·
        refine ⟨1202710127402316293451977, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12828908025624707130154421 1202710127402316293451977)
        ·
          refine ⟨902032595551737220088983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1202710127402316293451977 902032595551737220088983)
          ·
            refine ⟨1353048893327605830133475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902032595551737220088983 1353048893327605830133475)
            ·
              refine ⟨2029573339991408745200213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353048893327605830133475 2029573339991408745200213)
              ·
                refine ⟨23784062578024321232815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2029573339991408745200213 23784062578024321232815)
                ·
                  rfl

theorem cell23_1250621_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 2, 1, 1, 8].length) (baseStart_1250621 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250621 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250621 prefixEnd_1250621 := by exact prefixLift 1250621
  have htrace : WordTrace (prefixWord ++ tailWord_1250621) baseStart_1250621 baseEnd_1250621 := by
    simpa [prefixWord, tailWord_1250621, baseEnd_1250621] using wordTrace_append hprefix tailTrace_1250621
  have hstable : (prefixWord ++ tailWord_1250621).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250621).length < 2 ^ (prefixWord ++ tailWord_1250621).sum := by decide
  have hdescent : baseEnd_1250621 < baseStart_1250621 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250621) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250728 : List Nat := [2, 1, 6, 1, 3, 1, 1, 1, 7]
def baseStart_1250728 : Nat := 118140960795 + 1250728 * 2 ^ 59
def prefixEnd_1250728 : Nat := 4983230072969 + 3 ^ 40 * 1250728 * 2
def baseEnd_1250728 : Nat := 71358292448520861627557

theorem tailTrace_1250728 : CollatzResearch.WordTrace tailWord_1250728 prefixEnd_1250728 71358292448520861627557 := by
  unfold tailWord_1250728
  simp only [CollatzResearch.WordTrace]
  refine ⟨22808898906416769090680419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30411865208555692120907225 22808898906416769090680419)
  ·
    refine ⟨34213348359625153636020629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22808898906416769090680419 34213348359625153636020629)
    ·
      refine ⟨1603750704357429076688467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34213348359625153636020629 1603750704357429076688467)
      ·
        refine ⟨2405626056536143615032701, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1603750704357429076688467 2405626056536143615032701)
        ·
          refine ⟨902109771201053855637263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2405626056536143615032701 902109771201053855637263)
          ·
            refine ⟨1353164656801580783455895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902109771201053855637263 1353164656801580783455895)
            ·
              refine ⟨2029746985202371175183843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353164656801580783455895 2029746985202371175183843)
              ·
                refine ⟨3044620477803556762775765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2029746985202371175183843 3044620477803556762775765)
                ·
                  refine ⟨71358292448520861627557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3044620477803556762775765 71358292448520861627557)
                  ·
                    rfl

theorem cell23_1250728_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 3, 1, 1, 1, 7].length) (baseStart_1250728 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250728 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250728 prefixEnd_1250728 := by exact prefixLift 1250728
  have htrace : WordTrace (prefixWord ++ tailWord_1250728) baseStart_1250728 baseEnd_1250728 := by
    simpa [prefixWord, tailWord_1250728, baseEnd_1250728] using wordTrace_append hprefix tailTrace_1250728
  have hstable : (prefixWord ++ tailWord_1250728).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250728).length < 2 ^ (prefixWord ++ tailWord_1250728).sum := by decide
  have hdescent : baseEnd_1250728 < baseStart_1250728 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250728) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250744 : List Nat := [2, 1, 2, 1, 2, 2, 2, 3, 2, 4, 2]
def baseStart_1250744 : Nat := 118140960795 + 1250744 * 2 ^ 59
def prefixEnd_1250744 : Nat := 4983230072969 + 3 ^ 40 * 1250744 * 2
def baseEnd_1250744 : Nat := 642232847727159692047939

theorem tailTrace_1250744 : CollatzResearch.WordTrace tailWord_1250744 prefixEnd_1250744 642232847727159692047939 := by
  unfold tailWord_1250744
  simp only [CollatzResearch.WordTrace]
  refine ⟨22809190690387786456971643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30412254253850381942628857 22809190690387786456971643)
  ·
    refine ⟨34213786035581679685457465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22809190690387786456971643 34213786035581679685457465)
    ·
      refine ⟨25660339526686259764093099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34213786035581679685457465 25660339526686259764093099)
      ·
        refine ⟨38490509290029389646139649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25660339526686259764093099 38490509290029389646139649)
        ·
          refine ⟨28867881967522042234604737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38490509290029389646139649 28867881967522042234604737)
          ·
            refine ⟨21650911475641531675953553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28867881967522042234604737 21650911475641531675953553)
            ·
              refine ⟨16238183606731148756965165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21650911475641531675953553 16238183606731148756965165)
              ·
                refine ⟨6089318852524180783861937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16238183606731148756965165 6089318852524180783861937)
                ·
                  refine ⟨4566989139393135587896453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6089318852524180783861937 4566989139393135587896453)
                  ·
                    refine ⟨856310463636212922730585, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4566989139393135587896453 856310463636212922730585)
                    ·
                      refine ⟨642232847727159692047939, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856310463636212922730585 642232847727159692047939)
                      ·
                        rfl

theorem cell23_1250744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 2, 3, 2, 4, 2].length) (baseStart_1250744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250744 prefixEnd_1250744 := by exact prefixLift 1250744
  have htrace : WordTrace (prefixWord ++ tailWord_1250744) baseStart_1250744 baseEnd_1250744 := by
    simpa [prefixWord, tailWord_1250744, baseEnd_1250744] using wordTrace_append hprefix tailTrace_1250744
  have hstable : (prefixWord ++ tailWord_1250744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250744).length < 2 ^ (prefixWord ++ tailWord_1250744).sum := by decide
  have hdescent : baseEnd_1250744 < baseStart_1250744 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250781 : List Nat := [1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 3]
def baseStart_1250781 : Nat := 118140960795 + 1250781 * 2 ^ 59
def prefixEnd_1250781 : Nat := 4983230072969 + 3 ^ 40 * 1250781 * 2
def baseEnd_1250781 : Nat := 642251846511376047285269

theorem tailTrace_1250781 : CollatzResearch.WordTrace tailWord_1250781 prefixEnd_1250781 642251846511376047285269 := by
  unfold tailWord_1250781
  simp only [CollatzResearch.WordTrace]
  refine ⟨45619730881641528233040197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30413153921094352155360131 45619730881641528233040197)
  ·
    refine ⟨8553699540307786543695037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45619730881641528233040197 8553699540307786543695037)
    ·
      refine ⟨3207637327615419953885639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8553699540307786543695037 3207637327615419953885639)
      ·
        refine ⟨4811455991423129930828459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3207637327615419953885639 4811455991423129930828459)
        ·
          refine ⟨7217183987134694896242689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4811455991423129930828459 7217183987134694896242689)
          ·
            refine ⟨5412887990351021172182017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7217183987134694896242689 5412887990351021172182017)
            ·
              refine ⟨4059665992763265879136513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5412887990351021172182017 4059665992763265879136513)
              ·
                refine ⟨3044749494572449409352385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4059665992763265879136513 3044749494572449409352385)
                ·
                  refine ⟨2283562120929337057014289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3044749494572449409352385 2283562120929337057014289)
                  ·
                    refine ⟨1712671590697002792760717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283562120929337057014289 1712671590697002792760717)
                    ·
                      refine ⟨642251846511376047285269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1712671590697002792760717 642251846511376047285269)
                      ·
                        rfl

theorem cell23_1250781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 2, 2, 2, 2, 2, 3].length) (baseStart_1250781 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250781 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250781 prefixEnd_1250781 := by exact prefixLift 1250781
  have htrace : WordTrace (prefixWord ++ tailWord_1250781) baseStart_1250781 baseEnd_1250781 := by
    simpa [prefixWord, tailWord_1250781, baseEnd_1250781] using wordTrace_append hprefix tailTrace_1250781
  have hstable : (prefixWord ++ tailWord_1250781).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250781).length < 2 ^ (prefixWord ++ tailWord_1250781).sum := by decide
  have hdescent : baseEnd_1250781 < baseStart_1250781 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250871 : List Nat := [1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 3]
def baseStart_1250871 : Nat := 118140960795 + 1250871 * 2 ^ 59
def prefixEnd_1250871 : Nat := 4983230072969 + 3 ^ 40 * 1250871 * 2
def baseEnd_1250871 : Nat := 642298059770280695159855

theorem tailTrace_1250871 : CollatzResearch.WordTrace tailWord_1250871 prefixEnd_1250871 642298059770280695159855 := by
  unfold tailWord_1250871
  simp only [CollatzResearch.WordTrace]
  refine ⟨45623013451315473603816467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30415342300876982402544311 45623013451315473603816467)
  ·
    refine ⟨68434520176973210405724701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45623013451315473603816467 68434520176973210405724701)
    ·
      refine ⟨25662945066364953902146763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68434520176973210405724701 25662945066364953902146763)
      ·
        refine ⟨38494417599547430853220145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25662945066364953902146763 38494417599547430853220145)
        ·
          refine ⟨28870813199660573139915109, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38494417599547430853220145 28870813199660573139915109)
          ·
            refine ⟨5413277474936357463734083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28870813199660573139915109 5413277474936357463734083)
            ·
              refine ⟨8119916212404536195601125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5413277474936357463734083 8119916212404536195601125)
              ·
                refine ⟨1522484289825850536675211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8119916212404536195601125 1522484289825850536675211)
                ·
                  refine ⟨2283726434738775805012817, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522484289825850536675211 2283726434738775805012817)
                  ·
                    refine ⟨1712794826054081853759613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2283726434738775805012817 1712794826054081853759613)
                    ·
                      refine ⟨642298059770280695159855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1712794826054081853759613 642298059770280695159855)
                      ·
                        rfl

theorem cell23_1250871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 4, 1, 4, 1, 2, 3].length) (baseStart_1250871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250871 prefixEnd_1250871 := by exact prefixLift 1250871
  have htrace : WordTrace (prefixWord ++ tailWord_1250871) baseStart_1250871 baseEnd_1250871 := by
    simpa [prefixWord, tailWord_1250871, baseEnd_1250871] using wordTrace_append hprefix tailTrace_1250871
  have hstable : (prefixWord ++ tailWord_1250871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250871).length < 2 ^ (prefixWord ++ tailWord_1250871).sum := by decide
  have hdescent : baseEnd_1250871 < baseStart_1250871 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250928 : List Nat := [2, 1, 1, 1, 6, 2, 1, 1, 3, 3, 2]
def baseStart_1250928 : Nat := 118140960795 + 1250928 * 2 ^ 59
def prefixEnd_1250928 : Nat := 4983230072969 + 3 ^ 40 * 1250928 * 2
def baseEnd_1250928 : Nat := 642327328167586972147093

theorem tailTrace_1250928 : CollatzResearch.WordTrace tailWord_1250928 prefixEnd_1250928 642327328167586972147093 := by
  unfold tailWord_1250928
  simp only [CollatzResearch.WordTrace]
  refine ⟨22812546206054486169320719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30416728274739314892427625 22812546206054486169320719)
  ·
    refine ⟨34218819309081729253981079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22812546206054486169320719 34218819309081729253981079)
    ·
      refine ⟨51328228963622593880971619, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34218819309081729253981079 51328228963622593880971619)
      ·
        refine ⟨76992343445433890821457429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51328228963622593880971619 76992343445433890821457429)
        ·
          refine ⟨3609016099004713632255817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 76992343445433890821457429 3609016099004713632255817)
          ·
            refine ⟨2706762074253535224191863, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3609016099004713632255817 2706762074253535224191863)
            ·
              refine ⟨4060143111380302836287795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2706762074253535224191863 4060143111380302836287795)
              ·
                refine ⟨6090214667070454254431693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060143111380302836287795 6090214667070454254431693)
                ·
                  refine ⟨2283830500151420345411885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6090214667070454254431693 2283830500151420345411885)
                  ·
                    refine ⟨856436437556782629529457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2283830500151420345411885 856436437556782629529457)
                    ·
                      refine ⟨642327328167586972147093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856436437556782629529457 642327328167586972147093)
                      ·
                        rfl

theorem cell23_1250928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 2, 1, 1, 3, 3, 2].length) (baseStart_1250928 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250928 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250928 prefixEnd_1250928 := by exact prefixLift 1250928
  have htrace : WordTrace (prefixWord ++ tailWord_1250928) baseStart_1250928 baseEnd_1250928 := by
    simpa [prefixWord, tailWord_1250928, baseEnd_1250928] using wordTrace_append hprefix tailTrace_1250928
  have hstable : (prefixWord ++ tailWord_1250928).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250928).length < 2 ^ (prefixWord ++ tailWord_1250928).sum := by decide
  have hdescent : baseEnd_1250928 < baseStart_1250928 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250944 : List Nat := [2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5]
def baseStart_1250944 : Nat := 118140960795 + 1250944 * 2 ^ 59
def prefixEnd_1250944 : Nat := 4983230072969 + 3 ^ 40 * 1250944 * 2
def baseEnd_1250944 : Nat := 642335543858058909547019

theorem tailTrace_1250944 : CollatzResearch.WordTrace tailWord_1250944 prefixEnd_1250944 642335543858058909547019 := by
  unfold tailWord_1250944
  simp only [CollatzResearch.WordTrace]
  refine ⟨22812837990025503535611943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30417117320034004714149257 22812837990025503535611943)
  ·
    refine ⟨34219256985038255303417915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22812837990025503535611943 34219256985038255303417915)
    ·
      refine ⟨51328885477557382955126873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34219256985038255303417915 51328885477557382955126873)
      ·
        refine ⟨38496664108168037216345155, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51328885477557382955126873 38496664108168037216345155)
        ·
          refine ⟨57744996162252055824517733, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38496664108168037216345155 57744996162252055824517733)
          ·
            refine ⟨10827186780422260467097075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57744996162252055824517733 10827186780422260467097075)
            ·
              refine ⟨16240780170633390700645613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10827186780422260467097075 16240780170633390700645613)
              ·
                refine ⟨6090292563987521512742105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16240780170633390700645613 6090292563987521512742105)
                ·
                  refine ⟨4567719422990641134556579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6090292563987521512742105 4567719422990641134556579)
                  ·
                    refine ⟨6851579134485961701834869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4567719422990641134556579 6851579134485961701834869)
                    ·
                      refine ⟨642335543858058909547019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6851579134485961701834869 642335543858058909547019)
                      ·
                        rfl

theorem cell23_1250944_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 1, 3, 2, 1, 5].length) (baseStart_1250944 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250944 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250944 prefixEnd_1250944 := by exact prefixLift 1250944
  have htrace : WordTrace (prefixWord ++ tailWord_1250944) baseStart_1250944 baseEnd_1250944 := by
    simpa [prefixWord, tailWord_1250944, baseEnd_1250944] using wordTrace_append hprefix tailTrace_1250944
  have hstable : (prefixWord ++ tailWord_1250944).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250944).length < 2 ^ (prefixWord ++ tailWord_1250944).sum := by decide
  have hdescent : baseEnd_1250944 < baseStart_1250944 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250944) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1250952 : List Nat := [2, 1, 3, 5, 1, 1, 2, 2, 2, 1, 3]
def baseStart_1250952 : Nat := 118140960795 + 1250952 * 2 ^ 59
def prefixEnd_1250952 : Nat := 4983230072969 + 3 ^ 40 * 1250952 * 2
def baseEnd_1250952 : Nat := 642339651703294878246983

theorem tailTrace_1250952 : CollatzResearch.WordTrace tailWord_1250952 prefixEnd_1250952 642339651703294878246983 := by
  unfold tailWord_1250952
  simp only [CollatzResearch.WordTrace]
  refine ⟨22812983882011012218757555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30417311842681349625010073 22812983882011012218757555)
  ·
    refine ⟨34219475823016518328136333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22812983882011012218757555 34219475823016518328136333)
    ·
      refine ⟨12832303433631194373051125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34219475823016518328136333 12832303433631194373051125)
      ·
        refine ⟨1203028446902924472473543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12832303433631194373051125 1203028446902924472473543)
        ·
          refine ⟨1804542670354386708710315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203028446902924472473543 1804542670354386708710315)
          ·
            refine ⟨2706814005531580063065473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804542670354386708710315 2706814005531580063065473)
            ·
              refine ⟨2030110504148685047299105, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2706814005531580063065473 2030110504148685047299105)
              ·
                refine ⟨1522582878111513785474329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030110504148685047299105 1522582878111513785474329)
                ·
                  refine ⟨1141937158583635339105747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522582878111513785474329 1141937158583635339105747)
                  ·
                    refine ⟨1712905737875453008658621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1141937158583635339105747 1712905737875453008658621)
                    ·
                      refine ⟨642339651703294878246983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1712905737875453008658621 642339651703294878246983)
                      ·
                        rfl

theorem cell23_1250952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 5, 1, 1, 2, 2, 2, 1, 3].length) (baseStart_1250952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1250952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1250952 prefixEnd_1250952 := by exact prefixLift 1250952
  have htrace : WordTrace (prefixWord ++ tailWord_1250952) baseStart_1250952 baseEnd_1250952 := by
    simpa [prefixWord, tailWord_1250952, baseEnd_1250952] using wordTrace_append hprefix tailTrace_1250952
  have hstable : (prefixWord ++ tailWord_1250952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1250952).length < 2 ^ (prefixWord ++ tailWord_1250952).sum := by decide
  have hdescent : baseEnd_1250952 < baseStart_1250952 := by decide
  rcases family_descends (prefixWord ++ tailWord_1250952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251051 : List Nat := [1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 3]
def baseStart_1251051 : Nat := 118140960795 + 1251051 * 2 ^ 59
def prefixEnd_1251051 : Nat := 4983230072969 + 3 ^ 40 * 1251051 * 2
def baseEnd_1251051 : Nat := 642390486288089990909027

theorem tailTrace_1251051 : CollatzResearch.WordTrace tailWord_1251051 prefixEnd_1251051 642390486288089990909027 := by
  unfold tailWord_1251051
  simp only [CollatzResearch.WordTrace]
  refine ⟨45629578590663364345369007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30419719060442242896912671 45629578590663364345369007)
  ·
    refine ⟨68444367885995046518053511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45629578590663364345369007 68444367885995046518053511)
    ·
      refine ⟨102666551828992569777080267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68444367885995046518053511 102666551828992569777080267)
      ·
        refine ⟨153999827743488854665620401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102666551828992569777080267 153999827743488854665620401)
        ·
          refine ⟨115499870807616640999215301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 153999827743488854665620401 115499870807616640999215301)
          ·
            refine ⟨21656225776428120187352869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 115499870807616640999215301 21656225776428120187352869)
            ·
              refine ⟨4060542333080272535128663, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21656225776428120187352869 4060542333080272535128663)
              ·
                refine ⟨6090813499620408802692995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4060542333080272535128663 6090813499620408802692995)
                ·
                  refine ⟨9136220249430613204039493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6090813499620408802692995 9136220249430613204039493)
                  ·
                    refine ⟨1713041296768239975757405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9136220249430613204039493 1713041296768239975757405)
                    ·
                      refine ⟨642390486288089990909027, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1713041296768239975757405 642390486288089990909027)
                      ·
                        rfl

theorem cell23_1251051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 4, 4, 1, 1, 4, 3].length) (baseStart_1251051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251051 prefixEnd_1251051 := by exact prefixLift 1251051
  have htrace : WordTrace (prefixWord ++ tailWord_1251051) baseStart_1251051 baseEnd_1251051 := by
    simpa [prefixWord, tailWord_1251051, baseEnd_1251051] using wordTrace_append hprefix tailTrace_1251051
  have hstable : (prefixWord ++ tailWord_1251051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251051).length < 2 ^ (prefixWord ++ tailWord_1251051).sum := by decide
  have hdescent : baseEnd_1251051 < baseStart_1251051 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251068 : List Nat := [2, 2, 2, 1, 3, 1, 3, 2, 2, 2, 3]
def baseStart_1251068 : Nat := 118140960795 + 1251068 * 2 ^ 59
def prefixEnd_1251068 : Nat := 4983230072969 + 3 ^ 40 * 1251068 * 2
def baseEnd_1251068 : Nat := 642399215459216424396449

theorem tailTrace_1251068 : CollatzResearch.WordTrace tailWord_1251068 prefixEnd_1251068 642399215459216424396449 := by
  unfold tailWord_1251068
  simp only [CollatzResearch.WordTrace]
  refine ⟨22815099315800888124368929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30420132421067850832491905 22815099315800888124368929)
  ·
    refine ⟨17111324486850666093276697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22815099315800888124368929 17111324486850666093276697)
    ·
      refine ⟨12833493365137999569957523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17111324486850666093276697 12833493365137999569957523)
      ·
        refine ⟨19250240047706999354936285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12833493365137999569957523 19250240047706999354936285)
        ·
          refine ⟨7218840017890124758101107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19250240047706999354936285 7218840017890124758101107)
          ·
            refine ⟨10828260026835187137151661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7218840017890124758101107 10828260026835187137151661)
            ·
              refine ⟨4060597510063195176431873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10828260026835187137151661 4060597510063195176431873)
              ·
                refine ⟨3045448132547396382323905, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4060597510063195176431873 3045448132547396382323905)
                ·
                  refine ⟨2284086099410547286742929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3045448132547396382323905 2284086099410547286742929)
                  ·
                    refine ⟨1713064574557910465057197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2284086099410547286742929 1713064574557910465057197)
                    ·
                      refine ⟨642399215459216424396449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1713064574557910465057197 642399215459216424396449)
                      ·
                        rfl

theorem cell23_1251068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 1, 3, 2, 2, 2, 3].length) (baseStart_1251068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251068 prefixEnd_1251068 := by exact prefixLift 1251068
  have htrace : WordTrace (prefixWord ++ tailWord_1251068) baseStart_1251068 baseEnd_1251068 := by
    simpa [prefixWord, tailWord_1251068, baseEnd_1251068] using wordTrace_append hprefix tailTrace_1251068
  have hstable : (prefixWord ++ tailWord_1251068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251068).length < 2 ^ (prefixWord ++ tailWord_1251068).sum := by decide
  have hdescent : baseEnd_1251068 < baseStart_1251068 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251126 : List Nat := [5, 1, 2, 2, 1, 3, 2, 2, 1, 4]
def baseStart_1251126 : Nat := 118140960795 + 1251126 * 2 ^ 59
def prefixEnd_1251126 : Nat := 4983230072969 + 3 ^ 40 * 1251126 * 2
def baseEnd_1251126 : Nat := 214142999112392399157061

theorem tailTrace_1251126 : CollatzResearch.WordTrace tailWord_1251126 prefixEnd_1251126 214142999112392399157061 := by
  unfold tailWord_1251126
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852019629086978259646827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30421542710261101436232821 2852019629086978259646827)
  ·
    refine ⟨4278029443630467389470241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852019629086978259646827 4278029443630467389470241)
    ·
      refine ⟨3208522082722850542102681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4278029443630467389470241 3208522082722850542102681)
      ·
        refine ⟨2406391562042137906577011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3208522082722850542102681 2406391562042137906577011)
        ·
          refine ⟨3609587343063206859865517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406391562042137906577011 3609587343063206859865517)
          ·
            refine ⟨1353595253648702572449569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3609587343063206859865517 1353595253648702572449569)
            ·
              refine ⟨1015196440236526929337177, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353595253648702572449569 1015196440236526929337177)
              ·
                refine ⟨761397330177395197002883, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015196440236526929337177 761397330177395197002883)
                ·
                  refine ⟨1142095995266092795504325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761397330177395197002883 1142095995266092795504325)
                  ·
                    refine ⟨214142999112392399157061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142095995266092795504325 214142999112392399157061)
                    ·
                      rfl

theorem cell23_1251126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 2, 1, 3, 2, 2, 1, 4].length) (baseStart_1251126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251126 prefixEnd_1251126 := by exact prefixLift 1251126
  have htrace : WordTrace (prefixWord ++ tailWord_1251126) baseStart_1251126 baseEnd_1251126 := by
    simpa [prefixWord, tailWord_1251126, baseEnd_1251126] using wordTrace_append hprefix tailTrace_1251126
  have hstable : (prefixWord ++ tailWord_1251126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251126).length < 2 ^ (prefixWord ++ tailWord_1251126).sum := by decide
  have hdescent : baseEnd_1251126 < baseStart_1251126 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251141 : List Nat := [1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 5]
def baseStart_1251141 : Nat := 118140960795 + 1251141 * 2 ^ 59
def prefixEnd_1251141 : Nat := 4983230072969 + 3 ^ 40 * 1251141 * 2
def baseEnd_1251141 : Nat := 642436699546994638783613

theorem tailTrace_1251141 : CollatzResearch.WordTrace tailWord_1251141 prefixEnd_1251141 642436699546994638783613 := by
  unfold tailWord_1251141
  simp only [CollatzResearch.WordTrace]
  refine ⟨45632861160337309716145277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30421907440224873144096851 45632861160337309716145277)
  ·
    refine ⟨17112322935126491143554479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45632861160337309716145277 17112322935126491143554479)
    ·
      refine ⟨25668484402689736715331719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17112322935126491143554479 25668484402689736715331719)
      ·
        refine ⟨38502726604034605072997579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25668484402689736715331719 38502726604034605072997579)
        ·
          refine ⟨57754089906051907609496369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38502726604034605072997579 57754089906051907609496369)
          ·
            refine ⟨43315567429538930707122277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57754089906051907609496369 43315567429538930707122277)
            ·
              refine ⟨8121668893038549507585427, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43315567429538930707122277 8121668893038549507585427)
              ·
                refine ⟨12182503339557824261378141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8121668893038549507585427 12182503339557824261378141)
                ·
                  refine ⟨4568438752334184098016803, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12182503339557824261378141 4568438752334184098016803)
                  ·
                    refine ⟨6852658128501276147025205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4568438752334184098016803 6852658128501276147025205)
                    ·
                      refine ⟨642436699546994638783613, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6852658128501276147025205 642436699546994638783613)
                      ·
                        rfl

theorem cell23_1251141_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 4, 1, 3, 1, 5].length) (baseStart_1251141 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251141 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251141 prefixEnd_1251141 := by exact prefixLift 1251141
  have htrace : WordTrace (prefixWord ++ tailWord_1251141) baseStart_1251141 baseEnd_1251141 := by
    simpa [prefixWord, tailWord_1251141, baseEnd_1251141] using wordTrace_append hprefix tailTrace_1251141
  have hstable : (prefixWord ++ tailWord_1251141).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251141).length < 2 ^ (prefixWord ++ tailWord_1251141).sum := by decide
  have hdescent : baseEnd_1251141 < baseStart_1251141 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251141) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251159 : List Nat := [1, 1, 3, 2, 6, 1, 1, 1, 2, 3, 2]
def baseStart_1251159 : Nat := 118140960795 + 1251159 * 2 ^ 59
def prefixEnd_1251159 : Nat := 4983230072969 + 3 ^ 40 * 1251159 * 2
def baseEnd_1251159 : Nat := 642445942198775568358531

theorem tailTrace_1251159 : CollatzResearch.WordTrace tailWord_1251159 prefixEnd_1251159 642445942198775568358531 := by
  unfold tailWord_1251159
  simp only [CollatzResearch.WordTrace]
  refine ⟨45633517674272098790300531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30422345116181399193533687 45633517674272098790300531)
  ·
    refine ⟨68450276511408148185450797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45633517674272098790300531 68450276511408148185450797)
    ·
      refine ⟨25668853691778055569544049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68450276511408148185450797 25668853691778055569544049)
      ·
        refine ⟨19251640268833541677158037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25668853691778055569544049 19251640268833541677158037)
        ·
          refine ⟨902420637601572266116783, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 19251640268833541677158037 902420637601572266116783)
          ·
            refine ⟨1353630956402358399175175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902420637601572266116783 1353630956402358399175175)
            ·
              refine ⟨2030446434603537598762763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1353630956402358399175175 2030446434603537598762763)
              ·
                refine ⟨3045669651905306398144145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030446434603537598762763 3045669651905306398144145)
                ·
                  refine ⟨2284252238928979798608109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3045669651905306398144145 2284252238928979798608109)
                  ·
                    refine ⟨856594589598367424478041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284252238928979798608109 856594589598367424478041)
                    ·
                      refine ⟨642445942198775568358531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856594589598367424478041 642445942198775568358531)
                      ·
                        rfl

theorem cell23_1251159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 6, 1, 1, 1, 2, 3, 2].length) (baseStart_1251159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251159 prefixEnd_1251159 := by exact prefixLift 1251159
  have htrace : WordTrace (prefixWord ++ tailWord_1251159) baseStart_1251159 baseEnd_1251159 := by
    simpa [prefixWord, tailWord_1251159, baseEnd_1251159] using wordTrace_append hprefix tailTrace_1251159
  have hstable : (prefixWord ++ tailWord_1251159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251159).length < 2 ^ (prefixWord ++ tailWord_1251159).sum := by decide
  have hdescent : baseEnd_1251159 < baseStart_1251159 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251168 : List Nat := [2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4]
def baseStart_1251168 : Nat := 118140960795 + 1251168 * 2 ^ 59
def prefixEnd_1251168 : Nat := 4983230072969 + 3 ^ 40 * 1251168 * 2
def baseEnd_1251168 : Nat := 642450563524666033145989

theorem tailTrace_1251168 : CollatzResearch.WordTrace tailWord_1251168 prefixEnd_1251168 642450563524666033145989 := by
  unfold tailWord_1251168
  simp only [CollatzResearch.WordTrace]
  refine ⟨22816922965619746663689079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30422563954159662218252105 22816922965619746663689079)
  ·
    refine ⟨34225384448429619995533619, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22816922965619746663689079 34225384448429619995533619)
    ·
      refine ⟨51338076672644429993300429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34225384448429619995533619 51338076672644429993300429)
      ·
        refine ⟨19251778752241661247487661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51338076672644429993300429 19251778752241661247487661)
        ·
          refine ⟨7219417032090622967807873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 19251778752241661247487661 7219417032090622967807873)
          ·
            refine ⟨5414562774067967225855905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7219417032090622967807873 5414562774067967225855905)
            ·
              refine ⟨4060922080550975419391929, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5414562774067967225855905 4060922080550975419391929)
              ·
                refine ⟨3045691560413231564543947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4060922080550975419391929 3045691560413231564543947)
                ·
                  refine ⟨4568537340619847346815921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3045691560413231564543947 4568537340619847346815921)
                  ·
                    refine ⟨3426403005464885510111941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4568537340619847346815921 3426403005464885510111941)
                    ·
                      refine ⟨642450563524666033145989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3426403005464885510111941 642450563524666033145989)
                      ·
                        rfl

theorem cell23_1251168_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 2, 2, 1, 2, 4].length) (baseStart_1251168 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251168 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251168 prefixEnd_1251168 := by exact prefixLift 1251168
  have htrace : WordTrace (prefixWord ++ tailWord_1251168) baseStart_1251168 baseEnd_1251168 := by
    simpa [prefixWord, tailWord_1251168, baseEnd_1251168] using wordTrace_append hprefix tailTrace_1251168
  have hstable : (prefixWord ++ tailWord_1251168).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251168).length < 2 ^ (prefixWord ++ tailWord_1251168).sum := by decide
  have hdescent : baseEnd_1251168 < baseStart_1251168 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251168) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251175 : List Nat := [1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 3]
def baseStart_1251175 : Nat := 118140960795 + 1251175 * 2 ^ 59
def prefixEnd_1251175 : Nat := 4983230072969 + 3 ^ 40 * 1251175 * 2
def baseEnd_1251175 : Nat := 642454157889247505758457

theorem tailTrace_1251175 : CollatzResearch.WordTrace tailWord_1251175 prefixEnd_1251175 642454157889247505758457 := by
  unfold tailWord_1251175
  simp only [CollatzResearch.WordTrace]
  refine ⟨45634101242214133522882979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30422734161476089015255319 45634101242214133522882979)
  ·
    refine ⟨68451151863321200284324469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45634101242214133522882979 68451151863321200284324469)
    ·
      refine ⟨6417295487186362526655419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 68451151863321200284324469 6417295487186362526655419)
      ·
        refine ⟨9625943230779543789983129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6417295487186362526655419 9625943230779543789983129)
        ·
          refine ⟨7219457423084657842487347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9625943230779543789983129 7219457423084657842487347)
          ·
            refine ⟨10829186134626986763731021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219457423084657842487347 10829186134626986763731021)
            ·
              refine ⟨4060944800485120036399133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10829186134626986763731021 4060944800485120036399133)
              ·
                refine ⟨1522854300181920013649675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4060944800485120036399133 1522854300181920013649675)
                ·
                  refine ⟨2284281450272880020474513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1522854300181920013649675 2284281450272880020474513)
                  ·
                    refine ⟨1713211087704660015355885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2284281450272880020474513 1713211087704660015355885)
                    ·
                      refine ⟨642454157889247505758457, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1713211087704660015355885 642454157889247505758457)
                      ·
                        rfl

theorem cell23_1251175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 1, 3, 3, 1, 2, 3].length) (baseStart_1251175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251175 prefixEnd_1251175 := by exact prefixLift 1251175
  have htrace : WordTrace (prefixWord ++ tailWord_1251175) baseStart_1251175 baseEnd_1251175 := by
    simpa [prefixWord, tailWord_1251175, baseEnd_1251175] using wordTrace_append hprefix tailTrace_1251175
  have hstable : (prefixWord ++ tailWord_1251175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251175).length < 2 ^ (prefixWord ++ tailWord_1251175).sum := by decide
  have hdescent : baseEnd_1251175 < baseStart_1251175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251182 : List Nat := [4, 1, 2, 3, 1, 1, 3, 2, 2, 4]
def baseStart_1251182 : Nat := 118140960795 + 1251182 * 2 ^ 59
def prefixEnd_1251182 : Nat := 4983230072969 + 3 ^ 40 * 1251182 * 2
def baseEnd_1251182 : Nat := 214152584084609659456975

theorem tailTrace_1251182 : CollatzResearch.WordTrace tailWord_1251182 prefixEnd_1251182 214152584084609659456975 := by
  unfold tailWord_1251182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5704294569148596714798475, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30422904368792515812258533 5704294569148596714798475)
  ·
    refine ⟨8556441853722895072197713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5704294569148596714798475 8556441853722895072197713)
    ·
      refine ⟨6417331390292171304148285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8556441853722895072197713 6417331390292171304148285)
      ·
        refine ⟨2406499271359564239055607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6417331390292171304148285 2406499271359564239055607)
        ·
          refine ⟨3609748907039346358583411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2406499271359564239055607 3609748907039346358583411)
          ·
            refine ⟨5414623360559019537875117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3609748907039346358583411 5414623360559019537875117)
            ·
              refine ⟨2030483760209632326703169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5414623360559019537875117 2030483760209632326703169)
              ·
                refine ⟨1522862820157224245027377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2030483760209632326703169 1522862820157224245027377)
                ·
                  refine ⟨1142147115117918183770533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1522862820157224245027377 1142147115117918183770533)
                  ·
                    refine ⟨214152584084609659456975, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142147115117918183770533 214152584084609659456975)
                    ·
                      rfl

theorem cell23_1251182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 1, 1, 3, 2, 2, 4].length) (baseStart_1251182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251182 prefixEnd_1251182 := by exact prefixLift 1251182
  have htrace : WordTrace (prefixWord ++ tailWord_1251182) baseStart_1251182 baseEnd_1251182 := by
    simpa [prefixWord, tailWord_1251182, baseEnd_1251182] using wordTrace_append hprefix tailTrace_1251182
  have hstable : (prefixWord ++ tailWord_1251182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251182).length < 2 ^ (prefixWord ++ tailWord_1251182).sum := by decide
  have hdescent : baseEnd_1251182 < baseStart_1251182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251189 : List Nat := [1, 3, 4, 1, 1, 1, 1, 6, 1, 2, 2]
def baseStart_1251189 : Nat := 118140960795 + 1251189 * 2 ^ 59
def prefixEnd_1251189 : Nat := 4983230072969 + 3 ^ 40 * 1251189 * 2
def baseEnd_1251189 : Nat := 642461346618410450983393

theorem tailTrace_1251189 : CollatzResearch.WordTrace tailWord_1251189 prefixEnd_1251189 642461346618410450983393 := by
  unfold tailWord_1251189
  simp only [CollatzResearch.WordTrace]
  refine ⟨45634611864163413913892621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30423074576108942609261747 45634611864163413913892621)
  ·
    refine ⟨17112979449061280217709733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45634611864163413913892621 17112979449061280217709733)
    ·
      refine ⟨3208683646698990040820575, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 17112979449061280217709733 3208683646698990040820575)
      ·
        refine ⟨4813025470048485061230863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3208683646698990040820575 4813025470048485061230863)
        ·
          refine ⟨7219538205072727591846295, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813025470048485061230863 7219538205072727591846295)
          ·
            refine ⟨10829307307609091387769443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7219538205072727591846295 10829307307609091387769443)
            ·
              refine ⟨16243960961413637081654165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10829307307609091387769443 16243960961413637081654165)
              ·
                refine ⟨761435670066264238202539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 16243960961413637081654165 761435670066264238202539)
                ·
                  refine ⟨1142153505099396357303809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761435670066264238202539 1142153505099396357303809)
                  ·
                    refine ⟨856615128824547267977857, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1142153505099396357303809 856615128824547267977857)
                    ·
                      refine ⟨642461346618410450983393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856615128824547267977857 642461346618410450983393)
                      ·
                        rfl

theorem cell23_1251189_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 6, 1, 2, 2].length) (baseStart_1251189 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251189 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251189 prefixEnd_1251189 := by exact prefixLift 1251189
  have htrace : WordTrace (prefixWord ++ tailWord_1251189) baseStart_1251189 baseEnd_1251189 := by
    simpa [prefixWord, tailWord_1251189, baseEnd_1251189] using wordTrace_append hprefix tailTrace_1251189
  have hstable : (prefixWord ++ tailWord_1251189).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251189).length < 2 ^ (prefixWord ++ tailWord_1251189).sum := by decide
  have hdescent : baseEnd_1251189 < baseStart_1251189 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251189) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251240 : List Nat := [2, 1, 6, 2, 1, 1, 3, 2, 1, 2, 2]
def baseStart_1251240 : Nat := 118140960795 + 1251240 * 2 ^ 59
def prefixEnd_1251240 : Nat := 4983230072969 + 3 ^ 40 * 1251240 * 2
def baseEnd_1251240 : Nat := 642487534131789751445659

theorem tailTrace_1251240 : CollatzResearch.WordTrace tailWord_1251240 prefixEnd_1251240 642487534131789751445659 := by
  unfold tailWord_1251240
  simp only [CollatzResearch.WordTrace]
  refine ⟨22818235993489324811999587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30424314657985766415999449 22818235993489324811999587)
  ·
    refine ⟨34227353990233987217999381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22818235993489324811999587 34227353990233987217999381)
    ·
      refine ⟨1604407218292218150843721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 34227353990233987217999381 1604407218292218150843721)
      ·
        refine ⟨1203305413719163613132791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1604407218292218150843721 1203305413719163613132791)
        ·
          refine ⟨1804958120578745419699187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203305413719163613132791 1804958120578745419699187)
          ·
            refine ⟨2707437180868118129548781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1804958120578745419699187 2707437180868118129548781)
            ·
              refine ⟨1015288942825544298580793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707437180868118129548781 1015288942825544298580793)
              ·
                refine ⟨761466707119158223935595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015288942825544298580793 761466707119158223935595)
                ·
                  refine ⟨1142200060678737335903393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761466707119158223935595 1142200060678737335903393)
                  ·
                    refine ⟨856650045509053001927545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1142200060678737335903393 856650045509053001927545)
                    ·
                      refine ⟨642487534131789751445659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856650045509053001927545 642487534131789751445659)
                      ·
                        rfl

theorem cell23_1251240_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 2, 1, 1, 3, 2, 1, 2, 2].length) (baseStart_1251240 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251240 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251240 prefixEnd_1251240 := by exact prefixLift 1251240
  have htrace : WordTrace (prefixWord ++ tailWord_1251240) baseStart_1251240 baseEnd_1251240 := by
    simpa [prefixWord, tailWord_1251240, baseEnd_1251240] using wordTrace_append hprefix tailTrace_1251240
  have hstable : (prefixWord ++ tailWord_1251240).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251240).length < 2 ^ (prefixWord ++ tailWord_1251240).sum := by decide
  have hdescent : baseEnd_1251240 < baseStart_1251240 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251240) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251241 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 6]
def baseStart_1251241 : Nat := 118140960795 + 1251241 * 2 ^ 59
def prefixEnd_1251241 : Nat := 4983230072969 + 3 ^ 40 * 1251241 * 2
def baseEnd_1251241 : Nat := 642488047612444247533153

theorem tailTrace_1251241 : CollatzResearch.WordTrace tailWord_1251241 prefixEnd_1251241 642488047612444247533153 := by
  unfold tailWord_1251241
  simp only [CollatzResearch.WordTrace]
  refine ⟨45636508459975026794785577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30424338973316684529857051 45636508459975026794785577)
  ·
    refine ⟨34227381344981270096089183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45636508459975026794785577 34227381344981270096089183)
    ·
      refine ⟨51341072017471905144133775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34227381344981270096089183 51341072017471905144133775)
      ·
        refine ⟨77011608026207857716200663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51341072017471905144133775 77011608026207857716200663)
        ·
          refine ⟨115517412039311786574300995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77011608026207857716200663 115517412039311786574300995)
          ·
            refine ⟨173276118058967679861451493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115517412039311786574300995 173276118058967679861451493)
            ·
              refine ⟨32489272136056439974022155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 173276118058967679861451493 32489272136056439974022155)
              ·
                refine ⟨48733908204084659961033233, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32489272136056439974022155 48733908204084659961033233)
                ·
                  refine ⟨36550431153063494970774925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 48733908204084659961033233 36550431153063494970774925)
                  ·
                    refine ⟨13706411682398810614040597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 36550431153063494970774925 13706411682398810614040597)
                    ·
                      refine ⟨642488047612444247533153, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13706411682398810614040597 642488047612444247533153)
                      ·
                        rfl

theorem cell23_1251241_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 2, 3, 6].length) (baseStart_1251241 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251241 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251241 prefixEnd_1251241 := by exact prefixLift 1251241
  have htrace : WordTrace (prefixWord ++ tailWord_1251241) baseStart_1251241 baseEnd_1251241 := by
    simpa [prefixWord, tailWord_1251241, baseEnd_1251241] using wordTrace_append hprefix tailTrace_1251241
  have hstable : (prefixWord ++ tailWord_1251241).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251241).length < 2 ^ (prefixWord ++ tailWord_1251241).sum := by decide
  have hdescent : baseEnd_1251241 < baseStart_1251241 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251241) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251332 : List Nat := [2, 3, 2, 4, 1, 1, 1, 1, 1, 7]
def baseStart_1251332 : Nat := 118140960795 + 1251332 * 2 ^ 59
def prefixEnd_1251332 : Nat := 4983230072969 + 3 ^ 40 * 1251332 * 2
def baseEnd_1251332 : Nat := 214178258117334463831745

theorem tailTrace_1251332 : CollatzResearch.WordTrace tailWord_1251332 prefixEnd_1251332 214178258117334463831745 := by
  unfold tailWord_1251332
  simp only [CollatzResearch.WordTrace]
  refine ⟨22819913751322674668174125, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30426551668430232890898833 22819913751322674668174125)
  ·
    refine ⟨8557467656746003000565297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22819913751322674668174125 8557467656746003000565297)
    ·
      refine ⟨6418100742559502250423973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8557467656746003000565297 6418100742559502250423973)
      ·
        refine ⟨1203393889229906671954495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6418100742559502250423973 1203393889229906671954495)
        ·
          refine ⟨1805090833844860007931743, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203393889229906671954495 1805090833844860007931743)
          ·
            refine ⟨2707636250767290011897615, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1805090833844860007931743 2707636250767290011897615)
            ·
              refine ⟨4061454376150935017846423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707636250767290011897615 4061454376150935017846423)
              ·
                refine ⟨6092181564226402526769635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061454376150935017846423 6092181564226402526769635)
                ·
                  refine ⟨9138272346339603790154453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6092181564226402526769635 9138272346339603790154453)
                  ·
                    refine ⟨214178258117334463831745, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9138272346339603790154453 214178258117334463831745)
                    ·
                      rfl

theorem cell23_1251332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 4, 1, 1, 1, 1, 1, 7].length) (baseStart_1251332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251332 prefixEnd_1251332 := by exact prefixLift 1251332
  have htrace : WordTrace (prefixWord ++ tailWord_1251332) baseStart_1251332 baseEnd_1251332 := by
    simpa [prefixWord, tailWord_1251332, baseEnd_1251332] using wordTrace_append hprefix tailTrace_1251332
  have hstable : (prefixWord ++ tailWord_1251332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251332).length < 2 ^ (prefixWord ++ tailWord_1251332).sum := by decide
  have hdescent : baseEnd_1251332 < baseStart_1251332 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251334 : List Nat := [6, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2]
def baseStart_1251334 : Nat := 118140960795 + 1251334 * 2 ^ 59
def prefixEnd_1251334 : Nat := 4983230072969 + 3 ^ 40 * 1251334 * 2
def baseEnd_1251334 : Nat := 642535801313312383670227

theorem tailTrace_1251334 : CollatzResearch.WordTrace tailWord_1251334 prefixEnd_1251334 642535801313312383670227 := by
  unfold tailWord_1251334
  simp only [CollatzResearch.WordTrace]
  refine ⟨1426246889019940739935033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30426600299092069118614037 1426246889019940739935033)
  ·
    refine ⟨1069685166764955554951275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1426246889019940739935033 1069685166764955554951275)
    ·
      refine ⟨1604527750147433332426913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1069685166764955554951275 1604527750147433332426913)
      ·
        refine ⟨1203395812610574999320185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1604527750147433332426913 1203395812610574999320185)
        ·
          refine ⟨902546859457931249490139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203395812610574999320185 902546859457931249490139)
          ·
            refine ⟨1353820289186896874235209, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902546859457931249490139 1353820289186896874235209)
            ·
              refine ⟨1015365216890172655676407, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353820289186896874235209 1015365216890172655676407)
              ·
                refine ⟨1523047825335258983514611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015365216890172655676407 1523047825335258983514611)
                ·
                  refine ⟨2284571738002888475271917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523047825335258983514611 2284571738002888475271917)
                  ·
                    refine ⟨856714401751083178226969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284571738002888475271917 856714401751083178226969)
                    ·
                      refine ⟨642535801313312383670227, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856714401751083178226969 642535801313312383670227)
                      ·
                        rfl

theorem cell23_1251334_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 2, 2, 1, 2, 1, 1, 3, 2].length) (baseStart_1251334 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251334 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251334 prefixEnd_1251334 := by exact prefixLift 1251334
  have htrace : WordTrace (prefixWord ++ tailWord_1251334) baseStart_1251334 baseEnd_1251334 := by
    simpa [prefixWord, tailWord_1251334, baseEnd_1251334] using wordTrace_append hprefix tailTrace_1251334
  have hstable : (prefixWord ++ tailWord_1251334).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251334).length < 2 ^ (prefixWord ++ tailWord_1251334).sum := by decide
  have hdescent : baseEnd_1251334 < baseStart_1251334 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251334) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251335 : List Nat := [1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 4]
def baseStart_1251335 : Nat := 118140960795 + 1251335 * 2 ^ 59
def prefixEnd_1251335 : Nat := 4983230072969 + 3 ^ 40 * 1251335 * 2
def baseEnd_1251335 : Nat := 642536314793966879757721

theorem tailTrace_1251335 : CollatzResearch.WordTrace tailWord_1251335 prefixEnd_1251335 642536314793966879757721 := by
  unfold tailWord_1251335
  simp only [CollatzResearch.WordTrace]
  refine ⟨45639936921634480848707459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30426624614422987232471639 45639936921634480848707459)
  ·
    refine ⟨68459905382451721273061189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45639936921634480848707459 68459905382451721273061189)
    ·
      refine ⟨12836232259209697738698973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68459905382451721273061189 12836232259209697738698973)
      ·
        refine ⟨4813587097203636652012115, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12836232259209697738698973 4813587097203636652012115)
        ·
          refine ⟨7220380645805454978018173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4813587097203636652012115 7220380645805454978018173)
          ·
            refine ⟨2707642742177045616756815, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7220380645805454978018173 2707642742177045616756815)
            ·
              refine ⟨4061464113265568425135223, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707642742177045616756815 4061464113265568425135223)
              ·
                refine ⟨6092196169898352637702835, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061464113265568425135223 6092196169898352637702835)
                ·
                  refine ⟨9138294254847528956554253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6092196169898352637702835 9138294254847528956554253)
                  ·
                    refine ⟨3426860345567823358707845, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9138294254847528956554253 3426860345567823358707845)
                    ·
                      refine ⟨642536314793966879757721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3426860345567823358707845 642536314793966879757721)
                      ·
                        rfl

theorem cell23_1251335_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 3, 1, 1, 1, 3, 4].length) (baseStart_1251335 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251335 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251335 prefixEnd_1251335 := by exact prefixLift 1251335
  have htrace : WordTrace (prefixWord ++ tailWord_1251335) baseStart_1251335 baseEnd_1251335 := by
    simpa [prefixWord, tailWord_1251335, baseEnd_1251335] using wordTrace_append hprefix tailTrace_1251335
  have hstable : (prefixWord ++ tailWord_1251335).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251335).length < 2 ^ (prefixWord ++ tailWord_1251335).sum := by decide
  have hdescent : baseEnd_1251335 < baseStart_1251335 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251335) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251362 : List Nat := [3, 3, 1, 1, 1, 2, 4, 1, 3, 4]
def baseStart_1251362 : Nat := 118140960795 + 1251362 * 2 ^ 59
def prefixEnd_1251362 : Nat := 4983230072969 + 3 ^ 40 * 1251362 * 2
def baseEnd_1251362 : Nat := 214183392923879424706699

theorem tailTrace_1251362 : CollatzResearch.WordTrace tailWord_1251362 prefixEnd_1251362 214183392923879424706699 := by
  unfold tailWord_1251362
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410230423134166114985085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30427281128357776306626893 11410230423134166114985085)
  ·
    refine ⟨4278836408675312293119407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11410230423134166114985085 4278836408675312293119407)
    ·
      refine ⟨6418254613012968439679111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4278836408675312293119407 6418254613012968439679111)
      ·
        refine ⟨9627381919519452659518667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6418254613012968439679111 9627381919519452659518667)
        ·
          refine ⟨14441072879279178989278001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9627381919519452659518667 14441072879279178989278001)
          ·
            refine ⟨10830804659459384241958501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14441072879279178989278001 10830804659459384241958501)
            ·
              refine ⟨2030775873648634545367219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10830804659459384241958501 2030775873648634545367219)
              ·
                refine ⟨3046163810472951818050829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030775873648634545367219 3046163810472951818050829)
                ·
                  refine ⟨1142311428927356931769061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3046163810472951818050829 1142311428927356931769061)
                  ·
                    refine ⟨214183392923879424706699, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142311428927356931769061 214183392923879424706699)
                    ·
                      rfl

theorem cell23_1251362_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 4, 1, 3, 4].length) (baseStart_1251362 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251362 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251362 prefixEnd_1251362 := by exact prefixLift 1251362
  have htrace : WordTrace (prefixWord ++ tailWord_1251362) baseStart_1251362 baseEnd_1251362 := by
    simpa [prefixWord, tailWord_1251362, baseEnd_1251362] using wordTrace_append hprefix tailTrace_1251362
  have hstable : (prefixWord ++ tailWord_1251362).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251362).length < 2 ^ (prefixWord ++ tailWord_1251362).sum := by decide
  have hdescent : baseEnd_1251362 < baseStart_1251362 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251362) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251425 : List Nat := [1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 4]
def baseStart_1251425 : Nat := 118140960795 + 1251425 * 2 ^ 59
def prefixEnd_1251425 : Nat := 4983230072969 + 3 ^ 40 * 1251425 * 2
def baseEnd_1251425 : Nat := 642582528052871527632307

theorem tailTrace_1251425 : CollatzResearch.WordTrace tailWord_1251425 prefixEnd_1251425 642582528052871527632307 := by
  unfold tailWord_1251425
  simp only [CollatzResearch.WordTrace]
  refine ⟨45643219491308426219483729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30428812994205617479655819 45643219491308426219483729)
  ·
    refine ⟨34232414618481319664612797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45643219491308426219483729 34232414618481319664612797)
    ·
      refine ⟨12837155481930494874229799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34232414618481319664612797 12837155481930494874229799)
      ·
        refine ⟨19255733222895742311344699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12837155481930494874229799 19255733222895742311344699)
        ·
          refine ⟨28883599834343613467017049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19255733222895742311344699 28883599834343613467017049)
          ·
            refine ⟨21662699875757710100262787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 28883599834343613467017049 21662699875757710100262787)
            ·
              refine ⟨32494049813636565150394181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21662699875757710100262787 32494049813636565150394181)
              ·
                refine ⟨6092634340056855965698909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32494049813636565150394181 6092634340056855965698909)
                ·
                  refine ⟨2284737877521320987137091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6092634340056855965698909 2284737877521320987137091)
                  ·
                    refine ⟨3427106816281981480705637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284737877521320987137091 3427106816281981480705637)
                    ·
                      refine ⟨642582528052871527632307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3427106816281981480705637 642582528052871527632307)
                      ·
                        rfl

theorem cell23_1251425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 1, 4, 3, 1, 4].length) (baseStart_1251425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251425 prefixEnd_1251425 := by exact prefixLift 1251425
  have htrace : WordTrace (prefixWord ++ tailWord_1251425) baseStart_1251425 baseEnd_1251425 := by
    simpa [prefixWord, tailWord_1251425, baseEnd_1251425] using wordTrace_append hprefix tailTrace_1251425
  have hstable : (prefixWord ++ tailWord_1251425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251425).length < 2 ^ (prefixWord ++ tailWord_1251425).sum := by decide
  have hdescent : baseEnd_1251425 < baseStart_1251425 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251426 : List Nat := [3, 3, 2, 2, 2, 2, 2, 1, 6]
def baseStart_1251426 : Nat := 118140960795 + 1251426 * 2 ^ 59
def prefixEnd_1251426 : Nat := 4983230072969 + 3 ^ 40 * 1251426 * 2
def baseEnd_1251426 : Nat := 71398115725947335968867

theorem tailTrace_1251426 : CollatzResearch.WordTrace tailWord_1251426 prefixEnd_1251426 71398115725947335968867 := by
  unfold tailWord_1251426
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410813991076200847567533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30428837309536535593513421 11410813991076200847567533)
  ·
    refine ⟨4279055246653575317837825, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11410813991076200847567533 4279055246653575317837825)
    ·
      refine ⟨3209291434990181488378369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4279055246653575317837825 3209291434990181488378369)
      ·
        refine ⟨2406968576242636116283777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3209291434990181488378369 2406968576242636116283777)
        ·
          refine ⟨1805226432181977087212833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2406968576242636116283777 1805226432181977087212833)
          ·
            refine ⟨1353919824136482815409625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805226432181977087212833 1353919824136482815409625)
            ·
              refine ⟨1015439868102362111557219, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353919824136482815409625 1015439868102362111557219)
              ·
                refine ⟨1523159802153543167335829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015439868102362111557219 1523159802153543167335829)
                ·
                  refine ⟨71398115725947335968867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1523159802153543167335829 71398115725947335968867)
                  ·
                    rfl

theorem cell23_1251426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 2, 2, 2, 2, 1, 6].length) (baseStart_1251426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251426 prefixEnd_1251426 := by exact prefixLift 1251426
  have htrace : WordTrace (prefixWord ++ tailWord_1251426) baseStart_1251426 baseEnd_1251426 := by
    simpa [prefixWord, tailWord_1251426, baseEnd_1251426] using wordTrace_append hprefix tailTrace_1251426
  have hstable : (prefixWord ++ tailWord_1251426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251426).length < 2 ^ (prefixWord ++ tailWord_1251426).sum := by decide
  have hdescent : baseEnd_1251426 < baseStart_1251426 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251442 : List Nat := [3, 2, 1, 2, 2, 3, 1, 1, 3, 1, 4]
def baseStart_1251442 : Nat := 118140960795 + 1251442 * 2 ^ 59
def prefixEnd_1251442 : Nat := 4983230072969 + 3 ^ 40 * 1251442 * 2
def baseEnd_1251442 : Nat := 642591257223997961119729

theorem tailTrace_1251442 : CollatzResearch.WordTrace tailWord_1251442 prefixEnd_1251442 642591257223997961119729 := by
  unfold tailWord_1251442
  simp only [CollatzResearch.WordTrace]
  refine ⟨11410959883061709530713145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30429226354831225415235053 11410959883061709530713145)
  ·
    refine ⟨8558219912296282148034859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11410959883061709530713145 8558219912296282148034859)
    ·
      refine ⟨12837329868444423222052289, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558219912296282148034859 12837329868444423222052289)
      ·
        refine ⟨9627997401333317416539217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12837329868444423222052289 9627997401333317416539217)
        ·
          refine ⟨7220998050999988062404413, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9627997401333317416539217 7220998050999988062404413)
          ·
            refine ⟨2707874269124995523401655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7220998050999988062404413 2707874269124995523401655)
            ·
              refine ⟨4061811403687493285102483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2707874269124995523401655 4061811403687493285102483)
              ·
                refine ⟨6092717105531239927653725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4061811403687493285102483 6092717105531239927653725)
                ·
                  refine ⟨2284768914574214972870147, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6092717105531239927653725 2284768914574214972870147)
                  ·
                    refine ⟨3427153371861322459305221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284768914574214972870147 3427153371861322459305221)
                    ·
                      refine ⟨642591257223997961119729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3427153371861322459305221 642591257223997961119729)
                      ·
                        rfl

theorem cell23_1251442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 3, 1, 1, 3, 1, 4].length) (baseStart_1251442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251442 prefixEnd_1251442 := by exact prefixLift 1251442
  have htrace : WordTrace (prefixWord ++ tailWord_1251442) baseStart_1251442 baseEnd_1251442 := by
    simpa [prefixWord, tailWord_1251442, baseEnd_1251442] using wordTrace_append hprefix tailTrace_1251442
  have hstable : (prefixWord ++ tailWord_1251442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251442).length < 2 ^ (prefixWord ++ tailWord_1251442).sum := by decide
  have hdescent : baseEnd_1251442 < baseStart_1251442 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251446 : List Nat := [5, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2]
def baseStart_1251446 : Nat := 118140960795 + 1251446 * 2 ^ 59
def prefixEnd_1251446 : Nat := 4983230072969 + 3 ^ 40 * 1251446 * 2
def baseEnd_1251446 : Nat := 642593311146615945469711

theorem tailTrace_1251446 : CollatzResearch.WordTrace tailWord_1251446 prefixEnd_1251446 642593311146615945469711 := by
  unfold tailWord_1251446
  simp only [CollatzResearch.WordTrace]
  refine ⟨2852749089014521675374887, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30429323616154897870665461 2852749089014521675374887)
  ·
    refine ⟨4279123633521782513062331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2852749089014521675374887 4279123633521782513062331)
    ·
      refine ⟨6418685450282673769593497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4279123633521782513062331 6418685450282673769593497)
      ·
        refine ⟨4814014087712005327195123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6418685450282673769593497 4814014087712005327195123)
        ·
          refine ⟨7221021131568007990792685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814014087712005327195123 7221021131568007990792685)
          ·
            refine ⟨2707882924338002996547257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7221021131568007990792685 2707882924338002996547257)
            ·
              refine ⟨2030912193253502247410443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2707882924338002996547257 2030912193253502247410443)
              ·
                refine ⟨3046368289880253371115665, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2030912193253502247410443 3046368289880253371115665)
                ·
                  refine ⟨2284776217410190028336749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3046368289880253371115665 2284776217410190028336749)
                  ·
                    refine ⟨856791081528821260626281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2284776217410190028336749 856791081528821260626281)
                    ·
                      refine ⟨642593311146615945469711, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 856791081528821260626281 642593311146615945469711)
                      ·
                        rfl

theorem cell23_1251446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 1, 3, 2, 1, 2, 3, 2].length) (baseStart_1251446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251446 prefixEnd_1251446 := by exact prefixLift 1251446
  have htrace : WordTrace (prefixWord ++ tailWord_1251446) baseStart_1251446 baseEnd_1251446 := by
    simpa [prefixWord, tailWord_1251446, baseEnd_1251446] using wordTrace_append hprefix tailTrace_1251446
  have hstable : (prefixWord ++ tailWord_1251446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251446).length < 2 ^ (prefixWord ++ tailWord_1251446).sum := by decide
  have hdescent : baseEnd_1251446 < baseStart_1251446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251459 : List Nat := [1, 1, 1, 3, 3, 4, 3, 1, 1, 1, 4]
def baseStart_1251459 : Nat := 118140960795 + 1251459 * 2 ^ 59
def prefixEnd_1251459 : Nat := 4983230072969 + 3 ^ 40 * 1251459 * 2
def baseEnd_1251459 : Nat := 642599986395124394607151

theorem tailTrace_1251459 : CollatzResearch.WordTrace tailWord_1251459 prefixEnd_1251459 642599986395124394607151 := by
  unfold tailWord_1251459
  simp only [CollatzResearch.WordTrace]
  refine ⟨45644459573185250026221431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30429639715456833350814287 45644459573185250026221431)
  ·
    refine ⟨68466689359777875039332147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45644459573185250026221431 68466689359777875039332147)
    ·
      refine ⟨102700034039666812558998221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68466689359777875039332147 102700034039666812558998221)
      ·
        refine ⟨38512512764875054709624333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102700034039666812558998221 38512512764875054709624333)
        ·
          refine ⟨14442192286828145516109125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38512512764875054709624333 14442192286828145516109125)
          ·
            refine ⟨2707911053780277284270461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 14442192286828145516109125 2707911053780277284270461)
            ·
              refine ⟨1015466645167603981601423, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2707911053780277284270461 1015466645167603981601423)
              ·
                refine ⟨1523199967751405972402135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015466645167603981601423 1523199967751405972402135)
                ·
                  refine ⟨2284799951627108958603203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523199967751405972402135 2284799951627108958603203)
                  ·
                    refine ⟨3427199927440663437904805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2284799951627108958603203 3427199927440663437904805)
                    ·
                      refine ⟨642599986395124394607151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3427199927440663437904805 642599986395124394607151)
                      ·
                        rfl

theorem cell23_1251459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 4, 3, 1, 1, 1, 4].length) (baseStart_1251459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251459 prefixEnd_1251459 := by exact prefixLift 1251459
  have htrace : WordTrace (prefixWord ++ tailWord_1251459) baseStart_1251459 baseEnd_1251459 := by
    simpa [prefixWord, tailWord_1251459, baseEnd_1251459] using wordTrace_append hprefix tailTrace_1251459
  have hstable : (prefixWord ++ tailWord_1251459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251459).length < 2 ^ (prefixWord ++ tailWord_1251459).sum := by decide
  have hdescent : baseEnd_1251459 < baseStart_1251459 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251470 : List Nat := [4, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3]
def baseStart_1251470 : Nat := 118140960795 + 1251470 * 2 ^ 59
def prefixEnd_1251470 : Nat := 4983230072969 + 3 ^ 40 * 1251470 * 2
def baseEnd_1251470 : Nat := 642605634682323851569601

theorem tailTrace_1251470 : CollatzResearch.WordTrace tailWord_1251470 prefixEnd_1251470 642605634682323851569601 := by
  unfold tailWord_1251470
  simp only [CollatzResearch.WordTrace]
  refine ⟨5705607597018174863108983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30429907184096932603247909 5705607597018174863108983)
  ·
    refine ⟨8558411395527262294663475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5705607597018174863108983 8558411395527262294663475)
    ·
      refine ⟨12837617093290893441995213, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8558411395527262294663475 12837617093290893441995213)
      ·
        refine ⟨4814106409984085040748205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12837617093290893441995213 4814106409984085040748205)
        ·
          refine ⟨1805289903744031890280577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4814106409984085040748205 1805289903744031890280577)
          ·
            refine ⟨1353967427808023917710433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805289903744031890280577 1353967427808023917710433)
            ·
              refine ⟨1015475570856017938282825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1353967427808023917710433 1015475570856017938282825)
              ·
                refine ⟨761606678142013453712119, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1015475570856017938282825 761606678142013453712119)
                ·
                  refine ⟨1142410017213020180568179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 761606678142013453712119 1142410017213020180568179)
                  ·
                    refine ⟨1713615025819530270852269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142410017213020180568179 1713615025819530270852269)
                    ·
                      refine ⟨642605634682323851569601, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1713615025819530270852269 642605634682323851569601)
                      ·
                        rfl

theorem cell23_1251470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 2, 2, 1, 1, 3].length) (baseStart_1251470 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251470 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251470 prefixEnd_1251470 := by exact prefixLift 1251470
  have htrace : WordTrace (prefixWord ++ tailWord_1251470) baseStart_1251470 baseEnd_1251470 := by
    simpa [prefixWord, tailWord_1251470, baseEnd_1251470] using wordTrace_append hprefix tailTrace_1251470
  have hstable : (prefixWord ++ tailWord_1251470).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251470).length < 2 ^ (prefixWord ++ tailWord_1251470).sum := by decide
  have hdescent : baseEnd_1251470 < baseStart_1251470 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251475 : List Nat := [1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 3]
def baseStart_1251475 : Nat := 118140960795 + 1251475 * 2 ^ 59
def prefixEnd_1251475 : Nat := 4983230072969 + 3 ^ 40 * 1251475 * 2
def baseEnd_1251475 : Nat := 642608202085596332007077

theorem tailTrace_1251475 : CollatzResearch.WordTrace tailWord_1251475 prefixEnd_1251475 642608202085596332007077 := by
  unfold tailWord_1251475
  simp only [CollatzResearch.WordTrace]
  refine ⟨45645043141127284758803879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30430028760751523172535919 45645043141127284758803879)
  ·
    refine ⟨68467564711690927138205819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45645043141127284758803879 68467564711690927138205819)
    ·
      refine ⟨102701347067536390707308729, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68467564711690927138205819 102701347067536390707308729)
      ·
        refine ⟨77026010300652293030481547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102701347067536390707308729 77026010300652293030481547)
        ·
          refine ⟨115539015450978439545722321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77026010300652293030481547 115539015450978439545722321)
          ·
            refine ⟨86654261588233829659291741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115539015450978439545722321 86654261588233829659291741)
            ·
              refine ⟨32495348095587686122234403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86654261588233829659291741 32495348095587686122234403)
              ·
                refine ⟨48743022143381529183351605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32495348095587686122234403 48743022143381529183351605)
                ·
                  refine ⟨4569658325942018360939213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 48743022143381529183351605 4569658325942018360939213)
                  ·
                    refine ⟨1713621872228256885352205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4569658325942018360939213 1713621872228256885352205)
                    ·
                      refine ⟨642608202085596332007077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1713621872228256885352205 642608202085596332007077)
                      ·
                        rfl

theorem cell23_1251475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 1, 5, 3, 3].length) (baseStart_1251475 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251475 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251475 prefixEnd_1251475 := by exact prefixLift 1251475
  have htrace : WordTrace (prefixWord ++ tailWord_1251475) baseStart_1251475 baseEnd_1251475 := by
    simpa [prefixWord, tailWord_1251475, baseEnd_1251475] using wordTrace_append hprefix tailTrace_1251475
  have hstable : (prefixWord ++ tailWord_1251475).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251475).length < 2 ^ (prefixWord ++ tailWord_1251475).sum := by decide
  have hdescent : baseEnd_1251475 < baseStart_1251475 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251525 : List Nat := [1, 3, 1, 1, 1, 1, 5, 2, 2, 6]
def baseStart_1251525 : Nat := 118140960795 + 1251525 * 2 ^ 59
def prefixEnd_1251525 : Nat := 4983230072969 + 3 ^ 40 * 1251525 * 2
def baseEnd_1251525 : Nat := 214211292039440378793949

theorem tailTrace_1251525 : CollatzResearch.WordTrace tailWord_1251525 prefixEnd_1251525 214211292039440378793949 := by
  unfold tailWord_1251525
  simp only [CollatzResearch.WordTrace]
  refine ⟨45646866790946143298124029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30431244527297428865416019 45646866790946143298124029)
  ·
    refine ⟨17117575046604803736796511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45646866790946143298124029 17117575046604803736796511)
    ·
      refine ⟨25676362569907205605194767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17117575046604803736796511 25676362569907205605194767)
      ·
        refine ⟨38514543854860808407792151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25676362569907205605194767 38514543854860808407792151)
        ·
          refine ⟨57771815782291212611688227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38514543854860808407792151 57771815782291212611688227)
          ·
            refine ⟨86657723673436818917532341, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57771815782291212611688227 86657723673436818917532341)
            ·
              refine ⟨8124161594384701773518657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86657723673436818917532341 8124161594384701773518657)
              ·
                refine ⟨6093121195788526330138993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8124161594384701773518657 6093121195788526330138993)
                ·
                  refine ⟨4569840896841394747604245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6093121195788526330138993 4569840896841394747604245)
                  ·
                    refine ⟨214211292039440378793949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4569840896841394747604245 214211292039440378793949)
                    ·
                      rfl

theorem cell23_1251525_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 5, 2, 2, 6].length) (baseStart_1251525 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251525 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251525 prefixEnd_1251525 := by exact prefixLift 1251525
  have htrace : WordTrace (prefixWord ++ tailWord_1251525) baseStart_1251525 baseEnd_1251525 := by
    simpa [prefixWord, tailWord_1251525, baseEnd_1251525] using wordTrace_append hprefix tailTrace_1251525
  have hstable : (prefixWord ++ tailWord_1251525).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251525).length < 2 ^ (prefixWord ++ tailWord_1251525).sum := by decide
  have hdescent : baseEnd_1251525 < baseStart_1251525 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251525) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251582 : List Nat := [4, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7]
def baseStart_1251582 : Nat := 118140960795 + 1251582 * 2 ^ 59
def prefixEnd_1251582 : Nat := 4983230072969 + 3 ^ 40 * 1251582 * 2
def baseEnd_1251582 : Nat := 642663144515627413369085

theorem tailTrace_1251582 : CollatzResearch.WordTrace tailWord_1251582 prefixEnd_1251582 642663144515627413369085 := by
  unfold tailWord_1251582
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706118218967455254118625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30432630501159761355299333 5706118218967455254118625)
  ·
    refine ⟨4279588664225591440588969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5706118218967455254118625 4279588664225591440588969)
    ·
      refine ⟨3209691498169193580441727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4279588664225591440588969 3209691498169193580441727)
      ·
        refine ⟨4814537247253790370662591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3209691498169193580441727 4814537247253790370662591)
        ·
          refine ⟨7221805870880685555993887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4814537247253790370662591 7221805870880685555993887)
          ·
            refine ⟨10832708806321028333990831, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7221805870880685555993887 10832708806321028333990831)
            ·
              refine ⟨16249063209481542500986247, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10832708806321028333990831 16249063209481542500986247)
              ·
                refine ⟨24373594814222313751479371, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16249063209481542500986247 24373594814222313751479371)
                ·
                  refine ⟨36560392221333470627219057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 24373594814222313751479371 36560392221333470627219057)
                  ·
                    refine ⟨27420294166000102970414293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 36560392221333470627219057 27420294166000102970414293)
                    ·
                      refine ⟨642663144515627413369085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 27420294166000102970414293 642663144515627413369085)
                      ·
                        rfl

theorem cell23_1251582_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_1251582 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251582 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251582 prefixEnd_1251582 := by exact prefixLift 1251582
  have htrace : WordTrace (prefixWord ++ tailWord_1251582) baseStart_1251582 baseEnd_1251582 := by
    simpa [prefixWord, tailWord_1251582, baseEnd_1251582] using wordTrace_append hprefix tailTrace_1251582
  have hstable : (prefixWord ++ tailWord_1251582).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251582).length < 2 ^ (prefixWord ++ tailWord_1251582).sum := by decide
  have hdescent : baseEnd_1251582 < baseStart_1251582 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251582) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251632 : List Nat := [2, 1, 1, 1, 2, 2, 2, 1, 7, 4]
def baseStart_1251632 : Nat := 118140960795 + 1251632 * 2 ^ 59
def prefixEnd_1251632 : Nat := 4983230072969 + 3 ^ 40 * 1251632 * 2
def baseEnd_1251632 : Nat := 214229606182784072581285

theorem tailTrace_1251632 : CollatzResearch.WordTrace tailWord_1251632 prefixEnd_1251632 214229606182784072581285 := by
  unfold tailWord_1251632
  simp only [CollatzResearch.WordTrace]
  refine ⟨22825384700779250286134575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30433846267705667048179433 22825384700779250286134575)
  ·
    refine ⟨34238077051168875429201863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22825384700779250286134575 34238077051168875429201863)
    ·
      refine ⟨51357115576753313143802795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34238077051168875429201863 51357115576753313143802795)
      ·
        refine ⟨77035673365129969715704193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51357115576753313143802795 77035673365129969715704193)
        ·
          refine ⟨57776755023847477286778145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77035673365129969715704193 57776755023847477286778145)
          ·
            refine ⟨43332566267885607965083609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57776755023847477286778145 43332566267885607965083609)
            ·
              refine ⟨32499424700914205973812707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43332566267885607965083609 32499424700914205973812707)
              ·
                refine ⟨48749137051371308960719061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32499424700914205973812707 48749137051371308960719061)
                ·
                  refine ⟨1142557899641515053766853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48749137051371308960719061 1142557899641515053766853)
                  ·
                    refine ⟨214229606182784072581285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142557899641515053766853 214229606182784072581285)
                    ·
                      rfl

theorem cell23_1251632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 1, 7, 4].length) (baseStart_1251632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251632 prefixEnd_1251632 := by exact prefixLift 1251632
  have htrace : WordTrace (prefixWord ++ tailWord_1251632) baseStart_1251632 baseEnd_1251632 := by
    simpa [prefixWord, tailWord_1251632, baseEnd_1251632] using wordTrace_append hprefix tailTrace_1251632
  have hstable : (prefixWord ++ tailWord_1251632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251632).length < 2 ^ (prefixWord ++ tailWord_1251632).sum := by decide
  have hdescent : baseEnd_1251632 < baseStart_1251632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251672 : List Nat := [2, 1, 2, 2, 1, 1, 2, 1, 1, 7, 3]
def baseStart_1251672 : Nat := 118140960795 + 1251672 * 2 ^ 59
def prefixEnd_1251672 : Nat := 4983230072969 + 3 ^ 40 * 1251672 * 2
def baseEnd_1251672 : Nat := 642709357774532061243671

theorem tailTrace_1251672 : CollatzResearch.WordTrace tailWord_1251672 prefixEnd_1251672 642709357774532061243671 := by
  unfold tailWord_1251672
  simp only [CollatzResearch.WordTrace]
  refine ⟨22826114160706793701862635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30434818880942391602483513 22826114160706793701862635)
  ·
    refine ⟨34239171241060190552793953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22826114160706793701862635 34239171241060190552793953)
    ·
      refine ⟨25679378430795142914595465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34239171241060190552793953 25679378430795142914595465)
      ·
        refine ⟨19259533823096357185946599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25679378430795142914595465 19259533823096357185946599)
        ·
          refine ⟨28889300734644535778919899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19259533823096357185946599 28889300734644535778919899)
          ·
            refine ⟨43333951101966803668379849, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28889300734644535778919899 43333951101966803668379849)
            ·
              refine ⟨32500463326475102751284887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43333951101966803668379849 32500463326475102751284887)
              ·
                refine ⟨48750694989712654126927331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32500463326475102751284887 48750694989712654126927331)
                ·
                  refine ⟨73126042484568981190390997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 48750694989712654126927331 73126042484568981190390997)
                  ·
                    refine ⟨1713891620732085496649789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 73126042484568981190390997 1713891620732085496649789)
                    ·
                      refine ⟨642709357774532061243671, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1713891620732085496649789 642709357774532061243671)
                      ·
                        rfl

theorem cell23_1251672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 1, 1, 7, 3].length) (baseStart_1251672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251672 prefixEnd_1251672 := by exact prefixLift 1251672
  have htrace : WordTrace (prefixWord ++ tailWord_1251672) baseStart_1251672 baseEnd_1251672 := by
    simpa [prefixWord, tailWord_1251672, baseEnd_1251672] using wordTrace_append hprefix tailTrace_1251672
  have hstable : (prefixWord ++ tailWord_1251672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251672).length < 2 ^ (prefixWord ++ tailWord_1251672).sum := by decide
  have hdescent : baseEnd_1251672 < baseStart_1251672 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251689 : List Nat := [1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 3]
def baseStart_1251689 : Nat := 118140960795 + 1251689 * 2 ^ 59
def prefixEnd_1251689 : Nat := 4983230072969 + 3 ^ 40 * 1251689 * 2
def baseEnd_1251689 : Nat := 642718086945658494731093

theorem tailTrace_1251689 : CollatzResearch.WordTrace tailWord_1251689 prefixEnd_1251689 642718086945658494731093 := by
  unfold tailWord_1251689
  simp only [CollatzResearch.WordTrace]
  refine ⟨45652848362351999307094121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30435232241567999538062747 45652848362351999307094121)
  ·
    refine ⟨34239636271763999480320591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45652848362351999307094121 34239636271763999480320591)
    ·
      refine ⟨51359454407645999220480887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34239636271763999480320591 51359454407645999220480887)
      ·
        refine ⟨77039181611468998830721331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51359454407645999220480887 77039181611468998830721331)
        ·
          refine ⟨115558772417203498246081997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77039181611468998830721331 115558772417203498246081997)
          ·
            refine ⟨43334539656451311842280749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115558772417203498246081997 43334539656451311842280749)
            ·
              refine ⟨16250452371169241940855281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43334539656451311842280749 16250452371169241940855281)
              ·
                refine ⟨12187839278376931455641461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16250452371169241940855281 12187839278376931455641461)
                ·
                  refine ⟨1142609932347837323966387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12187839278376931455641461 1142609932347837323966387)
                  ·
                    refine ⟨1713914898521755985949581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142609932347837323966387 1713914898521755985949581)
                    ·
                      refine ⟨642718086945658494731093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1713914898521755985949581 642718086945658494731093)
                      ·
                        rfl

theorem cell23_1251689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 3, 2, 5, 1, 3].length) (baseStart_1251689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251689 prefixEnd_1251689 := by exact prefixLift 1251689
  have htrace : WordTrace (prefixWord ++ tailWord_1251689) baseStart_1251689 baseEnd_1251689 := by
    simpa [prefixWord, tailWord_1251689, baseEnd_1251689] using wordTrace_append hprefix tailTrace_1251689
  have hstable : (prefixWord ++ tailWord_1251689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251689).length < 2 ^ (prefixWord ++ tailWord_1251689).sum := by decide
  have hdescent : baseEnd_1251689 < baseStart_1251689 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251726 : List Nat := [4, 1, 1, 4, 1, 1, 1, 4, 1, 5]
def baseStart_1251726 : Nat := 118140960795 + 1251726 * 2 ^ 59
def prefixEnd_1251726 : Nat := 4983230072969 + 3 ^ 40 * 1251726 * 2
def baseEnd_1251726 : Nat := 214245695243291616656141

theorem tailTrace_1251726 : CollatzResearch.WordTrace tailWord_1251726 prefixEnd_1251726 214245695243291616656141 := by
  unfold tailWord_1251726
  simp only [CollatzResearch.WordTrace]
  refine ⟨5706774732902244328273879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30436131908811969750794021 5706774732902244328273879)
  ·
    refine ⟨8560162099353366492410819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5706774732902244328273879 8560162099353366492410819)
    ·
      refine ⟨12840243149030049738616229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8560162099353366492410819 12840243149030049738616229)
      ·
        refine ⟨2407545590443134325990543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12840243149030049738616229 2407545590443134325990543)
        ·
          refine ⟨3611318385664701488985815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2407545590443134325990543 3611318385664701488985815)
          ·
            refine ⟨5416977578497052233478723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611318385664701488985815 5416977578497052233478723)
            ·
              refine ⟨8125466367745578350218085, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5416977578497052233478723 8125466367745578350218085)
              ·
                refine ⟨1523524943952295940665891, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8125466367745578350218085 1523524943952295940665891)
                ·
                  refine ⟨2285287415928443910998837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523524943952295940665891 2285287415928443910998837)
                  ·
                    refine ⟨214245695243291616656141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2285287415928443910998837 214245695243291616656141)
                    ·
                      rfl

theorem cell23_1251726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 4, 1, 5].length) (baseStart_1251726 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251726 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251726 prefixEnd_1251726 := by exact prefixLift 1251726
  have htrace : WordTrace (prefixWord ++ tailWord_1251726) baseStart_1251726 baseEnd_1251726 := by
    simpa [prefixWord, tailWord_1251726, baseEnd_1251726] using wordTrace_append hprefix tailTrace_1251726
  have hstable : (prefixWord ++ tailWord_1251726).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251726).length < 2 ^ (prefixWord ++ tailWord_1251726).sum := by decide
  have hdescent : baseEnd_1251726 < baseStart_1251726 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251746 : List Nat := [3, 3, 1, 2, 1, 1, 1, 5, 1, 1, 4]
def baseStart_1251746 : Nat := 118140960795 + 1251746 * 2 ^ 59
def prefixEnd_1251746 : Nat := 4983230072969 + 3 ^ 40 * 1251746 * 2
def baseEnd_1251746 : Nat := 642747355342964771718331

theorem tailTrace_1251746 : CollatzResearch.WordTrace tailWord_1251746 prefixEnd_1251746 642747355342964771718331 := by
  unfold tailWord_1251746
  simp only [CollatzResearch.WordTrace]
  refine ⟨11413731830786374510479773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30436618215430332027946061 11413731830786374510479773)
  ·
    refine ⟨4280149436544890441429915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11413731830786374510479773 4280149436544890441429915)
    ·
      refine ⟨6420224154817335662144873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280149436544890441429915 6420224154817335662144873)
      ·
        refine ⟨4815168116113001746608655, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6420224154817335662144873 4815168116113001746608655)
        ·
          refine ⟨7222752174169502619912983, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4815168116113001746608655 7222752174169502619912983)
          ·
            refine ⟨10834128261254253929869475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7222752174169502619912983 10834128261254253929869475)
            ·
              refine ⟨16251192391881380894804213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10834128261254253929869475 16251192391881380894804213)
              ·
                refine ⟨1523549286738879458887895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16251192391881380894804213 1523549286738879458887895)
                ·
                  refine ⟨2285323930108319188331843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523549286738879458887895 2285323930108319188331843)
                  ·
                    refine ⟨3427985895162478782497765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2285323930108319188331843 3427985895162478782497765)
                    ·
                      refine ⟨642747355342964771718331, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3427985895162478782497765 642747355342964771718331)
                      ·
                        rfl

theorem cell23_1251746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 1, 1, 5, 1, 1, 4].length) (baseStart_1251746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251746 prefixEnd_1251746 := by exact prefixLift 1251746
  have htrace : WordTrace (prefixWord ++ tailWord_1251746) baseStart_1251746 baseEnd_1251746 := by
    simpa [prefixWord, tailWord_1251746, baseEnd_1251746] using wordTrace_append hprefix tailTrace_1251746
  have hstable : (prefixWord ++ tailWord_1251746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251746).length < 2 ^ (prefixWord ++ tailWord_1251746).sum := by decide
  have hdescent : baseEnd_1251746 < baseStart_1251746 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251749 : List Nat := [1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 5]
def baseStart_1251749 : Nat := 118140960795 + 1251749 * 2 ^ 59
def prefixEnd_1251749 : Nat := 4983230072969 + 3 ^ 40 * 1251749 * 2
def baseEnd_1251749 : Nat := 642748895784928259980817

theorem tailTrace_1251749 : CollatzResearch.WordTrace tailWord_1251749 prefixEnd_1251749 642748895784928259980817 := by
  unfold tailWord_1251749
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655036742134629554278301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30436691161423086369518867 45655036742134629554278301)
  ·
    refine ⟨17120638778300486082854363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45655036742134629554278301 17120638778300486082854363)
    ·
      refine ⟨25680958167450729124281545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17120638778300486082854363 25680958167450729124281545)
      ·
        refine ⟨19260718625588046843211159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25680958167450729124281545 19260718625588046843211159)
        ·
          refine ⟨28891077938382070264816739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19260718625588046843211159 28891077938382070264816739)
          ·
            refine ⟨43336616907573105397225109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28891077938382070264816739 43336616907573105397225109)
            ·
              refine ⟨2031403917542489315494927, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 43336616907573105397225109 2031403917542489315494927)
              ·
                refine ⟨3047105876313733973242391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031403917542489315494927 3047105876313733973242391)
                ·
                  refine ⟨4570658814470600959863587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047105876313733973242391 4570658814470600959863587)
                  ·
                    refine ⟨6855988221705901439795381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4570658814470600959863587 6855988221705901439795381)
                    ·
                      refine ⟨642748895784928259980817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6855988221705901439795381 642748895784928259980817)
                      ·
                        rfl

theorem cell23_1251749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 1, 6, 1, 1, 1, 5].length) (baseStart_1251749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251749 prefixEnd_1251749 := by exact prefixLift 1251749
  have htrace : WordTrace (prefixWord ++ tailWord_1251749) baseStart_1251749 baseEnd_1251749 := by
    simpa [prefixWord, tailWord_1251749, baseEnd_1251749] using wordTrace_append hprefix tailTrace_1251749
  have hstable : (prefixWord ++ tailWord_1251749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251749).length < 2 ^ (prefixWord ++ tailWord_1251749).sum := by decide
  have hdescent : baseEnd_1251749 < baseStart_1251749 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251757 : List Nat := [1, 5, 2, 2, 3, 1, 1, 1, 3, 1, 3]
def baseStart_1251757 : Nat := 118140960795 + 1251757 * 2 ^ 59
def prefixEnd_1251757 : Nat := 4983230072969 + 3 ^ 40 * 1251757 * 2
def baseEnd_1251757 : Nat := 642753003630164228680781

theorem tailTrace_1251757 : CollatzResearch.WordTrace tailWord_1251757 prefixEnd_1251757 642753003630164228680781 := by
  unfold tailWord_1251757
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655328526105646920569525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30436885684070431280379683 45655328526105646920569525)
  ·
    refine ⟨4280187049322404398803393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45655328526105646920569525 4280187049322404398803393)
    ·
      refine ⟨3210140286991803299102545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4280187049322404398803393 3210140286991803299102545)
      ·
        refine ⟨2407605215243852474326909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3210140286991803299102545 2407605215243852474326909)
        ·
          refine ⟨902851955716444677872591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2407605215243852474326909 902851955716444677872591)
          ·
            refine ⟨1354277933574667016808887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902851955716444677872591 1354277933574667016808887)
            ·
              refine ⟨2031416900362000525213331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354277933574667016808887 2031416900362000525213331)
              ·
                refine ⟨3047125350543000787819997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031416900362000525213331 3047125350543000787819997)
                ·
                  refine ⟨1142672006453625295432499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3047125350543000787819997 1142672006453625295432499)
                  ·
                    refine ⟨1714008009680437943148749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142672006453625295432499 1714008009680437943148749)
                    ·
                      refine ⟨642753003630164228680781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714008009680437943148749 642753003630164228680781)
                      ·
                        rfl

theorem cell23_1251757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 3, 1, 1, 1, 3, 1, 3].length) (baseStart_1251757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251757 prefixEnd_1251757 := by exact prefixLift 1251757
  have htrace : WordTrace (prefixWord ++ tailWord_1251757) baseStart_1251757 baseEnd_1251757 := by
    simpa [prefixWord, tailWord_1251757, baseEnd_1251757] using wordTrace_append hprefix tailTrace_1251757
  have hstable : (prefixWord ++ tailWord_1251757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251757).length < 2 ^ (prefixWord ++ tailWord_1251757).sum := by decide
  have hdescent : baseEnd_1251757 < baseStart_1251757 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251769 : List Nat := [1, 2, 1, 4, 3, 2, 2, 8]
def baseStart_1251769 : Nat := 118140960795 + 1251769 * 2 ^ 59
def prefixEnd_1251769 : Nat := 4983230072969 + 3 ^ 40 * 1251769 * 2
def baseEnd_1251769 : Nat := 23805895014741414138175

theorem tailTrace_1251769 : CollatzResearch.WordTrace tailWord_1251769 prefixEnd_1251769 23805895014741414138175 := by
  unfold tailWord_1251769
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655766202062172970006361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30437177468041448646670907 45655766202062172970006361)
  ·
    refine ⟨34241824651546629727504771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45655766202062172970006361 34241824651546629727504771)
    ·
      refine ⟨51362736977319944591257157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34241824651546629727504771 51362736977319944591257157)
      ·
        refine ⟨9630513183247489610860717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51362736977319944591257157 9630513183247489610860717)
        ·
          refine ⟨3611442443717808604072769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9630513183247489610860717 3611442443717808604072769)
          ·
            refine ⟨2708581832788356453054577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3611442443717808604072769 2708581832788356453054577)
            ·
              refine ⟨2031436374591267339790933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2708581832788356453054577 2031436374591267339790933)
              ·
                refine ⟨23805895014741414138175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2031436374591267339790933 23805895014741414138175)
                ·
                  rfl

theorem cell23_1251769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 2, 2, 8].length) (baseStart_1251769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251769 prefixEnd_1251769 := by exact prefixLift 1251769
  have htrace : WordTrace (prefixWord ++ tailWord_1251769) baseStart_1251769 baseEnd_1251769 := by
    simpa [prefixWord, tailWord_1251769, baseEnd_1251769] using wordTrace_append hprefix tailTrace_1251769
  have hstable : (prefixWord ++ tailWord_1251769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251769).length < 2 ^ (prefixWord ++ tailWord_1251769).sum := by decide
  have hdescent : baseEnd_1251769 < baseStart_1251769 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251773 : List Nat := [1, 4, 1, 2, 2, 2, 4, 1, 2, 4]
def baseStart_1251773 : Nat := 118140960795 + 1251773 * 2 ^ 59
def prefixEnd_1251773 : Nat := 4983230072969 + 3 ^ 40 * 1251773 * 2
def baseEnd_1251773 : Nat := 214253739773545388693569

theorem tailTrace_1251773 : CollatzResearch.WordTrace tailWord_1251773 prefixEnd_1251773 214253739773545388693569 := by
  unfold tailWord_1251773
  simp only [CollatzResearch.WordTrace]
  refine ⟨45655912094047681653151973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30437274729365121102101315 45655912094047681653151973)
  ·
    refine ⟨8560483517633940309965995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45655912094047681653151973 8560483517633940309965995)
    ·
      refine ⟨12840725276450910464948993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8560483517633940309965995 12840725276450910464948993)
      ·
        refine ⟨9630543957338182848711745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12840725276450910464948993 9630543957338182848711745)
        ·
          refine ⟨7222907968003637136533809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9630543957338182848711745 7222907968003637136533809)
          ·
            refine ⟨5417180976002727852400357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7222907968003637136533809 5417180976002727852400357)
            ·
              refine ⟨1015721433000511472325067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5417180976002727852400357 1015721433000511472325067)
              ·
                refine ⟨1523582149500767208487601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015721433000511472325067 1523582149500767208487601)
                ·
                  refine ⟨1142686612125575406365701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1523582149500767208487601 1142686612125575406365701)
                  ·
                    refine ⟨214253739773545388693569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1142686612125575406365701 214253739773545388693569)
                    ·
                      rfl

theorem cell23_1251773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 2, 4, 1, 2, 4].length) (baseStart_1251773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251773 prefixEnd_1251773 := by exact prefixLift 1251773
  have htrace : WordTrace (prefixWord ++ tailWord_1251773) baseStart_1251773 baseEnd_1251773 := by
    simpa [prefixWord, tailWord_1251773, baseEnd_1251773] using wordTrace_append hprefix tailTrace_1251773
  have hstable : (prefixWord ++ tailWord_1251773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251773).length < 2 ^ (prefixWord ++ tailWord_1251773).sum := by decide
  have hdescent : baseEnd_1251773 < baseStart_1251773 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251777 : List Nat := [1, 2, 7, 1, 1, 2, 1, 2, 1, 5]
def baseStart_1251777 : Nat := 118140960795 + 1251777 * 2 ^ 59
def prefixEnd_1251777 : Nat := 4983230072969 + 3 ^ 40 * 1251777 * 2
def baseEnd_1251777 : Nat := 214254424414418050143563

theorem tailTrace_1251777 : CollatzResearch.WordTrace tailWord_1251777 prefixEnd_1251777 214254424414418050143563 := by
  unfold tailWord_1251777
  simp only [CollatzResearch.WordTrace]
  refine ⟨45656057986033190336297585, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30437371990688793557531723 45656057986033190336297585)
  ·
    refine ⟨34242043489524892752223189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45656057986033190336297585 34242043489524892752223189)
    ·
      refine ⟨802547894285739673880231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 34242043489524892752223189 802547894285739673880231)
      ·
        refine ⟨1203821841428609510820347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 802547894285739673880231 1203821841428609510820347)
        ·
          refine ⟨1805732762142914266230521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1203821841428609510820347 1805732762142914266230521)
          ·
            refine ⟨1354299571607185699672891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805732762142914266230521 1354299571607185699672891)
            ·
              refine ⟨2031449357410778549509337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354299571607185699672891 2031449357410778549509337)
              ·
                refine ⟨1523587018058083912132003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031449357410778549509337 1523587018058083912132003)
                ·
                  refine ⟨2285380527087125868198005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523587018058083912132003 2285380527087125868198005)
                  ·
                    refine ⟨214254424414418050143563, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2285380527087125868198005 214254424414418050143563)
                    ·
                      rfl

theorem cell23_1251777_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 7, 1, 1, 2, 1, 2, 1, 5].length) (baseStart_1251777 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251777 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251777 prefixEnd_1251777 := by exact prefixLift 1251777
  have htrace : WordTrace (prefixWord ++ tailWord_1251777) baseStart_1251777 baseEnd_1251777 := by
    simpa [prefixWord, tailWord_1251777, baseEnd_1251777] using wordTrace_append hprefix tailTrace_1251777
  have hstable : (prefixWord ++ tailWord_1251777).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251777).length < 2 ^ (prefixWord ++ tailWord_1251777).sum := by decide
  have hdescent : baseEnd_1251777 < baseStart_1251777 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251777) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251779 : List Nat := [1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 3]
def baseStart_1251779 : Nat := 118140960795 + 1251779 * 2 ^ 59
def prefixEnd_1251779 : Nat := 4983230072969 + 3 ^ 40 * 1251779 * 2
def baseEnd_1251779 : Nat := 642764300204563142605679

theorem tailTrace_1251779 : CollatzResearch.WordTrace tailWord_1251779 prefixEnd_1251779 642764300204563142605679 := by
  unfold tailWord_1251779
  simp only [CollatzResearch.WordTrace]
  refine ⟨45656130932025944677870391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30437420621350629785246927 45656130932025944677870391)
  ·
    refine ⟨68484196398038917016805587, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45656130932025944677870391 68484196398038917016805587)
    ·
      refine ⟨102726294597058375525208381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68484196398038917016805587 102726294597058375525208381)
      ·
        refine ⟨38522360473896890821953143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102726294597058375525208381 38522360473896890821953143)
        ·
          refine ⟨57783540710845336232929715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38522360473896890821953143 57783540710845336232929715)
          ·
            refine ⟨86675311066268004349394573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57783540710845336232929715 86675311066268004349394573)
            ·
              refine ⟨32503241649850501631022965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 86675311066268004349394573 32503241649850501631022965)
              ·
                refine ⟨3047178904673484527908403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32503241649850501631022965 3047178904673484527908403)
                ·
                  refine ⟨4570768357010226791862605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047178904673484527908403 4570768357010226791862605)
                  ·
                    refine ⟨1714038133878835046948477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4570768357010226791862605 1714038133878835046948477)
                    ·
                      refine ⟨642764300204563142605679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714038133878835046948477 642764300204563142605679)
                      ·
                        rfl

theorem cell23_1251779_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 3, 5, 1, 3, 3].length) (baseStart_1251779 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251779 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251779 prefixEnd_1251779 := by exact prefixLift 1251779
  have htrace : WordTrace (prefixWord ++ tailWord_1251779) baseStart_1251779 baseEnd_1251779 := by
    simpa [prefixWord, tailWord_1251779, baseEnd_1251779] using wordTrace_append hprefix tailTrace_1251779
  have hstable : (prefixWord ++ tailWord_1251779).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251779).length < 2 ^ (prefixWord ++ tailWord_1251779).sum := by decide
  have hdescent : baseEnd_1251779 < baseStart_1251779 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251779) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251780 : List Nat := [2, 3, 3, 2, 2, 2, 1, 2, 1, 1, 4]
def baseStart_1251780 : Nat := 118140960795 + 1251780 * 2 ^ 59
def prefixEnd_1251780 : Nat := 4983230072969 + 3 ^ 40 * 1251780 * 2
def baseEnd_1251780 : Nat := 642764813685217638693175

theorem tailTrace_1251780 : CollatzResearch.WordTrace tailWord_1251780 prefixEnd_1251780 642764813685217638693175 := by
  unfold tailWord_1251780
  simp only [CollatzResearch.WordTrace]
  refine ⟨22828083702511160924328397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30437444936681547899104529 22828083702511160924328397)
  ·
    refine ⟨8560531388441685346623149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22828083702511160924328397 8560531388441685346623149)
    ·
      refine ⟨3210199270665632004983681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8560531388441685346623149 3210199270665632004983681)
      ·
        refine ⟨2407649452999224003737761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3210199270665632004983681 2407649452999224003737761)
        ·
          refine ⟨1805737089749418002803321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2407649452999224003737761 1805737089749418002803321)
          ·
            refine ⟨1354302817312063502102491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1805737089749418002803321 1354302817312063502102491)
            ·
              refine ⟨2031454225968095253153737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354302817312063502102491 2031454225968095253153737)
              ·
                refine ⟨1523590669476071439865303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031454225968095253153737 1523590669476071439865303)
                ·
                  refine ⟨2285386004214107159797955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523590669476071439865303 2285386004214107159797955)
                  ·
                    refine ⟨3428079006321160739696933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2285386004214107159797955 3428079006321160739696933)
                    ·
                      refine ⟨642764813685217638693175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3428079006321160739696933 642764813685217638693175)
                      ·
                        rfl

theorem cell23_1251780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 2, 2, 2, 1, 2, 1, 1, 4].length) (baseStart_1251780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251780 prefixEnd_1251780 := by exact prefixLift 1251780
  have htrace : WordTrace (prefixWord ++ tailWord_1251780) baseStart_1251780 baseEnd_1251780 := by
    simpa [prefixWord, tailWord_1251780, baseEnd_1251780] using wordTrace_append hprefix tailTrace_1251780
  have hstable : (prefixWord ++ tailWord_1251780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251780).length < 2 ^ (prefixWord ++ tailWord_1251780).sum := by decide
  have hdescent : baseEnd_1251780 < baseStart_1251780 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251783 : List Nat := [1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 3]
def baseStart_1251783 : Nat := 118140960795 + 1251783 * 2 ^ 59
def prefixEnd_1251783 : Nat := 4983230072969 + 3 ^ 40 * 1251783 * 2
def baseEnd_1251783 : Nat := 642766354127181126955661

theorem tailTrace_1251783 : CollatzResearch.WordTrace tailWord_1251783 prefixEnd_1251783 642766354127181126955661 := by
  unfold tailWord_1251783
  simp only [CollatzResearch.WordTrace]
  refine ⟨45656276824011453361016003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30437517882674302240677335 45656276824011453361016003)
  ·
    refine ⟨68484415236017180041524005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45656276824011453361016003 68484415236017180041524005)
    ·
      refine ⟨12840827856753221257785751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 68484415236017180041524005 12840827856753221257785751)
      ·
        refine ⟨19261241785129831886678627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12840827856753221257785751 19261241785129831886678627)
        ·
          refine ⟨28891862677694747830017941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19261241785129831886678627 28891862677694747830017941)
          ·
            refine ⟨1354306063016941304532091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 28891862677694747830017941 1354306063016941304532091)
            ·
              refine ⟨2031459094525411956798137, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354306063016941304532091 2031459094525411956798137)
              ·
                refine ⟨1523594320894058967598603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2031459094525411956798137 1523594320894058967598603)
                ·
                  refine ⟨2285391481341088451397905, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1523594320894058967598603 2285391481341088451397905)
                  ·
                    refine ⟨1714043611005816338548429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2285391481341088451397905 1714043611005816338548429)
                    ·
                      refine ⟨642766354127181126955661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714043611005816338548429 642766354127181126955661)
                      ·
                        rfl

theorem cell23_1251783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 6, 1, 2, 1, 2, 3].length) (baseStart_1251783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251783 prefixEnd_1251783 := by exact prefixLift 1251783
  have htrace : WordTrace (prefixWord ++ tailWord_1251783) baseStart_1251783 baseEnd_1251783 := by
    simpa [prefixWord, tailWord_1251783, baseEnd_1251783] using wordTrace_append hprefix tailTrace_1251783
  have hstable : (prefixWord ++ tailWord_1251783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251783).length < 2 ^ (prefixWord ++ tailWord_1251783).sum := by decide
  have hdescent : baseEnd_1251783 < baseStart_1251783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251796 : List Nat := [2, 4, 1, 2, 2, 1, 1, 1, 3, 3, 3]
def baseStart_1251796 : Nat := 118140960795 + 1251796 * 2 ^ 59
def prefixEnd_1251796 : Nat := 4983230072969 + 3 ^ 40 * 1251796 * 2
def baseEnd_1251796 : Nat := 642773029375689576093101

theorem tailTrace_1251796 : CollatzResearch.WordTrace tailWord_1251796 prefixEnd_1251796 642773029375689576093101 := by
  unfold tailWord_1251796
  simp only [CollatzResearch.WordTrace]
  refine ⟨22828375486482178290619621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30437833981976237720826161 22828375486482178290619621)
  ·
    refine ⟨4280320403715408429491179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22828375486482178290619621 4280320403715408429491179)
    ·
      refine ⟨6420480605573112644236769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4280320403715408429491179 6420480605573112644236769)
      ·
        refine ⟨4815360454179834483177577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6420480605573112644236769 4815360454179834483177577)
        ·
          refine ⟨3611520340634875862383183, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4815360454179834483177577 3611520340634875862383183)
          ·
            refine ⟨5417280510952313793574775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3611520340634875862383183 5417280510952313793574775)
            ·
              refine ⟨8125920766428470690362163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5417280510952313793574775 8125920766428470690362163)
              ·
                refine ⟨12188881149642706035543245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8125920766428470690362163 12188881149642706035543245)
                ·
                  refine ⟨4570830431116014763328717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 12188881149642706035543245 4570830431116014763328717)
                  ·
                    refine ⟨1714061411668505536248269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4570830431116014763328717 1714061411668505536248269)
                    ·
                      refine ⟨642773029375689576093101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714061411668505536248269 642773029375689576093101)
                      ·
                        rfl

theorem cell23_1251796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 2, 1, 1, 1, 3, 3, 3].length) (baseStart_1251796 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251796 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251796 prefixEnd_1251796 := by exact prefixLift 1251796
  have htrace : WordTrace (prefixWord ++ tailWord_1251796) baseStart_1251796 baseEnd_1251796 := by
    simpa [prefixWord, tailWord_1251796, baseEnd_1251796] using wordTrace_append hprefix tailTrace_1251796
  have hstable : (prefixWord ++ tailWord_1251796).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251796).length < 2 ^ (prefixWord ++ tailWord_1251796).sum := by decide
  have hdescent : baseEnd_1251796 < baseStart_1251796 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251839 : List Nat := [1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 3]
def baseStart_1251839 : Nat := 118140960795 + 1251839 * 2 ^ 59
def prefixEnd_1251839 : Nat := 4983230072969 + 3 ^ 40 * 1251839 * 2
def baseEnd_1251839 : Nat := 642795109043832907855403

theorem tailTrace_1251839 : CollatzResearch.WordTrace tailWord_1251839 prefixEnd_1251839 642795109043832907855403 := by
  unfold tailWord_1251839
  simp only [CollatzResearch.WordTrace]
  refine ⟨45658319311808574925054571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30438879541205716616703047 45658319311808574925054571)
  ·
    refine ⟨68487478967712862387581857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45658319311808574925054571 68487478967712862387581857)
    ·
      refine ⟨51365609225784646790686393, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68487478967712862387581857 51365609225784646790686393)
      ·
        refine ⟨38524206919338485093014795, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51365609225784646790686393 38524206919338485093014795)
        ·
          refine ⟨57786310379007727639522193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38524206919338485093014795 57786310379007727639522193)
          ·
            refine ⟨43339732784255795729641645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57786310379007727639522193 43339732784255795729641645)
            ·
              refine ⟨16252399794095923398615617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43339732784255795729641645 16252399794095923398615617)
              ·
                refine ⟨12189299845571942548961713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16252399794095923398615617 12189299845571942548961713)
                ·
                  refine ⟨9141974884178956911721285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12189299845571942548961713 9141974884178956911721285)
                  ·
                    refine ⟨1714120290783554420947741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 9141974884178956911721285 1714120290783554420947741)
                    ·
                      refine ⟨642795109043832907855403, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714120290783554420947741 642795109043832907855403)
                      ·
                        rfl

theorem cell23_1251839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 3, 2, 2, 4, 3].length) (baseStart_1251839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251839 prefixEnd_1251839 := by exact prefixLift 1251839
  have htrace : WordTrace (prefixWord ++ tailWord_1251839) baseStart_1251839 baseEnd_1251839 := by
    simpa [prefixWord, tailWord_1251839, baseEnd_1251839] using wordTrace_append hprefix tailTrace_1251839
  have hstable : (prefixWord ++ tailWord_1251839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251839).length < 2 ^ (prefixWord ++ tailWord_1251839).sum := by decide
  have hdescent : baseEnd_1251839 < baseStart_1251839 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251889 : List Nat := [1, 2, 2, 3, 1, 1, 3, 2, 1, 7]
def baseStart_1251889 : Nat := 118140960795 + 1251889 * 2 ^ 59
def prefixEnd_1251889 : Nat := 4983230072969 + 3 ^ 40 * 1251889 * 2
def baseEnd_1251889 : Nat := 214273594358852570743391

theorem tailTrace_1251889 : CollatzResearch.WordTrace tailWord_1251889 prefixEnd_1251889 214273594358852570743391 := by
  unfold tailWord_1251889
  simp only [CollatzResearch.WordTrace]
  refine ⟨45660142961627433464374721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30440095307751622309583147 45660142961627433464374721)
  ·
    refine ⟨34245107221220575098281041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45660142961627433464374721 34245107221220575098281041)
    ·
      refine ⟨25683830415915431323710781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34245107221220575098281041 25683830415915431323710781)
      ·
        refine ⟨9631436405968286746391543, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25683830415915431323710781 9631436405968286746391543)
        ·
          refine ⟨14447154608952430119587315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9631436405968286746391543 14447154608952430119587315)
          ·
            refine ⟨21670731913428645179380973, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14447154608952430119587315 21670731913428645179380973)
            ·
              refine ⟨8126524467535741942267865, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21670731913428645179380973 8126524467535741942267865)
              ·
                refine ⟨6094893350651806456700899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8126524467535741942267865 6094893350651806456700899)
                ·
                  refine ⟨9142340025977709685051349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6094893350651806456700899 9142340025977709685051349)
                  ·
                    refine ⟨214273594358852570743391, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9142340025977709685051349 214273594358852570743391)
                    ·
                      rfl

theorem cell23_1251889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 1, 3, 2, 1, 7].length) (baseStart_1251889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251889 prefixEnd_1251889 := by exact prefixLift 1251889
  have htrace : WordTrace (prefixWord ++ tailWord_1251889) baseStart_1251889 baseEnd_1251889 := by
    simpa [prefixWord, tailWord_1251889, baseEnd_1251889] using wordTrace_append hprefix tailTrace_1251889
  have hstable : (prefixWord ++ tailWord_1251889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251889).length < 2 ^ (prefixWord ++ tailWord_1251889).sum := by decide
  have hdescent : baseEnd_1251889 < baseStart_1251889 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251938 : List Nat := [3, 3, 2, 3, 2, 1, 2, 1, 2, 2, 2]
def baseStart_1251938 : Nat := 118140960795 + 1251938 * 2 ^ 59
def prefixEnd_1251938 : Nat := 4983230072969 + 3 ^ 40 * 1251938 * 2
def baseEnd_1251938 : Nat := 642845943628628020517449

theorem tailTrace_1251938 : CollatzResearch.WordTrace tailWord_1251938 prefixEnd_1251938 642845943628628020517449 := by
  unfold tailWord_1251938
  simp only [CollatzResearch.WordTrace]
  refine ⟨11415482534612478708227117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30441286758966609888605645 11415482534612478708227117)
  ·
    refine ⟨4280805950479679515585169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 11415482534612478708227117 4280805950479679515585169)
    ·
      refine ⟨3210604462859759636688877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4280805950479679515585169 3210604462859759636688877)
      ·
        refine ⟨1203976673572409863758329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3210604462859759636688877 1203976673572409863758329)
        ·
          refine ⟨902982505179307397818747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1203976673572409863758329 902982505179307397818747)
          ·
            refine ⟨1354473757768961096728121, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 902982505179307397818747 1354473757768961096728121)
            ·
              refine ⟨1015855318326720822546091, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354473757768961096728121 1015855318326720822546091)
              ·
                refine ⟨1523782977490081233819137, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1015855318326720822546091 1523782977490081233819137)
                ·
                  refine ⟨1142837233117560925364353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1523782977490081233819137 1142837233117560925364353)
                  ·
                    refine ⟨857127924838170694023265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1142837233117560925364353 857127924838170694023265)
                    ·
                      refine ⟨642845943628628020517449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857127924838170694023265 642845943628628020517449)
                      ·
                        rfl

theorem cell23_1251938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 3, 2, 1, 2, 1, 2, 2, 2].length) (baseStart_1251938 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251938 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251938 prefixEnd_1251938 := by exact prefixLift 1251938
  have htrace : WordTrace (prefixWord ++ tailWord_1251938) baseStart_1251938 baseEnd_1251938 := by
    simpa [prefixWord, tailWord_1251938, baseEnd_1251938] using wordTrace_append hprefix tailTrace_1251938
  have hstable : (prefixWord ++ tailWord_1251938).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251938).length < 2 ^ (prefixWord ++ tailWord_1251938).sum := by decide
  have hdescent : baseEnd_1251938 < baseStart_1251938 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1251993 : List Nat := [1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 3]
def baseStart_1251993 : Nat := 118140960795 + 1251993 * 2 ^ 59
def prefixEnd_1251993 : Nat := 4983230072969 + 3 ^ 40 * 1251993 * 2
def baseEnd_1251993 : Nat := 642874185064625305329695

theorem tailTrace_1251993 : CollatzResearch.WordTrace tailWord_1251993 prefixEnd_1251993 642874185064625305329695 := by
  unfold tailWord_1251993
  simp only [CollatzResearch.WordTrace]
  refine ⟨45663936153250659226160633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30442624102167106150773755 45663936153250659226160633)
  ·
    refine ⟨34247952114937994419620475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45663936153250659226160633 34247952114937994419620475)
    ·
      refine ⟨51371928172406991629430713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34247952114937994419620475 51371928172406991629430713)
      ·
        refine ⟨38528946129305243722073035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51371928172406991629430713 38528946129305243722073035)
        ·
          refine ⟨57793419193957865583109553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38528946129305243722073035 57793419193957865583109553)
          ·
            refine ⟨43345064395468399187332165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57793419193957865583109553 43345064395468399187332165)
            ·
              refine ⟨8127199574150324847624781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 43345064395468399187332165 8127199574150324847624781)
              ·
                refine ⟨3047699840306371817859293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8127199574150324847624781 3047699840306371817859293)
                ·
                  refine ⟨1142887440114889431697235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3047699840306371817859293 1142887440114889431697235)
                  ·
                    refine ⟨1714331160172334147545853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142887440114889431697235 1714331160172334147545853)
                    ·
                      refine ⟨642874185064625305329695, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714331160172334147545853 642874185064625305329695)
                      ·
                        rfl

theorem cell23_1251993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 2, 4, 3, 3, 1, 3].length) (baseStart_1251993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1251993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1251993 prefixEnd_1251993 := by exact prefixLift 1251993
  have htrace : WordTrace (prefixWord ++ tailWord_1251993) baseStart_1251993 baseEnd_1251993 := by
    simpa [prefixWord, tailWord_1251993, baseEnd_1251993] using wordTrace_append hprefix tailTrace_1251993
  have hstable : (prefixWord ++ tailWord_1251993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1251993).length < 2 ^ (prefixWord ++ tailWord_1251993).sum := by decide
  have hdescent : baseEnd_1251993 < baseStart_1251993 := by decide
  rcases family_descends (prefixWord ++ tailWord_1251993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252013 : List Nat := [1, 5, 2, 1, 1, 2, 2, 1, 3, 5]
def baseStart_1252013 : Nat := 118140960795 + 1252013 * 2 ^ 59
def prefixEnd_1252013 : Nat := 4983230072969 + 3 ^ 40 * 1252013 * 2
def baseEnd_1252013 : Nat := 214294818225905075693201

theorem tailTrace_1252013 : CollatzResearch.WordTrace tailWord_1252013 prefixEnd_1252013 214294818225905075693201 := by
  unfold tailWord_1252013
  simp only [CollatzResearch.WordTrace]
  refine ⟨45664665613178202641888693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30443110408785468427925795 45664665613178202641888693)
  ·
    refine ⟨4281062401235456497677065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 45664665613178202641888693 4281062401235456497677065)
    ·
      refine ⟨3210796800926592373257799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4281062401235456497677065 3210796800926592373257799)
      ·
        refine ⟨4816195201389888559886699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3210796800926592373257799 4816195201389888559886699)
        ·
          refine ⟨7224292802084832839830049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4816195201389888559886699 7224292802084832839830049)
          ·
            refine ⟨5418219601563624629872537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7224292802084832839830049 5418219601563624629872537)
            ·
              refine ⟨4063664701172718472404403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418219601563624629872537 4063664701172718472404403)
              ·
                refine ⟨6095497051759077708606605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4063664701172718472404403 6095497051759077708606605)
                ·
                  refine ⟨2285811394409654140727477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6095497051759077708606605 2285811394409654140727477)
                  ·
                    refine ⟨214294818225905075693201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2285811394409654140727477 214294818225905075693201)
                    ·
                      rfl

theorem cell23_1252013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 2, 2, 1, 3, 5].length) (baseStart_1252013 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252013 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252013 prefixEnd_1252013 := by exact prefixLift 1252013
  have htrace : WordTrace (prefixWord ++ tailWord_1252013) baseStart_1252013 baseEnd_1252013 := by
    simpa [prefixWord, tailWord_1252013, baseEnd_1252013] using wordTrace_append hprefix tailTrace_1252013
  have hstable : (prefixWord ++ tailWord_1252013).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252013).length < 2 ^ (prefixWord ++ tailWord_1252013).sum := by decide
  have hdescent : baseEnd_1252013 < baseStart_1252013 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252026 : List Nat := [3, 1, 1, 1, 2, 3, 1, 4, 1, 6]
def baseStart_1252026 : Nat := 118140960795 + 1252026 * 2 ^ 59
def prefixEnd_1252026 : Nat := 4983230072969 + 3 ^ 40 * 1252026 * 2
def baseEnd_1252026 : Nat := 214297043308741225405681

theorem tailTrace_1252026 : CollatzResearch.WordTrace tailWord_1252026 prefixEnd_1252026 214297043308741225405681 := by
  unfold tailWord_1252026
  simp only [CollatzResearch.WordTrace]
  refine ⟨11416284940532776465527983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30443426508087403908074621 11416284940532776465527983)
  ·
    refine ⟨17124427410799164698291975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11416284940532776465527983 17124427410799164698291975)
    ·
      refine ⟨25686641116198747047437963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17124427410799164698291975 25686641116198747047437963)
      ·
        refine ⟨38529961674298120571156945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25686641116198747047437963 38529961674298120571156945)
        ·
          refine ⟨28897471255723590428367709, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38529961674298120571156945 28897471255723590428367709)
          ·
            refine ⟨10836551720896346410637891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28897471255723590428367709 10836551720896346410637891)
            ·
              refine ⟨16254827581344519615956837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10836551720896346410637891 16254827581344519615956837)
              ·
                refine ⟨3047780171502097427991907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16254827581344519615956837 3047780171502097427991907)
                ·
                  refine ⟨4571670257253146141987861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047780171502097427991907 4571670257253146141987861)
                  ·
                    refine ⟨214297043308741225405681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4571670257253146141987861 214297043308741225405681)
                    ·
                      rfl

theorem cell23_1252026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 1, 4, 1, 6].length) (baseStart_1252026 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252026 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252026 prefixEnd_1252026 := by exact prefixLift 1252026
  have htrace : WordTrace (prefixWord ++ tailWord_1252026) baseStart_1252026 baseEnd_1252026 := by
    simpa [prefixWord, tailWord_1252026, baseEnd_1252026] using wordTrace_append hprefix tailTrace_1252026
  have hstable : (prefixWord ++ tailWord_1252026).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252026).length < 2 ^ (prefixWord ++ tailWord_1252026).sum := by decide
  have hdescent : baseEnd_1252026 < baseStart_1252026 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252060 : List Nat := [2, 2, 5, 1, 1, 1, 3, 1, 1, 6]
def baseStart_1252060 : Nat := 118140960795 + 1252060 * 2 ^ 59
def prefixEnd_1252060 : Nat := 4983230072969 + 3 ^ 40 * 1252060 * 2
def baseEnd_1252060 : Nat := 214302862756158847730629

theorem tailTrace_1252060 : CollatzResearch.WordTrace tailWord_1252060 prefixEnd_1252060 214302862756158847730629 := by
  unfold tailWord_1252060
  simp only [CollatzResearch.WordTrace]
  refine ⟨22833189922003964834424817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30444253229338619779233089 22833189922003964834424817)
  ·
    refine ⟨17124892441502973625818613, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22833189922003964834424817 17124892441502973625818613)
    ·
      refine ⟨1605458666390903777420495, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 17124892441502973625818613 1605458666390903777420495)
      ·
        refine ⟨2408187999586355666130743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1605458666390903777420495 2408187999586355666130743)
        ·
          refine ⟨3612281999379533499196115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408187999586355666130743 3612281999379533499196115)
          ·
            refine ⟨5418422999069300248794173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612281999379533499196115 5418422999069300248794173)
            ·
              refine ⟨2031908624650987593297815, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5418422999069300248794173 2031908624650987593297815)
              ·
                refine ⟨3047862936976481389946723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031908624650987593297815 3047862936976481389946723)
                ·
                  refine ⟨4571794405464722084920085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047862936976481389946723 4571794405464722084920085)
                  ·
                    refine ⟨214302862756158847730629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4571794405464722084920085 214302862756158847730629)
                    ·
                      rfl

theorem cell23_1252060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 5, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_1252060 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252060 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252060 prefixEnd_1252060 := by exact prefixLift 1252060
  have htrace : WordTrace (prefixWord ++ tailWord_1252060) baseStart_1252060 baseEnd_1252060 := by
    simpa [prefixWord, tailWord_1252060, baseEnd_1252060] using wordTrace_append hprefix tailTrace_1252060
  have hstable : (prefixWord ++ tailWord_1252060).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252060).length < 2 ^ (prefixWord ++ tailWord_1252060).sum := by decide
  have hdescent : baseEnd_1252060 < baseStart_1252060 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252063 : List Nat := [1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 4]
def baseStart_1252063 : Nat := 118140960795 + 1252063 * 2 ^ 59
def prefixEnd_1252063 : Nat := 4983230072969 + 3 ^ 40 * 1252063 * 2
def baseEnd_1252063 : Nat := 642910128710440031454373

theorem tailTrace_1252063 : CollatzResearch.WordTrace tailWord_1252063 prefixEnd_1252063 642910128710440031454373 := by
  unfold tailWord_1252063
  simp only [CollatzResearch.WordTrace]
  refine ⟨45666489262997061181208843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30444326175331374120805895 45666489262997061181208843)
  ·
    refine ⟨68499733894495591771813265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45666489262997061181208843 68499733894495591771813265)
    ·
      refine ⟨51374800420871693828859949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68499733894495591771813265 51374800420871693828859949)
      ·
        refine ⟨19265550157826885185822481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51374800420871693828859949 19265550157826885185822481)
        ·
          refine ⟨14449162618370163889366861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19265550157826885185822481 14449162618370163889366861)
          ·
            refine ⟨5418435981888811458512573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 14449162618370163889366861 5418435981888811458512573)
            ·
              refine ⟨2031913493208304296942215, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5418435981888811458512573 2031913493208304296942215)
              ·
                refine ⟨3047870239812456445413323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2031913493208304296942215 3047870239812456445413323)
                ·
                  refine ⟨4571805359718684668119985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3047870239812456445413323 4571805359718684668119985)
                  ·
                    refine ⟨3428854019789013501089989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4571805359718684668119985 3428854019789013501089989)
                    ·
                      refine ⟨642910128710440031454373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3428854019789013501089989 642910128710440031454373)
                      ·
                        rfl

theorem cell23_1252063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 3, 3, 1, 1, 2, 4].length) (baseStart_1252063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252063 prefixEnd_1252063 := by exact prefixLift 1252063
  have htrace : WordTrace (prefixWord ++ tailWord_1252063) baseStart_1252063 baseEnd_1252063 := by
    simpa [prefixWord, tailWord_1252063, baseEnd_1252063] using wordTrace_append hprefix tailTrace_1252063
  have hstable : (prefixWord ++ tailWord_1252063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252063).length < 2 ^ (prefixWord ++ tailWord_1252063).sum := by decide
  have hdescent : baseEnd_1252063 < baseStart_1252063 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252067 : List Nat := [1, 1, 1, 7, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1252067 : Nat := 118140960795 + 1252067 * 2 ^ 59
def prefixEnd_1252067 : Nat := 4983230072969 + 3 ^ 40 * 1252067 * 2
def baseEnd_1252067 : Nat := 642912182633058015804355

theorem tailTrace_1252067 : CollatzResearch.WordTrace tailWord_1252067 prefixEnd_1252067 642912182633058015804355 := by
  unfold tailWord_1252067
  simp only [CollatzResearch.WordTrace]
  refine ⟨45666635154982569864354455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30444423436655046576236303 45666635154982569864354455)
  ·
    refine ⟨68499952732473854796531683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45666635154982569864354455 68499952732473854796531683)
    ·
      refine ⟨102749929098710782194797525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68499952732473854796531683 102749929098710782194797525)
      ·
        refine ⟨2408201463251033957690567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 102749929098710782194797525 2408201463251033957690567)
        ·
          refine ⟨3612302194876550936535851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408201463251033957690567 3612302194876550936535851)
          ·
            refine ⟨5418453292314826404803777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3612302194876550936535851 5418453292314826404803777)
            ·
              refine ⟨4063839969236119803602833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5418453292314826404803777 4063839969236119803602833)
              ·
                refine ⟨3047879976927089852702125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4063839969236119803602833 3047879976927089852702125)
                ·
                  refine ⟨1142954991347658694763297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3047879976927089852702125 1142954991347658694763297)
                  ·
                    refine ⟨857216243510744021072473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1142954991347658694763297 857216243510744021072473)
                    ·
                      refine ⟨642912182633058015804355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857216243510744021072473 642912182633058015804355)
                      ·
                        rfl

theorem cell23_1252067_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1252067 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252067 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252067 prefixEnd_1252067 := by exact prefixLift 1252067
  have htrace : WordTrace (prefixWord ++ tailWord_1252067) baseStart_1252067 baseEnd_1252067 := by
    simpa [prefixWord, tailWord_1252067, baseEnd_1252067] using wordTrace_append hprefix tailTrace_1252067
  have hstable : (prefixWord ++ tailWord_1252067).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252067).length < 2 ^ (prefixWord ++ tailWord_1252067).sum := by decide
  have hdescent : baseEnd_1252067 < baseStart_1252067 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252067) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252100 : List Nat := [2, 3, 2, 2, 1, 1, 1, 3, 4, 1, 3]
def baseStart_1252100 : Nat := 118140960795 + 1252100 * 2 ^ 59
def prefixEnd_1252100 : Nat := 4983230072969 + 3 ^ 40 * 1252100 * 2
def baseEnd_1252100 : Nat := 642929127494656386691703

theorem tailTrace_1252100 : CollatzResearch.WordTrace tailWord_1252100 prefixEnd_1252100 642929127494656386691703 := by
  unfold tailWord_1252100
  simp only [CollatzResearch.WordTrace]
  refine ⟨22833919381931508250152877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30445225842575344333537169 22833919381931508250152877)
  ·
    refine ⟨8562719768224315593807329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22833919381931508250152877 8562719768224315593807329)
    ·
      refine ⟨6422039826168236695355497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8562719768224315593807329 6422039826168236695355497)
      ·
        refine ⟨4816529869626177521516623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6422039826168236695355497 4816529869626177521516623)
        ·
          refine ⟨7224794804439266282274935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4816529869626177521516623 7224794804439266282274935)
          ·
            refine ⟨10837192206658899423412403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7224794804439266282274935 10837192206658899423412403)
            ·
              refine ⟨16255788309988349135118605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10837192206658899423412403 16255788309988349135118605)
              ·
                refine ⟨6095920616245630925669477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16255788309988349135118605 6095920616245630925669477)
                ·
                  refine ⟨1142985115546055798563027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 6095920616245630925669477 1142985115546055798563027)
                  ·
                    refine ⟨1714477673319083697844541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1142985115546055798563027 1714477673319083697844541)
                    ·
                      refine ⟨642929127494656386691703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714477673319083697844541 642929127494656386691703)
                      ·
                        rfl

theorem cell23_1252100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 1, 3, 4, 1, 3].length) (baseStart_1252100 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252100 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252100 prefixEnd_1252100 := by exact prefixLift 1252100
  have htrace : WordTrace (prefixWord ++ tailWord_1252100) baseStart_1252100 baseEnd_1252100 := by
    simpa [prefixWord, tailWord_1252100, baseEnd_1252100] using wordTrace_append hprefix tailTrace_1252100
  have hstable : (prefixWord ++ tailWord_1252100).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252100).length < 2 ^ (prefixWord ++ tailWord_1252100).sum := by decide
  have hdescent : baseEnd_1252100 < baseStart_1252100 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252110 : List Nat := [4, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2]
def baseStart_1252110 : Nat := 118140960795 + 1252110 * 2 ^ 59
def prefixEnd_1252110 : Nat := 4983230072969 + 3 ^ 40 * 1252110 * 2
def baseEnd_1252110 : Nat := 642934262301201347566657

theorem tailTrace_1252110 : CollatzResearch.WordTrace tailWord_1252110 prefixEnd_1252110 642934262301201347566657 := by
  unfold tailWord_1252110
  simp only [CollatzResearch.WordTrace]
  refine ⟨5708525436728348526021223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30445468995884525472113189 5708525436728348526021223)
  ·
    refine ⟨8562788155092522789031835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5708525436728348526021223 8562788155092522789031835)
    ·
      refine ⟨12844182232638784183547753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8562788155092522789031835 12844182232638784183547753)
      ·
        refine ⟨9633136674479088137660815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12844182232638784183547753 9633136674479088137660815)
        ·
          refine ⟨14449705011718632206491223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9633136674479088137660815 14449705011718632206491223)
          ·
            refine ⟨21674557517577948309736835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14449705011718632206491223 21674557517577948309736835)
            ·
              refine ⟨32511836276366922464605253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21674557517577948309736835 32511836276366922464605253)
              ·
                refine ⟨6095969301818797962113485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 32511836276366922464605253 6095969301818797962113485)
                ·
                  refine ⟨2285988488182049235792557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6095969301818797962113485 2285988488182049235792557)
                  ·
                    refine ⟨857245683068268463422209, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2285988488182049235792557 857245683068268463422209)
                    ·
                      refine ⟨642934262301201347566657, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857245683068268463422209 642934262301201347566657)
                      ·
                        rfl

theorem cell23_1252110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 1, 4, 3, 3, 2].length) (baseStart_1252110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252110 prefixEnd_1252110 := by exact prefixLift 1252110
  have htrace : WordTrace (prefixWord ++ tailWord_1252110) baseStart_1252110 baseEnd_1252110 := by
    simpa [prefixWord, tailWord_1252110, baseEnd_1252110] using wordTrace_append hprefix tailTrace_1252110
  have hstable : (prefixWord ++ tailWord_1252110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252110).length < 2 ^ (prefixWord ++ tailWord_1252110).sum := by decide
  have hdescent : baseEnd_1252110 < baseStart_1252110 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252127 : List Nat := [1, 1, 2, 4, 2, 2, 3, 2, 1, 3, 2]
def baseStart_1252127 : Nat := 118140960795 + 1252127 * 2 ^ 59
def prefixEnd_1252127 : Nat := 4983230072969 + 3 ^ 40 * 1252127 * 2
def baseEnd_1252127 : Nat := 642942991472327781054079

theorem tailTrace_1252127 : CollatzResearch.WordTrace tailWord_1252127 prefixEnd_1252127 642942991472327781054079 := by
  unfold tailWord_1252127
  simp only [CollatzResearch.WordTrace]
  refine ⟨45668823534765200111538635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30445882356510133407692423 45668823534765200111538635)
  ·
    refine ⟨68503235302147800167307953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45668823534765200111538635 68503235302147800167307953)
    ·
      refine ⟨51377426476610850125480965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68503235302147800167307953 51377426476610850125480965)
      ·
        refine ⟨9633267464364534398527681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51377426476610850125480965 9633267464364534398527681)
        ·
          refine ⟨7224950598273400798895761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9633267464364534398527681 7224950598273400798895761)
          ·
            refine ⟨5418712948705050599171821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7224950598273400798895761 5418712948705050599171821)
            ·
              refine ⟨2032017355764393974689433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5418712948705050599171821 2032017355764393974689433)
              ·
                refine ⟨1524013016823295481017075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032017355764393974689433 1524013016823295481017075)
                ·
                  refine ⟨2286019525234943221525613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524013016823295481017075 2286019525234943221525613)
                  ·
                    refine ⟨857257321963103708072105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286019525234943221525613 857257321963103708072105)
                    ·
                      refine ⟨642942991472327781054079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857257321963103708072105 642942991472327781054079)
                      ·
                        rfl

theorem cell23_1252127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 3, 2, 1, 3, 2].length) (baseStart_1252127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252127 prefixEnd_1252127 := by exact prefixLift 1252127
  have htrace : WordTrace (prefixWord ++ tailWord_1252127) baseStart_1252127 baseEnd_1252127 := by
    simpa [prefixWord, tailWord_1252127, baseEnd_1252127] using wordTrace_append hprefix tailTrace_1252127
  have hstable : (prefixWord ++ tailWord_1252127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252127).length < 2 ^ (prefixWord ++ tailWord_1252127).sum := by decide
  have hdescent : baseEnd_1252127 < baseStart_1252127 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252140 : List Nat := [2, 2, 1, 1, 1, 4, 3, 2, 1, 4, 2]
def baseStart_1252140 : Nat := 118140960795 + 1252140 * 2 ^ 59
def prefixEnd_1252140 : Nat := 4983230072969 + 3 ^ 40 * 1252140 * 2
def baseEnd_1252140 : Nat := 642949666720836230191519

theorem tailTrace_1252140 : CollatzResearch.WordTrace tailWord_1252140 prefixEnd_1252140 642949666720836230191519 := by
  unfold tailWord_1252140
  simp only [CollatzResearch.WordTrace]
  refine ⟨22834648841859051665880937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30446198455812068887841249 22834648841859051665880937)
  ·
    refine ⟨17125986631394288749410703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22834648841859051665880937 17125986631394288749410703)
    ·
      refine ⟨25688979947091433124116055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17125986631394288749410703 25688979947091433124116055)
      ·
        refine ⟨38533469920637149686174083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25688979947091433124116055 38533469920637149686174083)
        ·
          refine ⟨57800204880955724529261125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38533469920637149686174083 57800204880955724529261125)
          ·
            refine ⟨10837538415179198349236461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 57800204880955724529261125 10837538415179198349236461)
            ·
              refine ⟨4064076905692199380963673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10837538415179198349236461 4064076905692199380963673)
              ·
                refine ⟨3048057679269149535722755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064076905692199380963673 3048057679269149535722755)
                ·
                  refine ⟨4572086518903724303584133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3048057679269149535722755 4572086518903724303584133)
                  ·
                    refine ⟨857266222294448306922025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4572086518903724303584133 857266222294448306922025)
                    ·
                      refine ⟨642949666720836230191519, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857266222294448306922025 642949666720836230191519)
                      ·
                        rfl

theorem cell23_1252140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 4, 2].length) (baseStart_1252140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252140 prefixEnd_1252140 := by exact prefixLift 1252140
  have htrace : WordTrace (prefixWord ++ tailWord_1252140) baseStart_1252140 baseEnd_1252140 := by
    simpa [prefixWord, tailWord_1252140, baseEnd_1252140] using wordTrace_append hprefix tailTrace_1252140
  have hstable : (prefixWord ++ tailWord_1252140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252140).length < 2 ^ (prefixWord ++ tailWord_1252140).sum := by decide
  have hdescent : baseEnd_1252140 < baseStart_1252140 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252180 : List Nat := [2, 4, 1, 1, 4, 1, 1, 2, 7]
def baseStart_1252180 : Nat := 118140960795 + 1252180 * 2 ^ 59
def prefixEnd_1252180 : Nat := 4983230072969 + 3 ^ 40 * 1252180 * 2
def baseEnd_1252180 : Nat := 71441133994112897076815

theorem tailTrace_1252180 : CollatzResearch.WordTrace tailWord_1252180 prefixEnd_1252180 71441133994112897076815 := by
  unfold tailWord_1252180
  simp only [CollatzResearch.WordTrace]
  refine ⟨22835378301786595081608997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30447171069048793442145329 22835378301786595081608997)
  ·
    refine ⟨4281633431584986577801687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22835378301786595081608997 4281633431584986577801687)
    ·
      refine ⟨6422450147377479866702531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4281633431584986577801687 6422450147377479866702531)
      ·
        refine ⟨9633675221066219800053797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6422450147377479866702531 9633675221066219800053797)
        ·
          refine ⟨1806314103949916212510087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 9633675221066219800053797 1806314103949916212510087)
          ·
            refine ⟨2709471155924874318765131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806314103949916212510087 2709471155924874318765131)
            ·
              refine ⟨4064206733887311478147697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2709471155924874318765131 4064206733887311478147697)
              ·
                refine ⟨3048155050415483608610773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4064206733887311478147697 3048155050415483608610773)
                ·
                  refine ⟨71441133994112897076815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3048155050415483608610773 71441133994112897076815)
                  ·
                    rfl

theorem cell23_1252180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 4, 1, 1, 2, 7].length) (baseStart_1252180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252180 prefixEnd_1252180 := by exact prefixLift 1252180
  have htrace : WordTrace (prefixWord ++ tailWord_1252180) baseStart_1252180 baseEnd_1252180 := by
    simpa [prefixWord, tailWord_1252180, baseEnd_1252180] using wordTrace_append hprefix tailTrace_1252180
  have hstable : (prefixWord ++ tailWord_1252180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252180).length < 2 ^ (prefixWord ++ tailWord_1252180).sum := by decide
  have hdescent : baseEnd_1252180 < baseStart_1252180 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252193 : List Nat := [1, 2, 3, 1, 1, 1, 2, 5, 2, 5]
def baseStart_1252193 : Nat := 118140960795 + 1252193 * 2 ^ 59
def prefixEnd_1252193 : Nat := 4983230072969 + 3 ^ 40 * 1252193 * 2
def baseEnd_1252193 : Nat := 214325627065174840942925

theorem tailTrace_1252193 : CollatzResearch.WordTrace tailWord_1252193 prefixEnd_1252193 214325627065174840942925 := by
  unfold tailWord_1252193
  simp only [CollatzResearch.WordTrace]
  refine ⟨45671230752526093383441233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30447487168350728922294155 45671230752526093383441233)
  ·
    refine ⟨34253423064394570037580925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45671230752526093383441233 34253423064394570037580925)
    ·
      refine ⟨12845033649147963764092847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34253423064394570037580925 12845033649147963764092847)
      ·
        refine ⟨19267550473721945646139271, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12845033649147963764092847 19267550473721945646139271)
        ·
          refine ⟨28901325710582918469208907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19267550473721945646139271 28901325710582918469208907)
          ·
            refine ⟨43351988565874377703813361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28901325710582918469208907 43351988565874377703813361)
            ·
              refine ⟨32513991424405783277860021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43351988565874377703813361 32513991424405783277860021)
              ·
                refine ⟨3048186696038042182299377, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 32513991424405783277860021 3048186696038042182299377)
                ·
                  refine ⟨2286140022028531636724533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3048186696038042182299377 2286140022028531636724533)
                  ·
                    refine ⟨214325627065174840942925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2286140022028531636724533 214325627065174840942925)
                    ·
                      rfl

theorem cell23_1252193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 2, 5, 2, 5].length) (baseStart_1252193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252193 prefixEnd_1252193 := by exact prefixLift 1252193
  have htrace : WordTrace (prefixWord ++ tailWord_1252193) baseStart_1252193 baseEnd_1252193 := by
    simpa [prefixWord, tailWord_1252193, baseEnd_1252193] using wordTrace_append hprefix tailTrace_1252193
  have hstable : (prefixWord ++ tailWord_1252193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252193).length < 2 ^ (prefixWord ++ tailWord_1252193).sum := by decide
  have hdescent : baseEnd_1252193 < baseStart_1252193 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252253 : List Nat := [1, 4, 2, 1, 2, 1, 1, 1, 10]
def baseStart_1252253 : Nat := 118140960795 + 1252253 * 2 ^ 59
def prefixEnd_1252253 : Nat := 4983230072969 + 3 ^ 40 * 1252253 * 2
def baseEnd_1252253 : Nat := 71445298892754920897611

theorem tailTrace_1252253 : CollatzResearch.WordTrace tailWord_1252253 prefixEnd_1252253 71445298892754920897611 := by
  unfold tailWord_1252253
  simp only [CollatzResearch.WordTrace]
  refine ⟨45673419132308723630625413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30448946088205815753750275 45673419132308723630625413)
  ·
    refine ⟨8563766087307885680742265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45673419132308723630625413 8563766087307885680742265)
    ·
      refine ⟨6422824565480914260556699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8563766087307885680742265 6422824565480914260556699)
      ·
        refine ⟨9634236848221371390835049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6422824565480914260556699 9634236848221371390835049)
        ·
          refine ⟨7225677636166028543126287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9634236848221371390835049 7225677636166028543126287)
          ·
            refine ⟨10838516454249042814689431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225677636166028543126287 10838516454249042814689431)
            ·
              refine ⟨16257774681373564222034147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10838516454249042814689431 16257774681373564222034147)
              ·
                refine ⟨24386662022060346333051221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16257774681373564222034147 24386662022060346333051221)
                ·
                  refine ⟨71445298892754920897611, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 24386662022060346333051221 71445298892754920897611)
                  ·
                    rfl

theorem cell23_1252253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 1, 1, 1, 10].length) (baseStart_1252253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252253 prefixEnd_1252253 := by exact prefixLift 1252253
  have htrace : WordTrace (prefixWord ++ tailWord_1252253) baseStart_1252253 baseEnd_1252253 := by
    simpa [prefixWord, tailWord_1252253, baseEnd_1252253] using wordTrace_append hprefix tailTrace_1252253
  have hstable : (prefixWord ++ tailWord_1252253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252253).length < 2 ^ (prefixWord ++ tailWord_1252253).sum := by decide
  have hdescent : baseEnd_1252253 < baseStart_1252253 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252300 : List Nat := [2, 2, 1, 4, 1, 1, 3, 1, 3, 5]
def baseStart_1252300 : Nat := 118140960795 + 1252300 * 2 ^ 59
def prefixEnd_1252300 : Nat := 4983230072969 + 3 ^ 40 * 1252300 * 2
def baseEnd_1252300 : Nat := 214343941208518534730261

theorem tailTrace_1252300 : CollatzResearch.WordTrace tailWord_1252300 prefixEnd_1252300 214343941208518534730261 := by
  unfold tailWord_1252300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22837566681569225328793177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30450088908758967105057569 22837566681569225328793177)
  ·
    refine ⟨17128175011176918996594883, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22837566681569225328793177 17128175011176918996594883)
    ·
      refine ⟨25692262516765378494892325, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17128175011176918996594883 25692262516765378494892325)
      ·
        refine ⟨4817299221893508467792311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25692262516765378494892325 4817299221893508467792311)
        ·
          refine ⟨7225948832840262701688467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817299221893508467792311 7225948832840262701688467)
          ·
            refine ⟨10838923249260394052532701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7225948832840262701688467 10838923249260394052532701)
            ·
              refine ⟨4064596218472647769699763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10838923249260394052532701 4064596218472647769699763)
              ·
                refine ⟨6096894327708971654549645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4064596218472647769699763 6096894327708971654549645)
                ·
                  refine ⟨2286335372890864370456117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6096894327708971654549645 2286335372890864370456117)
                  ·
                    refine ⟨214343941208518534730261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2286335372890864370456117 214343941208518534730261)
                    ·
                      rfl

theorem cell23_1252300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 1, 3, 1, 3, 5].length) (baseStart_1252300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252300 prefixEnd_1252300 := by exact prefixLift 1252300
  have htrace : WordTrace (prefixWord ++ tailWord_1252300) baseStart_1252300 baseEnd_1252300 := by
    simpa [prefixWord, tailWord_1252300, baseEnd_1252300] using wordTrace_append hprefix tailTrace_1252300
  have hstable : (prefixWord ++ tailWord_1252300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252300).length < 2 ^ (prefixWord ++ tailWord_1252300).sum := by decide
  have hdescent : baseEnd_1252300 < baseStart_1252300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252325 : List Nat := [1, 3, 1, 6, 2, 1, 2, 2, 1, 4]
def baseStart_1252325 : Nat := 118140960795 + 1252325 * 2 ^ 59
def prefixEnd_1252325 : Nat := 4983230072969 + 3 ^ 40 * 1252325 * 2
def baseEnd_1252325 : Nat := 214348220213972668792723

theorem tailTrace_1252325 : CollatzResearch.WordTrace tailWord_1252325 prefixEnd_1252325 214348220213972668792723 := by
  unfold tailWord_1252325
  simp only [CollatzResearch.WordTrace]
  refine ⟨45676045188047879927246429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30450696792031919951497619 45676045188047879927246429)
  ·
    refine ⟨17128516945517954972717411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45676045188047879927246429 17128516945517954972717411)
    ·
      refine ⟨25692775418276932459076117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17128516945517954972717411 25692775418276932459076117)
      ·
        refine ⟨1204348847731731209019193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25692775418276932459076117 1204348847731731209019193)
        ·
          refine ⟨903261635798798406764395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1204348847731731209019193 903261635798798406764395)
          ·
            refine ⟨1354892453698197610146593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903261635798798406764395 1354892453698197610146593)
            ·
              refine ⟨1016169340273648207609945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1354892453698197610146593 1016169340273648207609945)
              ·
                refine ⟨762127005205236155707459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016169340273648207609945 762127005205236155707459)
                ·
                  refine ⟨1143190507807854233561189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762127005205236155707459 1143190507807854233561189)
                  ·
                    refine ⟨214348220213972668792723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1143190507807854233561189 214348220213972668792723)
                    ·
                      rfl

theorem cell23_1252325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 6, 2, 1, 2, 2, 1, 4].length) (baseStart_1252325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252325 prefixEnd_1252325 := by exact prefixLift 1252325
  have htrace : WordTrace (prefixWord ++ tailWord_1252325) baseStart_1252325 baseEnd_1252325 := by
    simpa [prefixWord, tailWord_1252325, baseEnd_1252325] using wordTrace_append hprefix tailTrace_1252325
  have hstable : (prefixWord ++ tailWord_1252325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252325).length < 2 ^ (prefixWord ++ tailWord_1252325).sum := by decide
  have hdescent : baseEnd_1252325 < baseStart_1252325 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252357 : List Nat := [1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 3]
def baseStart_1252357 : Nat := 118140960795 + 1252357 * 2 ^ 59
def prefixEnd_1252357 : Nat := 4983230072969 + 3 ^ 40 * 1252357 * 2
def baseEnd_1252357 : Nat := 643061092022861881178021

theorem tailTrace_1252357 : CollatzResearch.WordTrace tailWord_1252357 prefixEnd_1252357 643061092022861881178021 := by
  unfold tailWord_1252357
  simp only [CollatzResearch.WordTrace]
  refine ⟨45677212323931949392411325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30451474882621299594940883 45677212323931949392411325)
  ·
    refine ⟨17128954621474481022154247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45677212323931949392411325 17128954621474481022154247)
    ·
      refine ⟨25693431932211721533231371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17128954621474481022154247 25693431932211721533231371)
      ·
        refine ⟨38540147898317582299847057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25693431932211721533231371 38540147898317582299847057)
        ·
          refine ⟨28905110923738186724885293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38540147898317582299847057 28905110923738186724885293)
          ·
            refine ⟨10839416596401820021831985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 28905110923738186724885293 10839416596401820021831985)
            ·
              refine ⟨8129562447301365016373989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10839416596401820021831985 8129562447301365016373989)
              ·
                refine ⟨1524292958869005940570123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8129562447301365016373989 1524292958869005940570123)
                ·
                  refine ⟨2286439438303508910855185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524292958869005940570123 2286439438303508910855185)
                  ·
                    refine ⟨1714829578727631683141389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2286439438303508910855185 1714829578727631683141389)
                    ·
                      refine ⟨643061092022861881178021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1714829578727631683141389 643061092022861881178021)
                      ·
                        rfl

theorem cell23_1252357_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 3, 2, 4, 1, 2, 3].length) (baseStart_1252357 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252357 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252357 prefixEnd_1252357 := by exact prefixLift 1252357
  have htrace : WordTrace (prefixWord ++ tailWord_1252357) baseStart_1252357 baseEnd_1252357 := by
    simpa [prefixWord, tailWord_1252357, baseEnd_1252357] using wordTrace_append hprefix tailTrace_1252357
  have hstable : (prefixWord ++ tailWord_1252357).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252357).length < 2 ^ (prefixWord ++ tailWord_1252357).sum := by decide
  have hdescent : baseEnd_1252357 < baseStart_1252357 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252357) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252381 : List Nat := [1, 4, 2, 2, 3, 2, 1, 2, 2, 4]
def baseStart_1252381 : Nat := 118140960795 + 1252381 * 2 ^ 59
def prefixEnd_1252381 : Nat := 4983230072969 + 3 ^ 40 * 1252381 * 2
def baseEnd_1252381 : Nat := 214357805186189929092637

theorem tailTrace_1252381 : CollatzResearch.WordTrace tailWord_1252381 prefixEnd_1252381 214357805186189929092637 := by
  unfold tailWord_1252381
  simp only [CollatzResearch.WordTrace]
  refine ⟨45678087675845001491284997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30452058450563334327523331 45678087675845001491284997)
  ·
    refine ⟨8564641439220937779615937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45678087675845001491284997 8564641439220937779615937)
    ·
      refine ⟨6423481079415703334711953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8564641439220937779615937 6423481079415703334711953)
      ·
        refine ⟨4817610809561777501033965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6423481079415703334711953 4817610809561777501033965)
        ·
          refine ⟨1806604053585666562887737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4817610809561777501033965 1806604053585666562887737)
          ·
            refine ⟨1354953040189249922165803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1806604053585666562887737 1354953040189249922165803)
            ·
              refine ⟨2032429560283874883248705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354953040189249922165803 2032429560283874883248705)
              ·
                refine ⟨1524322170212906162436529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2032429560283874883248705 1524322170212906162436529)
                ·
                  refine ⟨1143241627659679621827397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1524322170212906162436529 1143241627659679621827397)
                  ·
                    refine ⟨214357805186189929092637, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1143241627659679621827397 214357805186189929092637)
                    ·
                      rfl

theorem cell23_1252381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 3, 2, 1, 2, 2, 4].length) (baseStart_1252381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252381 prefixEnd_1252381 := by exact prefixLift 1252381
  have htrace : WordTrace (prefixWord ++ tailWord_1252381) baseStart_1252381 baseEnd_1252381 := by
    simpa [prefixWord, tailWord_1252381, baseEnd_1252381] using wordTrace_append hprefix tailTrace_1252381
  have hstable : (prefixWord ++ tailWord_1252381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252381).length < 2 ^ (prefixWord ++ tailWord_1252381).sum := by decide
  have hdescent : baseEnd_1252381 < baseStart_1252381 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252388 : List Nat := [2, 3, 1, 4, 1, 1, 2, 4, 1, 2, 2]
def baseStart_1252388 : Nat := 118140960795 + 1252388 * 2 ^ 59
def prefixEnd_1252388 : Nat := 4983230072969 + 3 ^ 40 * 1252388 * 2
def baseEnd_1252388 : Nat := 643077009923151259890379

theorem tailTrace_1252388 : CollatzResearch.WordTrace tailWord_1252388 prefixEnd_1252388 643077009923151259890379 := by
  unfold tailWord_1252388
  simp only [CollatzResearch.WordTrace]
  refine ⟨22839171493409820843394909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30452228657879761124526545 22839171493409820843394909)
  ·
    refine ⟨8564689310028682816273091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22839171493409820843394909 8564689310028682816273091)
    ·
      refine ⟨12847033965043024224409637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8564689310028682816273091 12847033965043024224409637)
      ·
        refine ⟨2408818868445567042076807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 12847033965043024224409637 2408818868445567042076807)
        ·
          refine ⟨3613228302668350563115211, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2408818868445567042076807 3613228302668350563115211)
          ·
            refine ⟨5419842454002525844672817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613228302668350563115211 5419842454002525844672817)
            ·
              refine ⟨4064881840501894383504613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5419842454002525844672817 4064881840501894383504613)
              ·
                refine ⟨762165345094105196907115, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4064881840501894383504613 762165345094105196907115)
                ·
                  refine ⟨1143248017641157795360673, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762165345094105196907115 1143248017641157795360673)
                  ·
                    refine ⟨857436013230868346520505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1143248017641157795360673 857436013230868346520505)
                    ·
                      refine ⟨643077009923151259890379, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857436013230868346520505 643077009923151259890379)
                      ·
                        rfl

theorem cell23_1252388_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 1, 1, 2, 4, 1, 2, 2].length) (baseStart_1252388 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252388 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252388 prefixEnd_1252388 := by exact prefixLift 1252388
  have htrace : WordTrace (prefixWord ++ tailWord_1252388) baseStart_1252388 baseEnd_1252388 := by
    simpa [prefixWord, tailWord_1252388, baseEnd_1252388] using wordTrace_append hprefix tailTrace_1252388
  have hstable : (prefixWord ++ tailWord_1252388).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252388).length < 2 ^ (prefixWord ++ tailWord_1252388).sum := by decide
  have hdescent : baseEnd_1252388 < baseStart_1252388 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252388) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252410 : List Nat := [3, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4]
def baseStart_1252410 : Nat := 118140960795 + 1252410 * 2 ^ 59
def prefixEnd_1252410 : Nat := 4983230072969 + 3 ^ 40 * 1252410 * 2
def baseEnd_1252410 : Nat := 643088306497550173815277

theorem tailTrace_1252410 : CollatzResearch.WordTrace tailWord_1252410 prefixEnd_1252410 643088306497550173815277 := by
  unfold tailWord_1252410
  simp only [CollatzResearch.WordTrace]
  refine ⟨11419786348184984861022671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30452763595159959629393789 11419786348184984861022671)
  ·
    refine ⟨17129679522277477291534007, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11419786348184984861022671 17129679522277477291534007)
    ·
      refine ⟨25694519283416215937301011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17129679522277477291534007 25694519283416215937301011)
      ·
        refine ⟨38541778925124323905951517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25694519283416215937301011 38541778925124323905951517)
        ·
          refine ⟨14453167096921621464731819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38541778925124323905951517 14453167096921621464731819)
          ·
            refine ⟨21679750645382432197097729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14453167096921621464731819 21679750645382432197097729)
            ·
              refine ⟨16259812984036824147823297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21679750645382432197097729 16259812984036824147823297)
              ·
                refine ⟨12194859738027618110867473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16259812984036824147823297 12194859738027618110867473)
                ·
                  refine ⟨9146144803520713583150605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12194859738027618110867473 9146144803520713583150605)
                  ·
                    refine ⟨3429804301320267593681477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9146144803520713583150605 3429804301320267593681477)
                    ·
                      refine ⟨643088306497550173815277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3429804301320267593681477 643088306497550173815277)
                      ·
                        rfl

theorem cell23_1252410_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 2, 2, 2, 3, 4].length) (baseStart_1252410 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252410 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252410 prefixEnd_1252410 := by exact prefixLift 1252410
  have htrace : WordTrace (prefixWord ++ tailWord_1252410) baseStart_1252410 baseEnd_1252410 := by
    simpa [prefixWord, tailWord_1252410, baseEnd_1252410] using wordTrace_append hprefix tailTrace_1252410
  have hstable : (prefixWord ++ tailWord_1252410).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252410).length < 2 ^ (prefixWord ++ tailWord_1252410).sum := by decide
  have hdescent : baseEnd_1252410 < baseStart_1252410 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252410) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252422 : List Nat := [6, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2]
def baseStart_1252422 : Nat := 118140960795 + 1252422 * 2 ^ 59
def prefixEnd_1252422 : Nat := 4983230072969 + 3 ^ 40 * 1252422 * 2
def baseEnd_1252422 : Nat := 643094468265404126865223

theorem tailTrace_1252422 : CollatzResearch.WordTrace tailWord_1252422 prefixEnd_1252422 643094468265404126865223 := by
  unfold tailWord_1252422
  simp only [CollatzResearch.WordTrace]
  refine ⟨1427486970896764546672735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30453055379130976995685013 1427486970896764546672735)
  ·
    refine ⟨2141230456345146820009103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1427486970896764546672735 2141230456345146820009103)
    ·
      refine ⟨3211845684517720230013655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2141230456345146820009103 3211845684517720230013655)
      ·
        refine ⟨4817768526776580345020483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3211845684517720230013655 4817768526776580345020483)
        ·
          refine ⟨7226652790164870517530725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4817768526776580345020483 7226652790164870517530725)
          ·
            refine ⟨1354997398155913222037011, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7226652790164870517530725 1354997398155913222037011)
            ·
              refine ⟨2032496097233869833055517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1354997398155913222037011 2032496097233869833055517)
              ·
                refine ⟨762186036462701187395819, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2032496097233869833055517 762186036462701187395819)
                ·
                  refine ⟨1143279054694051781093729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762186036462701187395819 1143279054694051781093729)
                  ·
                    refine ⟨857459291020538835820297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1143279054694051781093729 857459291020538835820297)
                    ·
                      refine ⟨643094468265404126865223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857459291020538835820297 643094468265404126865223)
                      ·
                        rfl

theorem cell23_1252422_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 4, 1, 3, 1, 2, 2].length) (baseStart_1252422 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252422 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252422 prefixEnd_1252422 := by exact prefixLift 1252422
  have htrace : WordTrace (prefixWord ++ tailWord_1252422) baseStart_1252422 baseEnd_1252422 := by
    simpa [prefixWord, tailWord_1252422, baseEnd_1252422] using wordTrace_append hprefix tailTrace_1252422
  have hstable : (prefixWord ++ tailWord_1252422).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252422).length < 2 ^ (prefixWord ++ tailWord_1252422).sum := by decide
  have hdescent : baseEnd_1252422 < baseStart_1252422 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252422) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252480 : List Nat := [2, 1, 1, 2, 1, 3, 2, 3, 1, 7]
def baseStart_1252480 : Nat := 118140960795 + 1252480 * 2 ^ 59
def prefixEnd_1252480 : Nat := 4983230072969 + 3 ^ 40 * 1252480 * 2
def baseEnd_1252480 : Nat := 214374750047788299979985

theorem tailTrace_1252480 : CollatzResearch.WordTrace tailWord_1252480 prefixEnd_1252480 214374750047788299979985 := by
  unfold tailWord_1252480
  simp only [CollatzResearch.WordTrace]
  refine ⟨22840849251243170699569447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30454465668324227599425929 22840849251243170699569447)
  ·
    refine ⟨34261273876864756049354171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22840849251243170699569447 34261273876864756049354171)
    ·
      refine ⟨51391910815297134074031257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34261273876864756049354171 51391910815297134074031257)
      ·
        refine ⟨38543933111472850555523443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51391910815297134074031257 38543933111472850555523443)
        ·
          refine ⟨57815899667209275833285165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38543933111472850555523443 57815899667209275833285165)
          ·
            refine ⟨21680962375203478437481937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57815899667209275833285165 21680962375203478437481937)
            ·
              refine ⟨16260721781402608828111453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21680962375203478437481937 16260721781402608828111453)
              ·
                refine ⟨6097770668025978310541795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16260721781402608828111453 6097770668025978310541795)
                ·
                  refine ⟨9146656002038967465812693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 6097770668025978310541795 9146656002038967465812693)
                  ·
                    refine ⟨214374750047788299979985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 9146656002038967465812693 214374750047788299979985)
                    ·
                      rfl

theorem cell23_1252480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 2, 3, 1, 7].length) (baseStart_1252480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252480 prefixEnd_1252480 := by exact prefixLift 1252480
  have htrace : WordTrace (prefixWord ++ tailWord_1252480) baseStart_1252480 baseEnd_1252480 := by
    simpa [prefixWord, tailWord_1252480, baseEnd_1252480] using wordTrace_append hprefix tailTrace_1252480
  have hstable : (prefixWord ++ tailWord_1252480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252480).length < 2 ^ (prefixWord ++ tailWord_1252480).sum := by decide
  have hdescent : baseEnd_1252480 < baseStart_1252480 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252504 : List Nat := [2, 1, 2, 4, 2, 1, 1, 1, 2, 5, 2]
def baseStart_1252504 : Nat := 118140960795 + 1252504 * 2 ^ 59
def prefixEnd_1252504 : Nat := 4983230072969 + 3 ^ 40 * 1252504 * 2
def baseEnd_1252504 : Nat := 643136573679072806039845

theorem tailTrace_1252504 : CollatzResearch.WordTrace tailWord_1252504 prefixEnd_1252504 643136573679072806039845 := by
  unfold tailWord_1252504
  simp only [CollatzResearch.WordTrace]
  refine ⟨22841286927199696749006283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30455049236266262332008377 22841286927199696749006283)
  ·
    refine ⟨34261930390799545123509425, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22841286927199696749006283 34261930390799545123509425)
    ·
      refine ⟨25696447793099658842632069, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34261930390799545123509425 25696447793099658842632069)
      ·
        refine ⟨4818083961206186032993513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25696447793099658842632069 4818083961206186032993513)
        ·
          refine ⟨3613562970904639524745135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4818083961206186032993513 3613562970904639524745135)
          ·
            refine ⟨5420344456356959287117703, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3613562970904639524745135 5420344456356959287117703)
            ·
              refine ⟨8130516684535438930676555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5420344456356959287117703 8130516684535438930676555)
              ·
                refine ⟨12195775026803158396014833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130516684535438930676555 12195775026803158396014833)
                ·
                  refine ⟨9146831270102368797011125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12195775026803158396014833 9146831270102368797011125)
                  ·
                    refine ⟨857515431572097074719793, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9146831270102368797011125 857515431572097074719793)
                    ·
                      refine ⟨643136573679072806039845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857515431572097074719793 643136573679072806039845)
                      ·
                        rfl

theorem cell23_1252504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 1, 1, 1, 2, 5, 2].length) (baseStart_1252504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252504 prefixEnd_1252504 := by exact prefixLift 1252504
  have htrace : WordTrace (prefixWord ++ tailWord_1252504) baseStart_1252504 baseEnd_1252504 := by
    simpa [prefixWord, tailWord_1252504, baseEnd_1252504] using wordTrace_append hprefix tailTrace_1252504
  have hstable : (prefixWord ++ tailWord_1252504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252504).length < 2 ^ (prefixWord ++ tailWord_1252504).sum := by decide
  have hdescent : baseEnd_1252504 < baseStart_1252504 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252527 : List Nat := [1, 1, 2, 1, 2, 3, 3, 1, 5, 4]
def baseStart_1252527 : Nat := 118140960795 + 1252527 * 2 ^ 59
def prefixEnd_1252527 : Nat := 4983230072969 + 3 ^ 40 * 1252527 * 2
def baseEnd_1252527 : Nat := 214382794578042072017413

theorem tailTrace_1252527 : CollatzResearch.WordTrace tailWord_1252527 prefixEnd_1252527 214382794578042072017413 := by
  unfold tailWord_1252527
  simp only [CollatzResearch.WordTrace]
  refine ⟨45683412733316068426099835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30455608488877378950733223 45683412733316068426099835)
  ·
    refine ⟨68525119099974102639149753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45683412733316068426099835 68525119099974102639149753)
    ·
      refine ⟨51393839324980576979362315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68525119099974102639149753 51393839324980576979362315)
      ·
        refine ⟨77090758987470865469043473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51393839324980576979362315 77090758987470865469043473)
        ·
          refine ⟨57818069240603149101782605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77090758987470865469043473 57818069240603149101782605)
          ·
            refine ⟨21681775965226180913168477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57818069240603149101782605 21681775965226180913168477)
            ·
              refine ⟨8130665986959817842438179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21681775965226180913168477 8130665986959817842438179)
              ·
                refine ⟨12195998980439726763657269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8130665986959817842438179 12195998980439726763657269)
                ·
                  refine ⟨1143374904416224384092869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12195998980439726763657269 1143374904416224384092869)
                  ·
                    refine ⟨214382794578042072017413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1143374904416224384092869 214382794578042072017413)
                    ·
                      rfl

theorem cell23_1252527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 3, 1, 5, 4].length) (baseStart_1252527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252527 prefixEnd_1252527 := by exact prefixLift 1252527
  have htrace : WordTrace (prefixWord ++ tailWord_1252527) baseStart_1252527 baseEnd_1252527 := by
    simpa [prefixWord, tailWord_1252527, baseEnd_1252527] using wordTrace_append hprefix tailTrace_1252527
  have hstable : (prefixWord ++ tailWord_1252527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252527).length < 2 ^ (prefixWord ++ tailWord_1252527).sum := by decide
  have hdescent : baseEnd_1252527 < baseStart_1252527 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252611 : List Nat := [1, 1, 1, 3, 2, 5, 1, 2, 2, 3, 2]
def baseStart_1252611 : Nat := 118140960795 + 1252611 * 2 ^ 59
def prefixEnd_1252611 : Nat := 4983230072969 + 3 ^ 40 * 1252611 * 2
def baseEnd_1252611 : Nat := 643191516109103887401853

theorem tailTrace_1252611 : CollatzResearch.WordTrace tailWord_1252611 prefixEnd_1252611 643191516109103887401853 := by
  unfold tailWord_1252611
  simp only [CollatzResearch.WordTrace]
  refine ⟨45686476465011750772157687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30457650976674500514771791 45686476465011750772157687)
  ·
    refine ⟨68529714697517626158236531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45686476465011750772157687 68529714697517626158236531)
    ·
      refine ⟨102794572046276439237354797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68529714697517626158236531 102794572046276439237354797)
      ·
        refine ⟨38547964517353664714008049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 102794572046276439237354797 38547964517353664714008049)
        ·
          refine ⟨28910973388015248535506037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38547964517353664714008049 28910973388015248535506037)
          ·
            refine ⟨2710403755126429550203691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 28910973388015248535506037 2710403755126429550203691)
            ·
              refine ⟨4065605632689644325305537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710403755126429550203691 4065605632689644325305537)
              ·
                refine ⟨3049204224517233243979153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4065605632689644325305537 3049204224517233243979153)
                ·
                  refine ⟨2286903168387924932984365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3049204224517233243979153 2286903168387924932984365)
                  ·
                    refine ⟨857588688145471849869137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2286903168387924932984365 857588688145471849869137)
                    ·
                      refine ⟨643191516109103887401853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857588688145471849869137 643191516109103887401853)
                      ·
                        rfl

theorem cell23_1252611_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 5, 1, 2, 2, 3, 2].length) (baseStart_1252611 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252611 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252611 prefixEnd_1252611 := by exact prefixLift 1252611
  have htrace : WordTrace (prefixWord ++ tailWord_1252611) baseStart_1252611 baseEnd_1252611 := by
    simpa [prefixWord, tailWord_1252611, baseEnd_1252611] using wordTrace_append hprefix tailTrace_1252611
  have hstable : (prefixWord ++ tailWord_1252611).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252611).length < 2 ^ (prefixWord ++ tailWord_1252611).sum := by decide
  have hdescent : baseEnd_1252611 < baseStart_1252611 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252611) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252627 : List Nat := [1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 3]
def baseStart_1252627 : Nat := 118140960795 + 1252627 * 2 ^ 59
def prefixEnd_1252627 : Nat := 4983230072969 + 3 ^ 40 * 1252627 * 2
def baseEnd_1252627 : Nat := 643199731799575824801779

theorem tailTrace_1252627 : CollatzResearch.WordTrace tailWord_1252627 prefixEnd_1252627 643199731799575824801779 := by
  unfold tailWord_1252627
  simp only [CollatzResearch.WordTrace]
  refine ⟨45687060032953785504740135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30458040021969190336493423 45687060032953785504740135)
  ·
    refine ⟨68530590049430678257110203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45687060032953785504740135 68530590049430678257110203)
    ·
      refine ⟨102795885074146017385665305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68530590049430678257110203 102795885074146017385665305)
      ·
        refine ⟨77096913805609513039248979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102795885074146017385665305 77096913805609513039248979)
        ·
          refine ⟨115645370708414269558873469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77096913805609513039248979 115645370708414269558873469)
          ·
            refine ⟨43367014015655351084577551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115645370708414269558873469 43367014015655351084577551)
            ·
              refine ⟨65050521023483026626866327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43367014015655351084577551 65050521023483026626866327)
              ·
                refine ⟨97575781535224539940299491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 65050521023483026626866327 97575781535224539940299491)
                ·
                  refine ⟨146363672302836809910449237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 97575781535224539940299491 146363672302836809910449237)
                  ·
                    refine ⟨1715199284798868866138077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 146363672302836809910449237 1715199284798868866138077)
                    ·
                      refine ⟨643199731799575824801779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1715199284798868866138077 643199731799575824801779)
                      ·
                        rfl

theorem cell23_1252627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 1, 1, 8, 3].length) (baseStart_1252627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252627 prefixEnd_1252627 := by exact prefixLift 1252627
  have htrace : WordTrace (prefixWord ++ tailWord_1252627) baseStart_1252627 baseEnd_1252627 := by
    simpa [prefixWord, tailWord_1252627, baseEnd_1252627] using wordTrace_append hprefix tailTrace_1252627
  have hstable : (prefixWord ++ tailWord_1252627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252627).length < 2 ^ (prefixWord ++ tailWord_1252627).sum := by decide
  have hdescent : baseEnd_1252627 < baseStart_1252627 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252638 : List Nat := [4, 3, 2, 1, 2, 1, 1, 1, 3, 5]
def baseStart_1252638 : Nat := 118140960795 + 1252638 * 2 ^ 59
def prefixEnd_1252638 : Nat := 4983230072969 + 3 ^ 40 * 1252638 * 2
def baseEnd_1252638 : Nat := 214401793362258427254743

theorem tailTrace_1252638 : CollatzResearch.WordTrace tailWord_1252638 prefixEnd_1252638 214401793362258427254743 := by
  unfold tailWord_1252638
  simp only [CollatzResearch.WordTrace]
  refine ⟨5710932654489241797923821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30458307490609289588927045 5710932654489241797923821)
  ·
    refine ⟨2141599745433465674221433, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5710932654489241797923821 2141599745433465674221433)
    ·
      refine ⟨1606199809075099255666075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2141599745433465674221433 1606199809075099255666075)
      ·
        refine ⟨2409299713612648883499113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606199809075099255666075 2409299713612648883499113)
        ·
          refine ⟨1806974785209486662624335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2409299713612648883499113 1806974785209486662624335)
          ·
            refine ⟨2710462177814229993936503, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1806974785209486662624335 2710462177814229993936503)
            ·
              refine ⟨4065693266721344990904755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2710462177814229993936503 4065693266721344990904755)
              ·
                refine ⟨6098539900082017486357133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4065693266721344990904755 6098539900082017486357133)
                ·
                  refine ⟨2286952462530756557383925, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6098539900082017486357133 2286952462530756557383925)
                  ·
                    refine ⟨214401793362258427254743, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2286952462530756557383925 214401793362258427254743)
                    ·
                      rfl

theorem cell23_1252638_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 2, 1, 1, 1, 3, 5].length) (baseStart_1252638 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252638 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252638 prefixEnd_1252638 := by exact prefixLift 1252638
  have htrace : WordTrace (prefixWord ++ tailWord_1252638) baseStart_1252638 baseEnd_1252638 := by
    simpa [prefixWord, tailWord_1252638, baseEnd_1252638] using wordTrace_append hprefix tailTrace_1252638
  have hstable : (prefixWord ++ tailWord_1252638).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252638).length < 2 ^ (prefixWord ++ tailWord_1252638).sum := by decide
  have hdescent : baseEnd_1252638 < baseStart_1252638 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252638) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252641 : List Nat := [1, 2, 3, 2, 1, 1, 1, 3, 5, 2, 2]
def baseStart_1252641 : Nat := 118140960795 + 1252641 * 2 ^ 59
def prefixEnd_1252641 : Nat := 4983230072969 + 3 ^ 40 * 1252641 * 2
def baseEnd_1252641 : Nat := 643206920528738770026715

theorem tailTrace_1252641 : CollatzResearch.WordTrace tailWord_1252641 prefixEnd_1252641 643206920528738770026715 := by
  unfold tailWord_1252641
  simp only [CollatzResearch.WordTrace]
  refine ⟨45687570654903065895749777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30458380436602043930499851 45687570654903065895749777)
  ·
    refine ⟨34265677991177299421812333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45687570654903065895749777 34265677991177299421812333)
    ·
      refine ⟨12849629246691487283179625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34265677991177299421812333 12849629246691487283179625)
      ·
        refine ⟨9637221935018615462384719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12849629246691487283179625 9637221935018615462384719)
        ·
          refine ⟨14455832902527923193577079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9637221935018615462384719 14455832902527923193577079)
          ·
            refine ⟨21683749353791884790365619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14455832902527923193577079 21683749353791884790365619)
            ·
              refine ⟨32525624030687827185548429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21683749353791884790365619 32525624030687827185548429)
              ·
                refine ⟨12197109011507935194580661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 32525624030687827185548429 12197109011507935194580661)
                ·
                  refine ⟨1143478969828868924491937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 12197109011507935194580661 1143478969828868924491937)
                  ·
                    refine ⟨857609227371651693368953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1143478969828868924491937 857609227371651693368953)
                    ·
                      refine ⟨643206920528738770026715, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857609227371651693368953 643206920528738770026715)
                      ·
                        rfl

theorem cell23_1252641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 1, 3, 5, 2, 2].length) (baseStart_1252641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252641 prefixEnd_1252641 := by exact prefixLift 1252641
  have htrace : WordTrace (prefixWord ++ tailWord_1252641) baseStart_1252641 baseEnd_1252641 := by
    simpa [prefixWord, tailWord_1252641, baseEnd_1252641] using wordTrace_append hprefix tailTrace_1252641
  have hstable : (prefixWord ++ tailWord_1252641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252641).length < 2 ^ (prefixWord ++ tailWord_1252641).sum := by decide
  have hdescent : baseEnd_1252641 < baseStart_1252641 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252658 : List Nat := [3, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4]
def baseStart_1252658 : Nat := 118140960795 + 1252658 * 2 ^ 59
def prefixEnd_1252658 : Nat := 4983230072969 + 3 ^ 40 * 1252658 * 2
def baseEnd_1252658 : Nat := 643215649699865203514137

theorem tailTrace_1252658 : CollatzResearch.WordTrace tailWord_1252658 prefixEnd_1252658 643215649699865203514137 := by
  unfold tailWord_1252658
  simp only [CollatzResearch.WordTrace]
  refine ⟨11422047673960369449779657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30458793797227651866079085 11422047673960369449779657)
  ·
    refine ⟨8566535755470277087334743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11422047673960369449779657 8566535755470277087334743)
    ·
      refine ⟨12849803633205415631002115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566535755470277087334743 12849803633205415631002115)
      ·
        refine ⟨19274705449808123446503173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12849803633205415631002115 19274705449808123446503173)
        ·
          refine ⟨3614007271839023146219345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19274705449808123446503173 3614007271839023146219345)
          ·
            refine ⟨2710505453879267359664509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3614007271839023146219345 2710505453879267359664509)
            ·
              refine ⟨1016439545204725259874191, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2710505453879267359664509 1016439545204725259874191)
              ·
                refine ⟨1524659317807087889811287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016439545204725259874191 1524659317807087889811287)
                ·
                  refine ⟨2286988976710631834716931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524659317807087889811287 2286988976710631834716931)
                  ·
                    refine ⟨3430483465065947752075397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2286988976710631834716931 3430483465065947752075397)
                    ·
                      refine ⟨643215649699865203514137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3430483465065947752075397 643215649699865203514137)
                      ·
                        rfl

theorem cell23_1252658_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 2, 3, 1, 1, 1, 4].length) (baseStart_1252658 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252658 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252658 prefixEnd_1252658 := by exact prefixLift 1252658
  have htrace : WordTrace (prefixWord ++ tailWord_1252658) baseStart_1252658 baseEnd_1252658 := by
    simpa [prefixWord, tailWord_1252658, baseEnd_1252658] using wordTrace_append hprefix tailTrace_1252658
  have hstable : (prefixWord ++ tailWord_1252658).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252658).length < 2 ^ (prefixWord ++ tailWord_1252658).sum := by decide
  have hdescent : baseEnd_1252658 < baseStart_1252658 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252658) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252661 : List Nat := [1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 5]
def baseStart_1252661 : Nat := 118140960795 + 1252661 * 2 ^ 59
def prefixEnd_1252661 : Nat := 4983230072969 + 3 ^ 40 * 1252661 * 2
def baseEnd_1252661 : Nat := 643217190141828691776623

theorem tailTrace_1252661 : CollatzResearch.WordTrace tailWord_1252661 prefixEnd_1252661 643217190141828691776623 := by
  unfold tailWord_1252661
  simp only [CollatzResearch.WordTrace]
  refine ⟨45688300114830609311477837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30458866743220406207651891 45688300114830609311477837)
  ·
    refine ⟨17133112543061478491804189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45688300114830609311477837 17133112543061478491804189)
    ·
      refine ⟨6424917203648054434426571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17133112543061478491804189 6424917203648054434426571)
      ·
        refine ⟨9637375805472081651639857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6424917203648054434426571 9637375805472081651639857)
        ·
          refine ⟨7228031854104061238729893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9637375805472081651639857 7228031854104061238729893)
          ·
            refine ⟨1355255972644511482261855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7228031854104061238729893 1355255972644511482261855)
            ·
              refine ⟨2032883958966767223392783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355255972644511482261855 2032883958966767223392783)
              ·
                refine ⟨3049325938450150835089175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2032883958966767223392783 3049325938450150835089175)
                ·
                  refine ⟨4573988907675226252633763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3049325938450150835089175 4573988907675226252633763)
                  ·
                    refine ⟨6860983361512839378950645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4573988907675226252633763 6860983361512839378950645)
                    ·
                      refine ⟨643217190141828691776623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6860983361512839378950645 643217190141828691776623)
                      ·
                        rfl

theorem cell23_1252661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 4, 1, 1, 1, 1, 5].length) (baseStart_1252661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252661 prefixEnd_1252661 := by exact prefixLift 1252661
  have htrace : WordTrace (prefixWord ++ tailWord_1252661) baseStart_1252661 baseEnd_1252661 := by
    simpa [prefixWord, tailWord_1252661, baseEnd_1252661] using wordTrace_append hprefix tailTrace_1252661
  have hstable : (prefixWord ++ tailWord_1252661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252661).length < 2 ^ (prefixWord ++ tailWord_1252661).sum := by decide
  have hdescent : baseEnd_1252661 < baseStart_1252661 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252669 : List Nat := [1, 4, 1, 5, 1, 2, 2, 2, 1, 1, 3]
def baseStart_1252669 : Nat := 118140960795 + 1252669 * 2 ^ 59
def prefixEnd_1252669 : Nat := 4983230072969 + 3 ^ 40 * 1252669 * 2
def baseEnd_1252669 : Nat := 643221297987064660476587

theorem tailTrace_1252669 : CollatzResearch.WordTrace tailWord_1252669 prefixEnd_1252669 643221297987064660476587 := by
  unfold tailWord_1252669
  simp only [CollatzResearch.WordTrace]
  refine ⟨45688591898801626677769061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30459061265867751118512707 45688591898801626677769061)
  ·
    refine ⟨8566610981025305002081699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45688591898801626677769061 8566610981025305002081699)
    ·
      refine ⟨12849916471537957503122549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8566610981025305002081699 12849916471537957503122549)
      ·
        refine ⟨1204679669206683515917739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 12849916471537957503122549 1204679669206683515917739)
        ·
          refine ⟨1807019503810025273876609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1204679669206683515917739 1807019503810025273876609)
          ·
            refine ⟨1355264627857518955407457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807019503810025273876609 1355264627857518955407457)
            ·
              refine ⟨1016448470893139216555593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355264627857518955407457 1016448470893139216555593)
              ·
                refine ⟨762336353169854412416695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1016448470893139216555593 762336353169854412416695)
                ·
                  refine ⟨1143504529754781618625043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762336353169854412416695 1143504529754781618625043)
                  ·
                    refine ⟨1715256794632172427937565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1143504529754781618625043 1715256794632172427937565)
                    ·
                      refine ⟨643221297987064660476587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1715256794632172427937565 643221297987064660476587)
                      ·
                        rfl

theorem cell23_1252669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 2, 2, 1, 1, 3].length) (baseStart_1252669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252669 prefixEnd_1252669 := by exact prefixLift 1252669
  have htrace : WordTrace (prefixWord ++ tailWord_1252669) baseStart_1252669 baseEnd_1252669 := by
    simpa [prefixWord, tailWord_1252669, baseEnd_1252669] using wordTrace_append hprefix tailTrace_1252669
  have hstable : (prefixWord ++ tailWord_1252669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252669).length < 2 ^ (prefixWord ++ tailWord_1252669).sum := by decide
  have hdescent : baseEnd_1252669 < baseStart_1252669 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252691 : List Nat := [1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 3]
def baseStart_1252691 : Nat := 118140960795 + 1252691 * 2 ^ 59
def prefixEnd_1252691 : Nat := 4983230072969 + 3 ^ 40 * 1252691 * 2
def baseEnd_1252691 : Nat := 643232594561463574401485

theorem tailTrace_1252691 : CollatzResearch.WordTrace tailWord_1252691 prefixEnd_1252691 643232594561463574401485 := by
  unfold tailWord_1252691
  simp only [CollatzResearch.WordTrace]
  refine ⟨45689394304721924435069927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30459596203147949623379951 45689394304721924435069927)
  ·
    refine ⟨68534091457082886652604891, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45689394304721924435069927 68534091457082886652604891)
    ·
      refine ⟨102801137185624329978907337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68534091457082886652604891 102801137185624329978907337)
      ·
        refine ⟨77100852889218247484180503, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 102801137185624329978907337 77100852889218247484180503)
        ·
          refine ⟨115651279333827371226270755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77100852889218247484180503 115651279333827371226270755)
          ·
            refine ⟨173476919000741056839406133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 115651279333827371226270755 173476919000741056839406133)
            ·
              refine ⟨16263461156319474078694325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 173476919000741056839406133 16263461156319474078694325)
              ·
                refine ⟨1524699483404950694877593, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 16263461156319474078694325 1524699483404950694877593)
                ·
                  refine ⟨1143524612553713021158195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1524699483404950694877593 1143524612553713021158195)
                  ·
                    refine ⟨1715286918830569531737293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1143524612553713021158195 1715286918830569531737293)
                    ·
                      refine ⟨643232594561463574401485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1715286918830569531737293 643232594561463574401485)
                      ·
                        rfl

theorem cell23_1252691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 5, 5, 2, 1, 3].length) (baseStart_1252691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252691 prefixEnd_1252691 := by exact prefixLift 1252691
  have htrace : WordTrace (prefixWord ++ tailWord_1252691) baseStart_1252691 baseEnd_1252691 := by
    simpa [prefixWord, tailWord_1252691, baseEnd_1252691] using wordTrace_append hprefix tailTrace_1252691
  have hstable : (prefixWord ++ tailWord_1252691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252691).length < 2 ^ (prefixWord ++ tailWord_1252691).sum := by decide
  have hdescent : baseEnd_1252691 < baseStart_1252691 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252712 : List Nat := [2, 1, 4, 2, 4, 1, 2, 1, 1, 2, 3]
def baseStart_1252712 : Nat := 118140960795 + 1252712 * 2 ^ 59
def prefixEnd_1252712 : Nat := 4983230072969 + 3 ^ 40 * 1252712 * 2
def baseEnd_1252712 : Nat := 643243377655207992238889

theorem tailTrace_1252712 : CollatzResearch.WordTrace tailWord_1252712 prefixEnd_1252712 643243377655207992238889 := by
  unfold tailWord_1252712
  simp only [CollatzResearch.WordTrace]
  refine ⟨22845080118822922510792195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30460106825097230014389593 22845080118822922510792195)
  ·
    refine ⟨34267620178234383766188293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22845080118822922510792195 34267620178234383766188293)
    ·
      refine ⟨6425178783418946956160305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34267620178234383766188293 6425178783418946956160305)
      ·
        refine ⟨4818884087564210217120229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6425178783418946956160305 4818884087564210217120229)
        ·
          refine ⟨903540766418289415710043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 4818884087564210217120229 903540766418289415710043)
          ·
            refine ⟨1355311149627434123565065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 903540766418289415710043 1355311149627434123565065)
            ·
              refine ⟨1016483362220575592673799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1355311149627434123565065 1016483362220575592673799)
              ·
                refine ⟨1524725043330863389010699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1016483362220575592673799 1524725043330863389010699)
                ·
                  refine ⟨2287087564996295083516049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524725043330863389010699 2287087564996295083516049)
                  ·
                    refine ⟨1715315673747221312637037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2287087564996295083516049 1715315673747221312637037)
                    ·
                      refine ⟨643243377655207992238889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1715315673747221312637037 643243377655207992238889)
                      ·
                        rfl

theorem cell23_1252712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 4, 1, 2, 1, 1, 2, 3].length) (baseStart_1252712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252712 prefixEnd_1252712 := by exact prefixLift 1252712
  have htrace : WordTrace (prefixWord ++ tailWord_1252712) baseStart_1252712 baseEnd_1252712 := by
    simpa [prefixWord, tailWord_1252712, baseEnd_1252712] using wordTrace_append hprefix tailTrace_1252712
  have hstable : (prefixWord ++ tailWord_1252712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252712).length < 2 ^ (prefixWord ++ tailWord_1252712).sum := by decide
  have hdescent : baseEnd_1252712 < baseStart_1252712 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252791 : List Nat := [1, 1, 3, 1, 3, 2, 2, 1, 2, 5, 2]
def baseStart_1252791 : Nat := 118140960795 + 1252791 * 2 ^ 59
def prefixEnd_1252791 : Nat := 4983230072969 + 3 ^ 40 * 1252791 * 2
def baseEnd_1252791 : Nat := 643283942626913183151025

theorem tailTrace_1252791 : CollatzResearch.WordTrace tailWord_1252791 prefixEnd_1252791 643283942626913183151025 := by
  unfold tailWord_1252791
  simp only [CollatzResearch.WordTrace]
  refine ⟨45693041604359641513710227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30462027736239761009140151 45693041604359641513710227)
  ·
    refine ⟨68539562406539462270565341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45693041604359641513710227 68539562406539462270565341)
    ·
      refine ⟨25702335902452298351462003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68539562406539462270565341 25702335902452298351462003)
      ·
        refine ⟨38553503853678447527193005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25702335902452298351462003 38553503853678447527193005)
        ·
          refine ⟨14457563945129417822697377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 38553503853678447527193005 14457563945129417822697377)
          ·
            refine ⟨10843172958847063367023033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14457563945129417822697377 10843172958847063367023033)
            ·
              refine ⟨8132379719135297525267275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10843172958847063367023033 8132379719135297525267275)
              ·
                refine ⟨12198569578702946287900913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8132379719135297525267275 12198569578702946287900913)
                ·
                  refine ⟨9148927184027209715925685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12198569578702946287900913 9148927184027209715925685)
                  ·
                    refine ⟨857711923502550910868033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 9148927184027209715925685 857711923502550910868033)
                    ·
                      refine ⟨643283942626913183151025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857711923502550910868033 643283942626913183151025)
                      ·
                        rfl

theorem cell23_1252791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 2, 1, 2, 5, 2].length) (baseStart_1252791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252791 prefixEnd_1252791 := by exact prefixLift 1252791
  have htrace : WordTrace (prefixWord ++ tailWord_1252791) baseStart_1252791 baseEnd_1252791 := by
    simpa [prefixWord, tailWord_1252791, baseEnd_1252791] using wordTrace_append hprefix tailTrace_1252791
  have hstable : (prefixWord ++ tailWord_1252791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252791).length < 2 ^ (prefixWord ++ tailWord_1252791).sum := by decide
  have hdescent : baseEnd_1252791 < baseStart_1252791 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252814 : List Nat := [4, 1, 1, 1, 2, 1, 2, 1, 2, 8]
def baseStart_1252814 : Nat := 118140960795 + 1252814 * 2 ^ 59
def prefixEnd_1252814 : Nat := 4983230072969 + 3 ^ 40 * 1252814 * 2
def baseEnd_1252814 : Nat := 214431917560655531054473

theorem tailTrace_1252814 : CollatzResearch.WordTrace tailWord_1252814 prefixEnd_1252814 214431917560655531054473 := by
  unfold tailWord_1252814
  simp only [CollatzResearch.WordTrace]
  refine ⟨5711735060409539555224687, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30462586988850877627864997 5711735060409539555224687)
  ·
    refine ⟨8567602590614309332837031, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 5711735060409539555224687 8567602590614309332837031)
    ·
      refine ⟨12851403885921463999255547, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8567602590614309332837031 12851403885921463999255547)
      ·
        refine ⟨19277105828882195998883321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12851403885921463999255547 19277105828882195998883321)
        ·
          refine ⟨14457829371661646999162491, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19277105828882195998883321 14457829371661646999162491)
          ·
            refine ⟨21686744057492470498743737, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14457829371661646999162491 21686744057492470498743737)
            ·
              refine ⟨16265058043119352874057803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 21686744057492470498743737 16265058043119352874057803)
              ·
                refine ⟨24397587064679029311086705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 16265058043119352874057803 24397587064679029311086705)
                ·
                  refine ⟨18298190298509271983315029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 24397587064679029311086705 18298190298509271983315029)
                  ·
                    refine ⟨214431917560655531054473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 18298190298509271983315029 214431917560655531054473)
                    ·
                      rfl

theorem cell23_1252814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 2, 1, 2, 1, 2, 8].length) (baseStart_1252814 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252814 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252814 prefixEnd_1252814 := by exact prefixLift 1252814
  have htrace : WordTrace (prefixWord ++ tailWord_1252814) baseStart_1252814 baseEnd_1252814 := by
    simpa [prefixWord, tailWord_1252814, baseEnd_1252814] using wordTrace_append hprefix tailTrace_1252814
  have hstable : (prefixWord ++ tailWord_1252814).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252814).length < 2 ^ (prefixWord ++ tailWord_1252814).sum := by decide
  have hdescent : baseEnd_1252814 < baseStart_1252814 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252861 : List Nat := [1, 4, 1, 1, 1, 4, 2, 3, 6]
def baseStart_1252861 : Nat := 118140960795 + 1252861 * 2 ^ 59
def prefixEnd_1252861 : Nat := 4983230072969 + 3 ^ 40 * 1252861 * 2
def baseEnd_1252861 : Nat := 71479987363636434363967

theorem tailTrace_1252861 : CollatzResearch.WordTrace tailWord_1252861 prefixEnd_1252861 71479987363636434363967 := by
  unfold tailWord_1252861
  simp only [CollatzResearch.WordTrace]
  refine ⟨45695594714106043468758437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30463729809404028979172291 45695594714106043468758437)
  ·
    refine ⟨8567924008894883150392207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45695594714106043468758437 8567924008894883150392207)
    ·
      refine ⟨12851886013342324725588311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8567924008894883150392207 12851886013342324725588311)
      ·
        refine ⟨19277829020013487088382467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12851886013342324725588311 19277829020013487088382467)
        ·
          refine ⟨28916743530020230632573701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19277829020013487088382467 28916743530020230632573701)
          ·
            refine ⟨5421889411878793243607569, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28916743530020230632573701 5421889411878793243607569)
            ·
              refine ⟨4066417058909094932705677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5421889411878793243607569 4066417058909094932705677)
              ·
                refine ⟨1524906397090910599764629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4066417058909094932705677 1524906397090910599764629)
                ·
                  refine ⟨71479987363636434363967, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1524906397090910599764629 71479987363636434363967)
                  ·
                    rfl

theorem cell23_1252861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 4, 2, 3, 6].length) (baseStart_1252861 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252861 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252861 prefixEnd_1252861 := by exact prefixLift 1252861
  have htrace : WordTrace (prefixWord ++ tailWord_1252861) baseStart_1252861 baseEnd_1252861 := by
    simpa [prefixWord, tailWord_1252861, baseEnd_1252861] using wordTrace_append hprefix tailTrace_1252861
  have hstable : (prefixWord ++ tailWord_1252861).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252861).length < 2 ^ (prefixWord ++ tailWord_1252861).sum := by decide
  have hdescent : baseEnd_1252861 < baseStart_1252861 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252875 : List Nat := [1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 3]
def baseStart_1252875 : Nat := 118140960795 + 1252875 * 2 ^ 59
def prefixEnd_1252875 : Nat := 4983230072969 + 3 ^ 40 * 1252875 * 2
def baseEnd_1252875 : Nat := 643327075001890854500639

theorem tailTrace_1252875 : CollatzResearch.WordTrace tailWord_1252875 prefixEnd_1252875 643327075001890854500639 := by
  unfold tailWord_1252875
  simp only [CollatzResearch.WordTrace]
  refine ⟨45696105336055323859768079, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30464070224036882573178719 45696105336055323859768079)
  ·
    refine ⟨68544158004082985789652119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45696105336055323859768079 68544158004082985789652119)
    ·
      refine ⟨102816237006124478684478179, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68544158004082985789652119 102816237006124478684478179)
      ·
        refine ⟨154224355509186718026717269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102816237006124478684478179 154224355509186718026717269)
        ·
          refine ⟨1807316666123281851875593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 154224355509186718026717269 1807316666123281851875593)
          ·
            refine ⟨1355487499592461388906695, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807316666123281851875593 1355487499592461388906695)
            ·
              refine ⟨2033231249388692083360043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355487499592461388906695 2033231249388692083360043)
              ·
                refine ⟨3049846874083038125040065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033231249388692083360043 3049846874083038125040065)
                ·
                  refine ⟨2287385155562278593780049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3049846874083038125040065 2287385155562278593780049)
                  ·
                    refine ⟨1715538866671708945335037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2287385155562278593780049 1715538866671708945335037)
                    ·
                      refine ⟨643327075001890854500639, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1715538866671708945335037 643327075001890854500639)
                      ·
                        rfl

theorem cell23_1252875_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 8, 2, 1, 1, 2, 2, 3].length) (baseStart_1252875 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252875 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252875 prefixEnd_1252875 := by exact prefixLift 1252875
  have htrace : WordTrace (prefixWord ++ tailWord_1252875) baseStart_1252875 baseEnd_1252875 := by
    simpa [prefixWord, tailWord_1252875, baseEnd_1252875] using wordTrace_append hprefix tailTrace_1252875
  have hstable : (prefixWord ++ tailWord_1252875).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252875).length < 2 ^ (prefixWord ++ tailWord_1252875).sum := by decide
  have hdescent : baseEnd_1252875 < baseStart_1252875 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252875) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252925 : List Nat := [1, 4, 1, 3, 3, 1, 2, 2, 1, 5]
def baseStart_1252925 : Nat := 118140960795 + 1252925 * 2 ^ 59
def prefixEnd_1252925 : Nat := 4983230072969 + 3 ^ 40 * 1252925 * 2
def baseEnd_1252925 : Nat := 214450916344871886291803

theorem tailTrace_1252925 : CollatzResearch.WordTrace tailWord_1252925 prefixEnd_1252925 214450916344871886291803 := by
  unfold tailWord_1252925
  simp only [CollatzResearch.WordTrace]
  refine ⟨45697928985874182399088229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30465285990582788266058819 45697928985874182399088229)
  ·
    refine ⟨8568361684851409199829043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45697928985874182399088229 8568361684851409199829043)
    ·
      refine ⟨12852542527277113799743565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8568361684851409199829043 12852542527277113799743565)
      ·
        refine ⟨4819703447728917674903837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 12852542527277113799743565 4819703447728917674903837)
        ·
          refine ⟨1807388792898344128088939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 4819703447728917674903837 1807388792898344128088939)
          ·
            refine ⟨2711083189347516192133409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807388792898344128088939 2711083189347516192133409)
            ·
              refine ⟨2033312392010637144100057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711083189347516192133409 2033312392010637144100057)
              ·
                refine ⟨1524984294007977858075043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033312392010637144100057 1524984294007977858075043)
                ·
                  refine ⟨2287476441011966787112565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1524984294007977858075043 2287476441011966787112565)
                  ·
                    refine ⟨214450916344871886291803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2287476441011966787112565 214450916344871886291803)
                    ·
                      rfl

theorem cell23_1252925_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 3, 1, 2, 2, 1, 5].length) (baseStart_1252925 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252925 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252925 prefixEnd_1252925 := by exact prefixLift 1252925
  have htrace : WordTrace (prefixWord ++ tailWord_1252925) baseStart_1252925 baseEnd_1252925 := by
    simpa [prefixWord, tailWord_1252925, baseEnd_1252925] using wordTrace_append hprefix tailTrace_1252925
  have hstable : (prefixWord ++ tailWord_1252925).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252925).length < 2 ^ (prefixWord ++ tailWord_1252925).sum := by decide
  have hdescent : baseEnd_1252925 < baseStart_1252925 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252925) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252948 : List Nat := [2, 4, 1, 1, 1, 2, 4, 1, 1, 1, 5]
def baseStart_1252948 : Nat := 118140960795 + 1252948 * 2 ^ 59
def prefixEnd_1252948 : Nat := 4983230072969 + 3 ^ 40 * 1252948 * 2
def baseEnd_1252948 : Nat := 643364559089669068887803

theorem tailTrace_1252948 : CollatzResearch.WordTrace tailWord_1252948 prefixEnd_1252948 643364559089669068887803 := by
  unfold tailWord_1252948
  simp only [CollatzResearch.WordTrace]
  refine ⟨22849383932395428663587749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30465845243193904884783665 22849383932395428663587749)
  ·
    refine ⟨4284259487324142874422703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22849383932395428663587749 4284259487324142874422703)
    ·
      refine ⟨6426389230986214311634055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284259487324142874422703 6426389230986214311634055)
      ·
        refine ⟨9639583846479321467451083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6426389230986214311634055 9639583846479321467451083)
        ·
          refine ⟨14459375769718982201176625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9639583846479321467451083 14459375769718982201176625)
          ·
            refine ⟨10844531827289236650882469, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14459375769718982201176625 10844531827289236650882469)
            ·
              refine ⟨2033349717616731872040463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 10844531827289236650882469 2033349717616731872040463)
              ·
                refine ⟨3050024576425097808060695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033349717616731872040463 3050024576425097808060695)
                ·
                  refine ⟨4575036864637646712091043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3050024576425097808060695 4575036864637646712091043)
                  ·
                    refine ⟨6862555296956470068136565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 4575036864637646712091043 6862555296956470068136565)
                    ·
                      refine ⟨643364559089669068887803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 6862555296956470068136565 643364559089669068887803)
                      ·
                        rfl

theorem cell23_1252948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 2, 4, 1, 1, 1, 5].length) (baseStart_1252948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252948 prefixEnd_1252948 := by exact prefixLift 1252948
  have htrace : WordTrace (prefixWord ++ tailWord_1252948) baseStart_1252948 baseEnd_1252948 := by
    simpa [prefixWord, tailWord_1252948, baseEnd_1252948] using wordTrace_append hprefix tailTrace_1252948
  have hstable : (prefixWord ++ tailWord_1252948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252948).length < 2 ^ (prefixWord ++ tailWord_1252948).sum := by decide
  have hdescent : baseEnd_1252948 < baseStart_1252948 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252951 : List Nat := [1, 1, 3, 2, 2, 5, 9]
def baseStart_1252951 : Nat := 118140960795 + 1252951 * 2 ^ 59
def prefixEnd_1252951 : Nat := 4983230072969 + 3 ^ 40 * 1252951 * 2
def baseEnd_1252951 : Nat := 7942791352242377248769

theorem tailTrace_1252951 : CollatzResearch.WordTrace tailWord_1252951 prefixEnd_1252951 7942791352242377248769 := by
  unfold tailWord_1252951
  simp only [CollatzResearch.WordTrace]
  refine ⟨45698877283779988839534707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30465918189186659226356471 45698877283779988839534707)
  ·
    refine ⟨68548315925669983259302061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45698877283779988839534707 68548315925669983259302061)
    ·
      refine ⟨25705618472126243722238273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68548315925669983259302061 25705618472126243722238273)
      ·
        refine ⟨19279213854094682791678705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25705618472126243722238273 19279213854094682791678705)
        ·
          refine ⟨14459410390571012093759029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19279213854094682791678705 14459410390571012093759029)
          ·
            refine ⟨1355569724116032383789909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14459410390571012093759029 1355569724116032383789909)
            ·
              refine ⟨7942791352242377248769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1355569724116032383789909 7942791352242377248769)
              ·
                rfl

theorem cell23_1252951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 5, 9].length) (baseStart_1252951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252951 prefixEnd_1252951 := by exact prefixLift 1252951
  have htrace : WordTrace (prefixWord ++ tailWord_1252951) baseStart_1252951 baseEnd_1252951 := by
    simpa [prefixWord, tailWord_1252951, baseEnd_1252951] using wordTrace_append hprefix tailTrace_1252951
  have hstable : (prefixWord ++ tailWord_1252951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252951).length < 2 ^ (prefixWord ++ tailWord_1252951).sum := by decide
  have hdescent : baseEnd_1252951 < baseStart_1252951 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252968 : List Nat := [2, 1, 4, 3, 1, 2, 2, 8]
def baseStart_1252968 : Nat := 118140960795 + 1252968 * 2 ^ 59
def prefixEnd_1252968 : Nat := 4983230072969 + 3 ^ 40 * 1252968 * 2
def baseEnd_1252968 : Nat := 23828697359361444097693

theorem tailTrace_1252968 : CollatzResearch.WordTrace tailWord_1252968 prefixEnd_1252968 23828697359361444097693 := by
  unfold tailWord_1252968
  simp only [CollatzResearch.WordTrace]
  refine ⟨22849748662359200371451779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30466331549812267161935705 22849748662359200371451779)
  ·
    refine ⟨34274622993538800557177669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22849748662359200371451779 34274622993538800557177669)
    ·
      refine ⟨6426491811288525104470813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 34274622993538800557177669 6426491811288525104470813)
      ·
        refine ⟨2409934429233196914176555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6426491811288525104470813 2409934429233196914176555)
        ·
          refine ⟨3614901643849795371264833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2409934429233196914176555 3614901643849795371264833)
          ·
            refine ⟨2711176232887346528448625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3614901643849795371264833 2711176232887346528448625)
            ·
              refine ⟨2033382174665509896336469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711176232887346528448625 2033382174665509896336469)
              ·
                refine ⟨23828697359361444097693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2033382174665509896336469 23828697359361444097693)
                ·
                  rfl

theorem cell23_1252968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 1, 2, 2, 8].length) (baseStart_1252968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252968 prefixEnd_1252968 := by exact prefixLift 1252968
  have htrace : WordTrace (prefixWord ++ tailWord_1252968) baseStart_1252968 baseEnd_1252968 := by
    simpa [prefixWord, tailWord_1252968, baseEnd_1252968] using wordTrace_append hprefix tailTrace_1252968
  have hstable : (prefixWord ++ tailWord_1252968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252968).length < 2 ^ (prefixWord ++ tailWord_1252968).sum := by decide
  have hdescent : baseEnd_1252968 < baseStart_1252968 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1252982 : List Nat := [5, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3]
def baseStart_1252982 : Nat := 118140960795 + 1252982 * 2 ^ 59
def prefixEnd_1252982 : Nat := 4983230072969 + 3 ^ 40 * 1252982 * 2
def baseEnd_1252982 : Nat := 643382017431921935862647

theorem tailTrace_1252982 : CollatzResearch.WordTrace tailWord_1252982 prefixEnd_1252982 643382017431921935862647 := by
  unfold tailWord_1252982
  simp only [CollatzResearch.WordTrace]
  refine ⟨2856250496666730070869575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 30466671964445120755942133 2856250496666730070869575)
  ·
    refine ⟨4284375745000095106304363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 2856250496666730070869575 4284375745000095106304363)
    ·
      refine ⟨6426563617500142659456545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4284375745000095106304363 6426563617500142659456545)
      ·
        refine ⟨4819922713125106994592409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6426563617500142659456545 4819922713125106994592409)
        ·
          refine ⟨3614942034843830245944307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4819922713125106994592409 3614942034843830245944307)
          ·
            refine ⟨5422413052265745368916461, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3614942034843830245944307 5422413052265745368916461)
            ·
              refine ⟨2033404894599654513343673, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5422413052265745368916461 2033404894599654513343673)
              ·
                refine ⟨1525053670949740885007755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033404894599654513343673 1525053670949740885007755)
                ·
                  refine ⟨2287580506424611327511633, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525053670949740885007755 2287580506424611327511633)
                  ·
                    refine ⟨1715685379818458495633725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2287580506424611327511633 1715685379818458495633725)
                    ·
                      refine ⟨643382017431921935862647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1715685379818458495633725 643382017431921935862647)
                      ·
                        rfl

theorem cell23_1252982_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 2, 2, 1, 3, 2, 1, 2, 3].length) (baseStart_1252982 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1252982 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1252982 prefixEnd_1252982 := by exact prefixLift 1252982
  have htrace : WordTrace (prefixWord ++ tailWord_1252982) baseStart_1252982 baseEnd_1252982 := by
    simpa [prefixWord, tailWord_1252982, baseEnd_1252982] using wordTrace_append hprefix tailTrace_1252982
  have hstable : (prefixWord ++ tailWord_1252982).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1252982).length < 2 ^ (prefixWord ++ tailWord_1252982).sum := by decide
  have hdescent : baseEnd_1252982 < baseStart_1252982 := by decide
  rcases family_descends (prefixWord ++ tailWord_1252982) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253022 : List Nat := [4, 3, 1, 1, 1, 2, 1, 2, 3, 3, 2]
def baseStart_1253022 : Nat := 118140960795 + 1253022 * 2 ^ 59
def prefixEnd_1253022 : Nat := 4983230072969 + 3 ^ 40 * 1253022 * 2
def baseEnd_1253022 : Nat := 643402556658101779362463

theorem tailTrace_1253022 : CollatzResearch.WordTrace tailWord_1253022 prefixEnd_1253022 643402556658101779362463 := by
  unfold tailWord_1253022
  simp only [CollatzResearch.WordTrace]
  refine ⟨5712683358315345995671165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30467644577681845310246213 5712683358315345995671165)
  ·
    refine ⟨2142256259368254748376687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 5712683358315345995671165 2142256259368254748376687)
    ·
      refine ⟨3213384389052382122565031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142256259368254748376687 3213384389052382122565031)
      ·
        refine ⟨4820076583578573183847547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3213384389052382122565031 4820076583578573183847547)
        ·
          refine ⟨7230114875367859775771321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4820076583578573183847547 7230114875367859775771321)
          ·
            refine ⟨5422586156525894831828491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7230114875367859775771321 5422586156525894831828491)
            ·
              refine ⟨8133879234788842247742737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422586156525894831828491 8133879234788842247742737)
              ·
                refine ⟨6100409426091631685807053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8133879234788842247742737 6100409426091631685807053)
                ·
                  refine ⟨2287653534784361882177645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6100409426091631685807053 2287653534784361882177645)
                  ·
                    refine ⟨857870075544135705816617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2287653534784361882177645 857870075544135705816617)
                    ·
                      refine ⟨643402556658101779362463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 857870075544135705816617 643402556658101779362463)
                      ·
                        rfl

theorem cell23_1253022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 1, 2, 3, 3, 2].length) (baseStart_1253022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253022 prefixEnd_1253022 := by exact prefixLift 1253022
  have htrace : WordTrace (prefixWord ++ tailWord_1253022) baseStart_1253022 baseEnd_1253022 := by
    simpa [prefixWord, tailWord_1253022, baseEnd_1253022] using wordTrace_append hprefix tailTrace_1253022
  have hstable : (prefixWord ++ tailWord_1253022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253022).length < 2 ^ (prefixWord ++ tailWord_1253022).sum := by decide
  have hdescent : baseEnd_1253022 < baseStart_1253022 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253028 : List Nat := [2, 3, 1, 2, 2, 3, 1, 1, 2, 6]
def baseStart_1253028 : Nat := 118140960795 + 1253028 * 2 ^ 59
def prefixEnd_1253028 : Nat := 4983230072969 + 3 ^ 40 * 1253028 * 2
def baseEnd_1253028 : Nat := 214468545847342918629145

theorem tailTrace_1253028 : CollatzResearch.WordTrace tailWord_1253028 prefixEnd_1253028 214468545847342918629145 := by
  unfold tailWord_1253028
  simp only [CollatzResearch.WordTrace]
  refine ⟨22850842852250515495043869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30467790469667353993391825 22850842852250515495043869)
  ·
    refine ⟨8569066069593943310641451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22850842852250515495043869 8569066069593943310641451)
    ·
      refine ⟨12853599104390914965962177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 8569066069593943310641451 12853599104390914965962177)
      ·
        refine ⟨9640199328293186224471633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12853599104390914965962177 9640199328293186224471633)
        ·
          refine ⟨7230149496219889668353725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9640199328293186224471633 7230149496219889668353725)
          ·
            refine ⟨2711306061082458625632647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7230149496219889668353725 2711306061082458625632647)
            ·
              refine ⟨4066959091623687938448971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711306061082458625632647 4066959091623687938448971)
              ·
                refine ⟨6100438637435531907673457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4066959091623687938448971 6100438637435531907673457)
                ·
                  refine ⟨4575328978076648930755093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6100438637435531907673457 4575328978076648930755093)
                  ·
                    refine ⟨214468545847342918629145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4575328978076648930755093 214468545847342918629145)
                    ·
                      rfl

theorem cell23_1253028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 3, 1, 1, 2, 6].length) (baseStart_1253028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253028 prefixEnd_1253028 := by exact prefixLift 1253028
  have htrace : WordTrace (prefixWord ++ tailWord_1253028) baseStart_1253028 baseEnd_1253028 := by
    simpa [prefixWord, tailWord_1253028, baseEnd_1253028] using wordTrace_append hprefix tailTrace_1253028
  have hstable : (prefixWord ++ tailWord_1253028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253028).length < 2 ^ (prefixWord ++ tailWord_1253028).sum := by decide
  have hdescent : baseEnd_1253028 < baseStart_1253028 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253062 : List Nat := [6, 1, 2, 1, 1, 1, 1, 2, 2, 6]
def baseStart_1253062 : Nat := 118140960795 + 1253062 * 2 ^ 59
def prefixEnd_1253062 : Nat := 4983230072969 + 3 ^ 40 * 1253062 * 2
def baseEnd_1253062 : Nat := 214474365294760540954093

theorem tailTrace_1253062 : CollatzResearch.WordTrace tailWord_1253062 prefixEnd_1253062 214474365294760540954093 := by
  unfold tailWord_1253062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428216430824307962400795, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30468617190918569864550293 1428216430824307962400795)
  ·
    refine ⟨2142324646236461943601193, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1428216430824307962400795 2142324646236461943601193)
    ·
      refine ⟨1606743484677346457700895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2142324646236461943601193 1606743484677346457700895)
      ·
        refine ⟨2410115227016019686551343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1606743484677346457700895 2410115227016019686551343)
        ·
          refine ⟨3615172840524029529827015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410115227016019686551343 3615172840524029529827015)
          ·
            refine ⟨5422759260786044294740523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615172840524029529827015 5422759260786044294740523)
            ·
              refine ⟨8134138891179066442110785, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5422759260786044294740523 8134138891179066442110785)
              ·
                refine ⟨6100604168384299831583089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8134138891179066442110785 6100604168384299831583089)
                ·
                  refine ⟨4575453126288224873687317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6100604168384299831583089 4575453126288224873687317)
                  ·
                    refine ⟨214474365294760540954093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 4575453126288224873687317 214474365294760540954093)
                    ·
                      rfl

theorem cell23_1253062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 1, 1, 1, 2, 2, 6].length) (baseStart_1253062 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253062 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253062 prefixEnd_1253062 := by exact prefixLift 1253062
  have htrace : WordTrace (prefixWord ++ tailWord_1253062) baseStart_1253062 baseEnd_1253062 := by
    simpa [prefixWord, tailWord_1253062, baseEnd_1253062] using wordTrace_append hprefix tailTrace_1253062
  have hstable : (prefixWord ++ tailWord_1253062).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253062).length < 2 ^ (prefixWord ++ tailWord_1253062).sum := by decide
  have hdescent : baseEnd_1253062 < baseStart_1253062 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253175 : List Nat := [1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 3]
def baseStart_1253175 : Nat := 118140960795 + 1253175 * 2 ^ 59
def prefixEnd_1253175 : Nat := 4983230072969 + 3 ^ 40 * 1253175 * 2
def baseEnd_1253175 : Nat := 643481119198239680749259

theorem tailTrace_1253175 : CollatzResearch.WordTrace tailWord_1253175 prefixEnd_1253175 643481119198239680749259 := by
  unfold tailWord_1253175
  simp only [CollatzResearch.WordTrace]
  refine ⟨45707047234968475095688979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30471364823312316730459319 45707047234968475095688979)
  ·
    refine ⟨68560570852452712643533469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45707047234968475095688979 68560570852452712643533469)
    ·
      refine ⟨25710214069669767241325051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68560570852452712643533469 25710214069669767241325051)
      ·
        refine ⟨38565321104504650861987577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25710214069669767241325051 38565321104504650861987577)
        ·
          refine ⟨28923990828378488146490683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 38565321104504650861987577 28923990828378488146490683)
          ·
            refine ⟨43385986242567732219736025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28923990828378488146490683 43385986242567732219736025)
            ·
              refine ⟨32539489681925799164802019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 43385986242567732219736025 32539489681925799164802019)
              ·
                refine ⟨48809234522888698747203029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32539489681925799164802019 48809234522888698747203029)
                ·
                  refine ⟨1143966434130203876887571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48809234522888698747203029 1143966434130203876887571)
                  ·
                    refine ⟨1715949651195305815331357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1143966434130203876887571 1715949651195305815331357)
                    ·
                      refine ⟨643481119198239680749259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1715949651195305815331357 643481119198239680749259)
                      ·
                        rfl

theorem cell23_1253175_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 1, 7, 1, 3].length) (baseStart_1253175 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253175 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253175 prefixEnd_1253175 := by exact prefixLift 1253175
  have htrace : WordTrace (prefixWord ++ tailWord_1253175) baseStart_1253175 baseEnd_1253175 := by
    simpa [prefixWord, tailWord_1253175, baseEnd_1253175] using wordTrace_append hprefix tailTrace_1253175
  have hstable : (prefixWord ++ tailWord_1253175).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253175).length < 2 ^ (prefixWord ++ tailWord_1253175).sum := by decide
  have hdescent : baseEnd_1253175 < baseStart_1253175 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253175) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253182 : List Nat := [4, 2, 1, 2, 2, 2, 2, 2, 6]
def baseStart_1253182 : Nat := 118140960795 + 1253182 * 2 ^ 59
def prefixEnd_1253182 : Nat := 4983230072969 + 3 ^ 40 * 1253182 * 2
def baseEnd_1253182 : Nat := 71498301506980128151303

theorem tailTrace_1253182 : CollatzResearch.WordTrace tailWord_1253182 prefixEnd_1253182 71498301506980128151303 := by
  unfold tailWord_1253182
  simp only [CollatzResearch.WordTrace]
  refine ⟨5713412818242889411399225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 30471535030628743527462533 5713412818242889411399225)
  ·
    refine ⟨4285059613682167058549419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 5713412818242889411399225 4285059613682167058549419)
    ·
      refine ⟨6427589420523250587824129, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4285059613682167058549419 6427589420523250587824129)
      ·
        refine ⟨4820692065392437940868097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6427589420523250587824129 4820692065392437940868097)
        ·
          refine ⟨3615519049044328455651073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 4820692065392437940868097 3615519049044328455651073)
          ·
            refine ⟨2711639286783246341738305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3615519049044328455651073 2711639286783246341738305)
            ·
              refine ⟨2033729465087434756303729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2711639286783246341738305 2033729465087434756303729)
              ·
                refine ⟨1525297098815576067227797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033729465087434756303729 1525297098815576067227797)
                ·
                  refine ⟨71498301506980128151303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1525297098815576067227797 71498301506980128151303)
                  ·
                    rfl

theorem cell23_1253182_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 2, 2, 2, 2, 6].length) (baseStart_1253182 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253182 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253182 prefixEnd_1253182 := by exact prefixLift 1253182
  have htrace : WordTrace (prefixWord ++ tailWord_1253182) baseStart_1253182 baseEnd_1253182 := by
    simpa [prefixWord, tailWord_1253182, baseEnd_1253182] using wordTrace_append hprefix tailTrace_1253182
  have hstable : (prefixWord ++ tailWord_1253182).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253182).length < 2 ^ (prefixWord ++ tailWord_1253182).sum := by decide
  have hdescent : baseEnd_1253182 < baseStart_1253182 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253182) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253215 : List Nat := [1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 4]
def baseStart_1253215 : Nat := 118140960795 + 1253215 * 2 ^ 59
def prefixEnd_1253215 : Nat := 4983230072969 + 3 ^ 40 * 1253215 * 2
def baseEnd_1253215 : Nat := 643501658424419524249075

theorem tailTrace_1253215 : CollatzResearch.WordTrace tailWord_1253215 prefixEnd_1253215 643501658424419524249075 := by
  unfold tailWord_1253215
  simp only [CollatzResearch.WordTrace]
  refine ⟨45708506154823561927145099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30472337436549041284763399 45708506154823561927145099)
  ·
    refine ⟨68562759232235342890717649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45708506154823561927145099 68562759232235342890717649)
    ·
      refine ⟨51422069424176507168038237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68562759232235342890717649 51422069424176507168038237)
      ·
        refine ⟨19283276034066190188014339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 51422069424176507168038237 19283276034066190188014339)
        ·
          refine ⟨28924914051099285282021509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19283276034066190188014339 28924914051099285282021509)
          ·
            refine ⟨5423421384581115990379033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 28924914051099285282021509 5423421384581115990379033)
            ·
              refine ⟨4067566038435836992784275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5423421384581115990379033 4067566038435836992784275)
              ·
                refine ⟨6101349057653755489176413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4067566038435836992784275 6101349057653755489176413)
                ·
                  refine ⟨2288005896620158308441155, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6101349057653755489176413 2288005896620158308441155)
                  ·
                    refine ⟨3432008844930237462661733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2288005896620158308441155 3432008844930237462661733)
                    ·
                      refine ⟨643501658424419524249075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3432008844930237462661733 643501658424419524249075)
                      ·
                        rfl

theorem cell23_1253215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 2, 1, 3, 1, 4].length) (baseStart_1253215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253215 prefixEnd_1253215 := by exact prefixLift 1253215
  have htrace : WordTrace (prefixWord ++ tailWord_1253215) baseStart_1253215 baseEnd_1253215 := by
    simpa [prefixWord, tailWord_1253215, baseEnd_1253215] using wordTrace_append hprefix tailTrace_1253215
  have hstable : (prefixWord ++ tailWord_1253215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253215).length < 2 ^ (prefixWord ++ tailWord_1253215).sum := by decide
  have hdescent : baseEnd_1253215 < baseStart_1253215 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253232 : List Nat := [2, 1, 1, 1, 4, 1, 1, 1, 7, 2, 2]
def baseStart_1253232 : Nat := 118140960795 + 1253232 * 2 ^ 59
def prefixEnd_1253232 : Nat := 4983230072969 + 3 ^ 40 * 1253232 * 2
def baseEnd_1253232 : Nat := 643510387595545957736497

theorem tailTrace_1253232 : CollatzResearch.WordTrace tailWord_1253232 prefixEnd_1253232 643510387595545957736497 := by
  unfold tailWord_1253232
  simp only [CollatzResearch.WordTrace]
  refine ⟨22854563097880986915256975, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30472750797174649220342633 22854563097880986915256975)
  ·
    refine ⟨34281844646821480372885463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22854563097880986915256975 34281844646821480372885463)
    ·
      refine ⟨51422766970232220559328195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34281844646821480372885463 51422766970232220559328195)
      ·
        refine ⟨77134150455348330838992293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51422766970232220559328195 77134150455348330838992293)
        ·
          refine ⟨14462653210377812032311055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 77134150455348330838992293 14462653210377812032311055)
          ·
            refine ⟨21693979815566718048466583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14462653210377812032311055 21693979815566718048466583)
            ·
              refine ⟨32540969723350077072699875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21693979815566718048466583 32540969723350077072699875)
              ·
                refine ⟨48811454585025115609049813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32540969723350077072699875 48811454585025115609049813)
                ·
                  refine ⟨1144018466836526147087105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 48811454585025115609049813 1144018466836526147087105)
                  ·
                    refine ⟨858013850127394610315329, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1144018466836526147087105 858013850127394610315329)
                    ·
                      refine ⟨643510387595545957736497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858013850127394610315329 643510387595545957736497)
                      ·
                        rfl

theorem cell23_1253232_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 1, 7, 2, 2].length) (baseStart_1253232 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253232 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253232 prefixEnd_1253232 := by exact prefixLift 1253232
  have htrace : WordTrace (prefixWord ++ tailWord_1253232) baseStart_1253232 baseEnd_1253232 := by
    simpa [prefixWord, tailWord_1253232, baseEnd_1253232] using wordTrace_append hprefix tailTrace_1253232
  have hstable : (prefixWord ++ tailWord_1253232).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253232).length < 2 ^ (prefixWord ++ tailWord_1253232).sum := by decide
  have hdescent : baseEnd_1253232 < baseStart_1253232 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253232) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253242 : List Nat := [3, 1, 1, 1, 1, 1, 7, 2, 2, 4]
def baseStart_1253242 : Nat := 118140960795 + 1253242 * 2 ^ 59
def prefixEnd_1253242 : Nat := 4983230072969 + 3 ^ 40 * 1253242 * 2
def baseEnd_1253242 : Nat := 214505174134030306203817

theorem tailTrace_1253242 : CollatzResearch.WordTrace tailWord_1253242 prefixEnd_1253242 214505174134030306203817 := by
  unfold tailWord_1253242
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427372731431436384594495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30472993950483830358918653 11427372731431436384594495)
  ·
    refine ⟨17141059097147154576891743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11427372731431436384594495 17141059097147154576891743)
    ·
      refine ⟨25711588645720731865337615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17141059097147154576891743 25711588645720731865337615)
      ·
        refine ⟨38567382968581097798006423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25711588645720731865337615 38567382968581097798006423)
        ·
          refine ⟨57851074452871646697009635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38567382968581097798006423 57851074452871646697009635)
          ·
            refine ⟨86776611679307470045514453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57851074452871646697009635 86776611679307470045514453)
            ·
              refine ⟨2033826836233768829191745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 86776611679307470045514453 2033826836233768829191745)
              ·
                refine ⟨1525370127175326621893809, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2033826836233768829191745 1525370127175326621893809)
                ·
                  refine ⟨1144027595381494966420357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525370127175326621893809 1144027595381494966420357)
                  ·
                    refine ⟨214505174134030306203817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1144027595381494966420357 214505174134030306203817)
                    ·
                      rfl

theorem cell23_1253242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 7, 2, 2, 4].length) (baseStart_1253242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253242 prefixEnd_1253242 := by exact prefixLift 1253242
  have htrace : WordTrace (prefixWord ++ tailWord_1253242) baseStart_1253242 baseEnd_1253242 := by
    simpa [prefixWord, tailWord_1253242, baseEnd_1253242] using wordTrace_append hprefix tailTrace_1253242
  have hstable : (prefixWord ++ tailWord_1253242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253242).length < 2 ^ (prefixWord ++ tailWord_1253242).sum := by decide
  have hdescent : baseEnd_1253242 < baseStart_1253242 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253266 : List Nat := [3, 2, 3, 2, 1, 1, 2, 2, 3, 2, 2]
def baseStart_1253266 : Nat := 118140960795 + 1253266 * 2 ^ 59
def prefixEnd_1253266 : Nat := 4983230072969 + 3 ^ 40 * 1253266 * 2
def baseEnd_1253266 : Nat := 643527845937798824711341

theorem tailTrace_1253266 : CollatzResearch.WordTrace tailWord_1253266 prefixEnd_1253266 643527845937798824711341 := by
  unfold tailWord_1253266
  simp only [CollatzResearch.WordTrace]
  refine ⟨11427591569409699409312913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30473577518425865091501101 11427591569409699409312913)
  ·
    refine ⟨8570693677057274556984685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 11427591569409699409312913 8570693677057274556984685)
    ·
      refine ⟨3214010128896477958869257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8570693677057274556984685 3214010128896477958869257)
      ·
        refine ⟨2410507596672358469151943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3214010128896477958869257 2410507596672358469151943)
        ·
          refine ⟨3615761395008537703727915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410507596672358469151943 3615761395008537703727915)
          ·
            refine ⟨5423642092512806555591873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3615761395008537703727915 5423642092512806555591873)
            ·
              refine ⟨4067731569384604916693905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5423642092512806555591873 4067731569384604916693905)
              ·
                refine ⟨3050798677038453687520429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4067731569384604916693905 3050798677038453687520429)
                ·
                  refine ⟨1144049503889420132820161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3050798677038453687520429 1144049503889420132820161)
                  ·
                    refine ⟨858037127917065099615121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1144049503889420132820161 858037127917065099615121)
                    ·
                      refine ⟨643527845937798824711341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858037127917065099615121 643527845937798824711341)
                      ·
                        rfl

theorem cell23_1253266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 2, 1, 1, 2, 2, 3, 2, 2].length) (baseStart_1253266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253266 prefixEnd_1253266 := by exact prefixLift 1253266
  have htrace : WordTrace (prefixWord ++ tailWord_1253266) baseStart_1253266 baseEnd_1253266 := by
    simpa [prefixWord, tailWord_1253266, baseEnd_1253266] using wordTrace_append hprefix tailTrace_1253266
  have hstable : (prefixWord ++ tailWord_1253266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253266).length < 2 ^ (prefixWord ++ tailWord_1253266).sum := by decide
  have hdescent : baseEnd_1253266 < baseStart_1253266 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253272 : List Nat := [2, 1, 2, 6, 1, 1, 1, 9]
def baseStart_1253272 : Nat := 118140960795 + 1253272 * 2 ^ 59
def prefixEnd_1253272 : Nat := 4983230072969 + 3 ^ 40 * 1253272 * 2
def baseEnd_1253272 : Nat := 23834478771175029675419

theorem tailTrace_1253272 : CollatzResearch.WordTrace tailWord_1253272 prefixEnd_1253272 23834478771175029675419 := by
  unfold tailWord_1253272
  simp only [CollatzResearch.WordTrace]
  refine ⟨22855292557808530330985035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30473723410411373774646713 22855292557808530330985035)
  ·
    refine ⟨34282938836712795496477553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22855292557808530330985035 34282938836712795496477553)
    ·
      refine ⟨25712204127534596622358165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34282938836712795496477553 25712204127534596622358165)
      ·
        refine ⟨1205259568478184216673039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25712204127534596622358165 1205259568478184216673039)
        ·
          refine ⟨1807889352717276325009559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205259568478184216673039 1807889352717276325009559)
          ·
            refine ⟨2711834029075914487514339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1807889352717276325009559 2711834029075914487514339)
            ·
              refine ⟨4067751043613871731271509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2711834029075914487514339 4067751043613871731271509)
              ·
                refine ⟨23834478771175029675419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4067751043613871731271509 23834478771175029675419)
                ·
                  rfl

theorem cell23_1253272_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 6, 1, 1, 1, 9].length) (baseStart_1253272 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253272 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253272 prefixEnd_1253272 := by exact prefixLift 1253272
  have htrace : WordTrace (prefixWord ++ tailWord_1253272) baseStart_1253272 baseEnd_1253272 := by
    simpa [prefixWord, tailWord_1253272, baseEnd_1253272] using wordTrace_append hprefix tailTrace_1253272
  have hstable : (prefixWord ++ tailWord_1253272).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253272).length < 2 ^ (prefixWord ++ tailWord_1253272).sum := by decide
  have hdescent : baseEnd_1253272 < baseStart_1253272 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253272) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253300 : List Nat := [2, 5, 2, 1, 2, 2, 1, 1, 3, 2, 2]
def baseStart_1253300 : Nat := 118140960795 + 1253300 * 2 ^ 59
def prefixEnd_1253300 : Nat := 4983230072969 + 3 ^ 40 * 1253300 * 2
def baseEnd_1253300 : Nat := 643545304280051691686185

theorem tailTrace_1253300 : CollatzResearch.WordTrace tailWord_1253300 prefixEnd_1253300 643545304280051691686185 := by
  unfold tailWord_1253300
  simp only [CollatzResearch.WordTrace]
  refine ⟨22855803179757810721994677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30474404239677080962659569 22855803179757810721994677)
  ·
    refine ⟨2142731548102294755187001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 22855803179757810721994677 2142731548102294755187001)
    ·
      refine ⟨1607048661076721066390251, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2142731548102294755187001 1607048661076721066390251)
      ·
        refine ⟨2410572991615081599585377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607048661076721066390251 2410572991615081599585377)
        ·
          refine ⟨1807929743711311199689033, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2410572991615081599585377 1807929743711311199689033)
          ·
            refine ⟨1355947307783483399766775, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1807929743711311199689033 1355947307783483399766775)
            ·
              refine ⟨2033920961675225099650163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1355947307783483399766775 2033920961675225099650163)
              ·
                refine ⟨3050881442512837649475245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2033920961675225099650163 3050881442512837649475245)
                ·
                  refine ⟨1144080540942314118553217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3050881442512837649475245 1144080540942314118553217)
                  ·
                    refine ⟨858060405706735588914913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1144080540942314118553217 858060405706735588914913)
                    ·
                      refine ⟨643545304280051691686185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858060405706735588914913 643545304280051691686185)
                      ·
                        rfl

theorem cell23_1253300_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 2, 1, 2, 2, 1, 1, 3, 2, 2].length) (baseStart_1253300 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253300 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253300 prefixEnd_1253300 := by exact prefixLift 1253300
  have htrace : WordTrace (prefixWord ++ tailWord_1253300) baseStart_1253300 baseEnd_1253300 := by
    simpa [prefixWord, tailWord_1253300, baseEnd_1253300] using wordTrace_append hprefix tailTrace_1253300
  have hstable : (prefixWord ++ tailWord_1253300).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253300).length < 2 ^ (prefixWord ++ tailWord_1253300).sum := by decide
  have hdescent : baseEnd_1253300 < baseStart_1253300 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253300) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253305 : List Nat := [1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 4]
def baseStart_1253305 : Nat := 118140960795 + 1253305 * 2 ^ 59
def prefixEnd_1253305 : Nat := 4983230072969 + 3 ^ 40 * 1253305 * 2
def baseEnd_1253305 : Nat := 643547871683324172123661

theorem tailTrace_1253305 : CollatzResearch.WordTrace tailWord_1253305 prefixEnd_1253305 643547871683324172123661 := by
  unfold tailWord_1253305
  simp only [CollatzResearch.WordTrace]
  refine ⟨45711788724497507297921369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30474525816331671531947579 45711788724497507297921369)
  ·
    refine ⟨34283841543373130473441027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45711788724497507297921369 34283841543373130473441027)
    ·
      refine ⟨51425762315059695710161541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34283841543373130473441027 51425762315059695710161541)
      ·
        refine ⟨9642330434073692945655289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 51425762315059695710161541 9642330434073692945655289)
        ·
          refine ⟨7231747825555269709241467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 9642330434073692945655289 7231747825555269709241467)
          ·
            refine ⟨10847621738332904563862201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7231747825555269709241467 10847621738332904563862201)
            ·
              refine ⟨8135716303749678422896651, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10847621738332904563862201 8135716303749678422896651)
              ·
                refine ⟨12203574455624517634344977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8135716303749678422896651 12203574455624517634344977)
                ·
                  refine ⟨9152680841718388225758733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 12203574455624517634344977 9152680841718388225758733)
                  ·
                    refine ⟨3432255315644395584659525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9152680841718388225758733 3432255315644395584659525)
                    ·
                      refine ⟨643547871683324172123661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3432255315644395584659525 643547871683324172123661)
                      ·
                        rfl

theorem cell23_1253305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 3, 4].length) (baseStart_1253305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253305 prefixEnd_1253305 := by exact prefixLift 1253305
  have htrace : WordTrace (prefixWord ++ tailWord_1253305) baseStart_1253305 baseEnd_1253305 := by
    simpa [prefixWord, tailWord_1253305, baseEnd_1253305] using wordTrace_append hprefix tailTrace_1253305
  have hstable : (prefixWord ++ tailWord_1253305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253305).length < 2 ^ (prefixWord ++ tailWord_1253305).sum := by decide
  have hdescent : baseEnd_1253305 < baseStart_1253305 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253355 : List Nat := [1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 3]
def baseStart_1253355 : Nat := 118140960795 + 1253355 * 2 ^ 59
def prefixEnd_1253355 : Nat := 4983230072969 + 3 ^ 40 * 1253355 * 2
def baseEnd_1253355 : Nat := 643573545716048976498431

theorem tailTrace_1253355 : CollatzResearch.WordTrace tailWord_1253355 prefixEnd_1253355 643573545716048976498431 := by
  unfold tailWord_1253355
  simp only [CollatzResearch.WordTrace]
  refine ⟨45713612374316365837241519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30475741582877577224827679 45713612374316365837241519)
  ·
    refine ⟨68570418561474548755862279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45713612374316365837241519 68570418561474548755862279)
    ·
      refine ⟨102855627842211823133793419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68570418561474548755862279 102855627842211823133793419)
      ·
        refine ⟨154283441763317734700690129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102855627842211823133793419 154283441763317734700690129)
        ·
          refine ⟨115712581322488301025517597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 154283441763317734700690129 115712581322488301025517597)
          ·
            refine ⟨43392217995933112884569099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 115712581322488301025517597 43392217995933112884569099)
            ·
              refine ⟨65088326993899669326853649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43392217995933112884569099 65088326993899669326853649)
              ·
                refine ⟨48816245245424751995140237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65088326993899669326853649 48816245245424751995140237)
                ·
                  refine ⟨18306091967034281998177589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48816245245424751995140237 18306091967034281998177589)
                  ·
                    refine ⟨1716196121909463937329149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 18306091967034281998177589 1716196121909463937329149)
                    ·
                      refine ⟨643573545716048976498431, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1716196121909463937329149 643573545716048976498431)
                      ·
                        rfl

theorem cell23_1253355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 2, 3, 5, 3].length) (baseStart_1253355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253355 prefixEnd_1253355 := by exact prefixLift 1253355
  have htrace : WordTrace (prefixWord ++ tailWord_1253355) baseStart_1253355 baseEnd_1253355 := by
    simpa [prefixWord, tailWord_1253355, baseEnd_1253355] using wordTrace_append hprefix tailTrace_1253355
  have hstable : (prefixWord ++ tailWord_1253355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253355).length < 2 ^ (prefixWord ++ tailWord_1253355).sum := by decide
  have hdescent : baseEnd_1253355 < baseStart_1253355 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253372 : List Nat := [2, 2, 2, 1, 2, 2, 3, 1, 2, 3, 3]
def baseStart_1253372 : Nat := 118140960795 + 1253372 * 2 ^ 59
def prefixEnd_1253372 : Nat := 4983230072969 + 3 ^ 40 * 1253372 * 2
def baseEnd_1253372 : Nat := 643582274887175409985853

theorem tailTrace_1253372 : CollatzResearch.WordTrace tailWord_1253372 prefixEnd_1253372 643582274887175409985853 := by
  unfold tailWord_1253372
  simp only [CollatzResearch.WordTrace]
  refine ⟨22857116207627388870305185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30476154943503185160406913 22857116207627388870305185)
  ·
    refine ⟨17142837155720541652728889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22857116207627388870305185 17142837155720541652728889)
    ·
      refine ⟨12857127866790406239546667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 17142837155720541652728889 12857127866790406239546667)
      ·
        refine ⟨19285691800185609359320001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12857127866790406239546667 19285691800185609359320001)
        ·
          refine ⟨14464268850139207019490001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19285691800185609359320001 14464268850139207019490001)
          ·
            refine ⟨10848201637604405264617501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14464268850139207019490001 10848201637604405264617501)
            ·
              refine ⟨4068075614101651974231563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10848201637604405264617501 4068075614101651974231563)
              ·
                refine ⟨6102113421152477961347345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068075614101651974231563 6102113421152477961347345)
                ·
                  refine ⟨4576585065864358471010509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102113421152477961347345 4576585065864358471010509)
                  ·
                    refine ⟨1716219399699134426628941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4576585065864358471010509 1716219399699134426628941)
                    ·
                      refine ⟨643582274887175409985853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1716219399699134426628941 643582274887175409985853)
                      ·
                        rfl

theorem cell23_1253372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 3, 1, 2, 3, 3].length) (baseStart_1253372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253372 prefixEnd_1253372 := by exact prefixLift 1253372
  have htrace : WordTrace (prefixWord ++ tailWord_1253372) baseStart_1253372 baseEnd_1253372 := by
    simpa [prefixWord, tailWord_1253372, baseEnd_1253372] using wordTrace_append hprefix tailTrace_1253372
  have hstable : (prefixWord ++ tailWord_1253372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253372).length < 2 ^ (prefixWord ++ tailWord_1253372).sum := by decide
  have hdescent : baseEnd_1253372 < baseStart_1253372 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253375 : List Nat := [1, 1, 2, 2, 1, 2, 1, 4, 4, 5]
def baseStart_1253375 : Nat := 118140960795 + 1253375 * 2 ^ 59
def prefixEnd_1253375 : Nat := 4983230072969 + 3 ^ 40 * 1253375 * 2
def baseEnd_1253375 : Nat := 214527938443046299416113

theorem tailTrace_1253375 : CollatzResearch.WordTrace tailWord_1253375 prefixEnd_1253375 214527938443046299416113 := by
  unfold tailWord_1253375
  simp only [CollatzResearch.WordTrace]
  refine ⟨45714341834243909252969579, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30476227889495939501979719 45714341834243909252969579)
  ·
    refine ⟨68571512751365863879454369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45714341834243909252969579 68571512751365863879454369)
    ·
      refine ⟨51428634563524397909590777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68571512751365863879454369 51428634563524397909590777)
      ·
        refine ⟨38571475922643298432193083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51428634563524397909590777 38571475922643298432193083)
        ·
          refine ⟨57857213883964947648289625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38571475922643298432193083 57857213883964947648289625)
          ·
            refine ⟨43392910412973710736217219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 57857213883964947648289625 43392910412973710736217219)
            ·
              refine ⟨65089365619460566104325829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 43392910412973710736217219 65089365619460566104325829)
              ·
                refine ⟨12204256053648856144561093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 65089365619460566104325829 12204256053648856144561093)
                ·
                  refine ⟨2288298010059160527105205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12204256053648856144561093 2288298010059160527105205)
                  ·
                    refine ⟨214527938443046299416113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2288298010059160527105205 214527938443046299416113)
                    ·
                      rfl

theorem cell23_1253375_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 4, 4, 5].length) (baseStart_1253375 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253375 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253375 prefixEnd_1253375 := by exact prefixLift 1253375
  have htrace : WordTrace (prefixWord ++ tailWord_1253375) baseStart_1253375 baseEnd_1253375 := by
    simpa [prefixWord, tailWord_1253375, baseEnd_1253375] using wordTrace_append hprefix tailTrace_1253375
  have hstable : (prefixWord ++ tailWord_1253375).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253375).length < 2 ^ (prefixWord ++ tailWord_1253375).sum := by decide
  have hdescent : baseEnd_1253375 < baseStart_1253375 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253375) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253429 : List Nat := [1, 3, 3, 1, 1, 1, 4, 1, 2, 4, 2]
def baseStart_1253429 : Nat := 118140960795 + 1253429 * 2 ^ 59
def prefixEnd_1253429 : Nat := 4983230072969 + 3 ^ 40 * 1253429 * 2
def baseEnd_1253429 : Nat := 643611543284481686973091

theorem tailTrace_1253429 : CollatzResearch.WordTrace tailWord_1253429 prefixEnd_1253429 643611543284481686973091 := by
  unfold tailWord_1253429
  simp only [CollatzResearch.WordTrace]
  refine ⟨45716311376048276475435341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30477540917365517650290227 45716311376048276475435341)
  ·
    refine ⟨17143616766018103678288253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45716311376048276475435341 17143616766018103678288253)
    ·
      refine ⟨6428856287256788879358095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17143616766018103678288253 6428856287256788879358095)
      ·
        refine ⟨9643284430885183319037143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6428856287256788879358095 9643284430885183319037143)
        ·
          refine ⟨14464926646327774978555715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9643284430885183319037143 14464926646327774978555715)
          ·
            refine ⟨21697389969491662467833573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14464926646327774978555715 21697389969491662467833573)
            ·
              refine ⟨4068260619279686712718795, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21697389969491662467833573 4068260619279686712718795)
              ·
                refine ⟨6102390928919530069078193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068260619279686712718795 6102390928919530069078193)
                ·
                  refine ⟨4576793196689647551808645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6102390928919530069078193 4576793196689647551808645)
                  ·
                    refine ⟨858148724379308915964121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 4576793196689647551808645 858148724379308915964121)
                    ·
                      refine ⟨643611543284481686973091, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858148724379308915964121 643611543284481686973091)
                      ·
                        rfl

theorem cell23_1253429_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 4, 1, 2, 4, 2].length) (baseStart_1253429 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253429 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253429 prefixEnd_1253429 := by exact prefixLift 1253429
  have htrace : WordTrace (prefixWord ++ tailWord_1253429) baseStart_1253429 baseEnd_1253429 := by
    simpa [prefixWord, tailWord_1253429, baseEnd_1253429] using wordTrace_append hprefix tailTrace_1253429
  have hstable : (prefixWord ++ tailWord_1253429).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253429).length < 2 ^ (prefixWord ++ tailWord_1253429).sum := by decide
  have hdescent : baseEnd_1253429 < baseStart_1253429 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253429) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253446 : List Nat := [6, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4]
def baseStart_1253446 : Nat := 118140960795 + 1253446 * 2 ^ 59
def prefixEnd_1253446 : Nat := 4983230072969 + 3 ^ 40 * 1253446 * 2
def baseEnd_1253446 : Nat := 643620272455608120460513

theorem tailTrace_1253446 : CollatzResearch.WordTrace tailWord_1253446 prefixEnd_1253446 643620272455608120460513 := by
  unfold tailWord_1253446
  simp only [CollatzResearch.WordTrace]
  refine ⟨1428654106780834011837631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30477954277991125585869461 1428654106780834011837631)
  ·
    refine ⟨2142981160171251017756447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1428654106780834011837631 2142981160171251017756447)
    ·
      refine ⟨3214471740256876526634671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2142981160171251017756447 3214471740256876526634671)
      ·
        refine ⟨4821707610385314789952007, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3214471740256876526634671 4821707610385314789952007)
        ·
          refine ⟨7232561415577972184928011, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4821707610385314789952007 7232561415577972184928011)
          ·
            refine ⟨10848842123366958277392017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7232561415577972184928011 10848842123366958277392017)
            ·
              refine ⟨8136631592525218708044013, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10848842123366958277392017 8136631592525218708044013)
              ·
                refine ⟨3051236847196957015516505, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8136631592525218708044013 3051236847196957015516505)
                ·
                  refine ⟨2288427635397717761637379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051236847196957015516505 2288427635397717761637379)
                  ·
                    refine ⟨3432641453096576642456069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2288427635397717761637379 3432641453096576642456069)
                    ·
                      refine ⟨643620272455608120460513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3432641453096576642456069 643620272455608120460513)
                      ·
                        rfl

theorem cell23_1253446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4].length) (baseStart_1253446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253446 prefixEnd_1253446 := by exact prefixLift 1253446
  have htrace : WordTrace (prefixWord ++ tailWord_1253446) baseStart_1253446 baseEnd_1253446 := by
    simpa [prefixWord, tailWord_1253446, baseEnd_1253446] using wordTrace_append hprefix tailTrace_1253446
  have hstable : (prefixWord ++ tailWord_1253446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253446).length < 2 ^ (prefixWord ++ tailWord_1253446).sum := by decide
  have hdescent : baseEnd_1253446 < baseStart_1253446 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253455 : List Nat := [1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 6]
def baseStart_1253455 : Nat := 118140960795 + 1253455 * 2 ^ 59
def prefixEnd_1253455 : Nat := 4983230072969 + 3 ^ 40 * 1253455 * 2
def baseEnd_1253455 : Nat := 643624893781498585247971

theorem tailTrace_1253455 : CollatzResearch.WordTrace tailWord_1253455 prefixEnd_1253455 643624893781498585247971 := by
  unfold tailWord_1253455
  simp only [CollatzResearch.WordTrace]
  refine ⟨45717259673954082915881819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30478173115969388610587879 45717259673954082915881819)
  ·
    refine ⟨68575889510931124373822729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45717259673954082915881819 68575889510931124373822729)
    ·
      refine ⟨51431917133198343280367047, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68575889510931124373822729 51431917133198343280367047)
      ·
        refine ⟨77147875699797514920550571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51431917133198343280367047 77147875699797514920550571)
        ·
          refine ⟨115721813549696272380825857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 77147875699797514920550571 115721813549696272380825857)
          ·
            refine ⟨86791360162272204285619393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 115721813549696272380825857 86791360162272204285619393)
            ·
              refine ⟨65093520121704153214214545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 86791360162272204285619393 65093520121704153214214545)
              ·
                refine ⟨48820140091278114910660909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 65093520121704153214214545 48820140091278114910660909)
                ·
                  refine ⟨18307552534229293091497841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 48820140091278114910660909 18307552534229293091497841)
                  ·
                    refine ⟨13730664400671969818623381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 18307552534229293091497841 13730664400671969818623381)
                    ·
                      refine ⟨643624893781498585247971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 13730664400671969818623381 643624893781498585247971)
                      ·
                        rfl

theorem cell23_1253455_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 2, 2, 3, 2, 6].length) (baseStart_1253455 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253455 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253455 prefixEnd_1253455 := by exact prefixLift 1253455
  have htrace : WordTrace (prefixWord ++ tailWord_1253455) baseStart_1253455 baseEnd_1253455 := by
    simpa [prefixWord, tailWord_1253455, baseEnd_1253455] using wordTrace_append hprefix tailTrace_1253455
  have hstable : (prefixWord ++ tailWord_1253455).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253455).length < 2 ^ (prefixWord ++ tailWord_1253455).sum := by decide
  have hdescent : baseEnd_1253455 < baseStart_1253455 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253455) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253469 : List Nat := [1, 4, 4, 1, 1, 1, 2, 1, 8]
def baseStart_1253469 : Nat := 118140960795 + 1253469 * 2 ^ 59
def prefixEnd_1253469 : Nat := 4983230072969 + 3 ^ 40 * 1253469 * 2
def baseEnd_1253469 : Nat := 71514675834517947830323

theorem tailTrace_1253469 : CollatzResearch.WordTrace tailWord_1253469 prefixEnd_1253469 71514675834517947830323 := by
  unfold tailWord_1253469
  simp only [CollatzResearch.WordTrace]
  refine ⟨45717770295903363306891461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30478513530602242204594307 45717770295903363306891461)
  ·
    refine ⟨8572081930481880620042149, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45717770295903363306891461 8572081930481880620042149)
    ·
      refine ⟨1607265361965352616257903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8572081930481880620042149 1607265361965352616257903)
      ·
        refine ⟨2410898042948028924386855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607265361965352616257903 2410898042948028924386855)
        ·
          refine ⟨3616347064422043386580283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2410898042948028924386855 3616347064422043386580283)
          ·
            refine ⟨5424520596633065079870425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3616347064422043386580283 5424520596633065079870425)
            ·
              refine ⟨4068390447474798809902819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5424520596633065079870425 4068390447474798809902819)
              ·
                refine ⟨6102585671212198214854229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4068390447474798809902819 6102585671212198214854229)
                ·
                  refine ⟨71514675834517947830323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6102585671212198214854229 71514675834517947830323)
                  ·
                    rfl

theorem cell23_1253469_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 1, 2, 1, 8].length) (baseStart_1253469 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253469 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253469 prefixEnd_1253469 := by exact prefixLift 1253469
  have htrace : WordTrace (prefixWord ++ tailWord_1253469) baseStart_1253469 baseEnd_1253469 := by
    simpa [prefixWord, tailWord_1253469, baseEnd_1253469] using wordTrace_append hprefix tailTrace_1253469
  have hstable : (prefixWord ++ tailWord_1253469).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253469).length < 2 ^ (prefixWord ++ tailWord_1253469).sum := by decide
  have hdescent : baseEnd_1253469 < baseStart_1253469 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253469) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253489 : List Nat := [1, 2, 2, 2, 1, 1, 3, 2, 4, 3, 2]
def baseStart_1253489 : Nat := 118140960795 + 1253489 * 2 ^ 59
def prefixEnd_1253489 : Nat := 4983230072969 + 3 ^ 40 * 1253489 * 2
def baseEnd_1253489 : Nat := 643642352123751452222815

theorem tailTrace_1253489 : CollatzResearch.WordTrace tailWord_1253489 prefixEnd_1253489 643642352123751452222815 := by
  unfold tailWord_1253489
  simp only [CollatzResearch.WordTrace]
  refine ⟨45718499755830906722619521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30478999837220604481746347 45718499755830906722619521)
  ·
    refine ⟨34288874816873180041964641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45718499755830906722619521 34288874816873180041964641)
    ·
      refine ⟨25716656112654885031473481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34288874816873180041964641 25716656112654885031473481)
      ·
        refine ⟨19287492084491163773605111, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25716656112654885031473481 19287492084491163773605111)
        ·
          refine ⟨28931238126736745660407667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 19287492084491163773605111 28931238126736745660407667)
          ·
            refine ⟨43396857190105118490611501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 28931238126736745660407667 43396857190105118490611501)
            ·
              refine ⟨16273821446289419433979313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 43396857190105118490611501 16273821446289419433979313)
              ·
                refine ⟨12205366084717064575484485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16273821446289419433979313 12205366084717064575484485)
                ·
                  refine ⟨2288506140884449607903341, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 12205366084717064575484485 2288506140884449607903341)
                  ·
                    refine ⟨858189802831668602963753, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288506140884449607903341 858189802831668602963753)
                    ·
                      refine ⟨643642352123751452222815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858189802831668602963753 643642352123751452222815)
                      ·
                        rfl

theorem cell23_1253489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 1, 3, 2, 4, 3, 2].length) (baseStart_1253489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253489 prefixEnd_1253489 := by exact prefixLift 1253489
  have htrace : WordTrace (prefixWord ++ tailWord_1253489) baseStart_1253489 baseEnd_1253489 := by
    simpa [prefixWord, tailWord_1253489, baseEnd_1253489] using wordTrace_append hprefix tailTrace_1253489
  have hstable : (prefixWord ++ tailWord_1253489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253489).length < 2 ^ (prefixWord ++ tailWord_1253489).sum := by decide
  have hdescent : baseEnd_1253489 < baseStart_1253489 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253524 : List Nat := [2, 4, 2, 3, 2, 1, 2, 2, 1, 4]
def baseStart_1253524 : Nat := 118140960795 + 1253524 * 2 ^ 59
def prefixEnd_1253524 : Nat := 4983230072969 + 3 ^ 40 * 1253524 * 2
def baseEnd_1253524 : Nat := 214553441315552938428385

theorem tailTrace_1253524 : CollatzResearch.WordTrace tailWord_1253524 prefixEnd_1253524 214553441315552938428385 := by
  unfold tailWord_1253524
  simp only [CollatzResearch.WordTrace]
  refine ⟨22859888155352053850071813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30479850873802738466762417 22859888155352053850071813)
  ·
    refine ⟨4286229029128510096888465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 22859888155352053850071813 4286229029128510096888465)
    ·
      refine ⟨3214671771846382572666349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4286229029128510096888465 3214671771846382572666349)
      ·
        refine ⟨1205501914442393464749881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3214671771846382572666349 1205501914442393464749881)
        ·
          refine ⟨904126435831795098562411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205501914442393464749881 904126435831795098562411)
          ·
            refine ⟨1356189653747692647843617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904126435831795098562411 1356189653747692647843617)
            ·
              refine ⟨1017142240310769485882713, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356189653747692647843617 1017142240310769485882713)
              ·
                refine ⟨762856680233077114412035, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1017142240310769485882713 762856680233077114412035)
                ·
                  refine ⟨1144285020349615671618053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762856680233077114412035 1144285020349615671618053)
                  ·
                    refine ⟨214553441315552938428385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1144285020349615671618053 214553441315552938428385)
                    ·
                      rfl

theorem cell23_1253524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 3, 2, 1, 2, 2, 1, 4].length) (baseStart_1253524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253524 prefixEnd_1253524 := by exact prefixLift 1253524
  have htrace : WordTrace (prefixWord ++ tailWord_1253524) baseStart_1253524 baseEnd_1253524 := by
    simpa [prefixWord, tailWord_1253524, baseEnd_1253524] using wordTrace_append hprefix tailTrace_1253524
  have hstable : (prefixWord ++ tailWord_1253524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253524).length < 2 ^ (prefixWord ++ tailWord_1253524).sum := by decide
  have hdescent : baseEnd_1253524 < baseStart_1253524 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253530 : List Nat := [3, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3]
def baseStart_1253530 : Nat := 118140960795 + 1253530 * 2 ^ 59
def prefixEnd_1253530 : Nat := 4983230072969 + 3 ^ 40 * 1253530 * 2
def baseEnd_1253530 : Nat := 643663404830585791810127

theorem tailTrace_1253530 : CollatzResearch.WordTrace tailWord_1253530 prefixEnd_1253530 643663404830585791810127 := by
  unfold tailWord_1253530
  simp only [CollatzResearch.WordTrace]
  refine ⟨11429998787170592681215511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30479996765788247149908029 11429998787170592681215511)
  ·
    refine ⟨17144998180755889021823267, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 11429998787170592681215511 17144998180755889021823267)
    ·
      refine ⟨25717497271133833532734901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17144998180755889021823267 25717497271133833532734901)
      ·
        refine ⟨2411015369168796893693897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 25717497271133833532734901 2411015369168796893693897)
        ·
          refine ⟨1808261526876597670270423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2411015369168796893693897 1808261526876597670270423)
          ·
            refine ⟨2712392290314896505405635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808261526876597670270423 2712392290314896505405635)
            ·
              refine ⟨4068588435472344758108453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712392290314896505405635 4068588435472344758108453)
              ·
                refine ⟨762860331651064642145335, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4068588435472344758108453 762860331651064642145335)
                ·
                  refine ⟨1144290497476596963218003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 762860331651064642145335 1144290497476596963218003)
                  ·
                    refine ⟨1716435746214895444827005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1144290497476596963218003 1716435746214895444827005)
                    ·
                      refine ⟨643663404830585791810127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1716435746214895444827005 643663404830585791810127)
                      ·
                        rfl

theorem cell23_1253530_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 2, 1, 1, 4, 1, 1, 3].length) (baseStart_1253530 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253530 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253530 prefixEnd_1253530 := by exact prefixLift 1253530
  have htrace : WordTrace (prefixWord ++ tailWord_1253530) baseStart_1253530 baseEnd_1253530 := by
    simpa [prefixWord, tailWord_1253530, baseEnd_1253530] using wordTrace_append hprefix tailTrace_1253530
  have hstable : (prefixWord ++ tailWord_1253530).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253530).length < 2 ^ (prefixWord ++ tailWord_1253530).sum := by decide
  have hdescent : baseEnd_1253530 < baseStart_1253530 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253530) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253557 : List Nat := [1, 3, 3, 4, 2, 1, 1, 1, 2, 3, 2]
def baseStart_1253557 : Nat := 118140960795 + 1253557 * 2 ^ 59
def prefixEnd_1253557 : Nat := 4983230072969 + 3 ^ 40 * 1253557 * 2
def baseEnd_1253557 : Nat := 643677268808257186172503

theorem tailTrace_1253557 : CollatzResearch.WordTrace tailWord_1253557 prefixEnd_1253557 643677268808257186172503 := by
  unfold tailWord_1253557
  simp only [CollatzResearch.WordTrace]
  refine ⟨45720979919584554336094925, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30480653279723036224063283 45720979919584554336094925)
  ·
    refine ⟨17145367469844207876035597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45720979919584554336094925 17145367469844207876035597)
    ·
      refine ⟨6429512801191577953513349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 17145367469844207876035597 6429512801191577953513349)
      ·
        refine ⟨1205533650223420866283753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6429512801191577953513349 1205533650223420866283753)
        ·
          refine ⟨904150237667565649712815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205533650223420866283753 904150237667565649712815)
          ·
            refine ⟨1356225356501348474569223, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904150237667565649712815 1356225356501348474569223)
            ·
              refine ⟨2034338034752022711853835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356225356501348474569223 2034338034752022711853835)
              ·
                refine ⟨3051507052128034067780753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034338034752022711853835 3051507052128034067780753)
                ·
                  refine ⟨2288630289096025550835565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051507052128034067780753 2288630289096025550835565)
                  ·
                    refine ⟨858236358411009581563337, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2288630289096025550835565 858236358411009581563337)
                    ·
                      refine ⟨643677268808257186172503, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858236358411009581563337 643677268808257186172503)
                      ·
                        rfl

theorem cell23_1253557_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 4, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_1253557 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253557 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253557 prefixEnd_1253557 := by exact prefixLift 1253557
  have htrace : WordTrace (prefixWord ++ tailWord_1253557) baseStart_1253557 baseEnd_1253557 := by
    simpa [prefixWord, tailWord_1253557, baseEnd_1253557] using wordTrace_append hprefix tailTrace_1253557
  have hstable : (prefixWord ++ tailWord_1253557).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253557).length < 2 ^ (prefixWord ++ tailWord_1253557).sum := by decide
  have hdescent : baseEnd_1253557 < baseStart_1253557 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253557) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253559 : List Nat := [1, 1, 3, 1, 4, 3, 3, 7]
def baseStart_1253559 : Nat := 118140960795 + 1253559 * 2 ^ 59
def prefixEnd_1253559 : Nat := 4983230072969 + 3 ^ 40 * 1253559 * 2
def baseEnd_1253559 : Nat := 23839936880354302901759

theorem tailTrace_1253559 : CollatzResearch.WordTrace tailWord_1253559 prefixEnd_1253559 23839936880354302901759 := by
  unfold tailWord_1253559
  simp only [CollatzResearch.WordTrace]
  refine ⟨45721052865577308677667731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30480701910384872451778487 45721052865577308677667731)
  ·
    refine ⟨68581579298365963016501597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45721052865577308677667731 68581579298365963016501597)
    ·
      refine ⟨25718092236887236131188099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68581579298365963016501597 25718092236887236131188099)
      ·
        refine ⟨38577138355330854196782149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25718092236887236131188099 38577138355330854196782149)
        ·
          refine ⟨7233213441624535161896653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 38577138355330854196782149 7233213441624535161896653)
          ·
            refine ⟨2712455040609200685711245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7233213441624535161896653 2712455040609200685711245)
            ·
              refine ⟨1017170640228450257141717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2712455040609200685711245 1017170640228450257141717)
              ·
                refine ⟨23839936880354302901759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1017170640228450257141717 23839936880354302901759)
                ·
                  rfl

theorem cell23_1253559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 3, 3, 7].length) (baseStart_1253559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253559 prefixEnd_1253559 := by exact prefixLift 1253559
  have htrace : WordTrace (prefixWord ++ tailWord_1253559) baseStart_1253559 baseEnd_1253559 := by
    simpa [prefixWord, tailWord_1253559, baseEnd_1253559] using wordTrace_append hprefix tailTrace_1253559
  have hstable : (prefixWord ++ tailWord_1253559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253559).length < 2 ^ (prefixWord ++ tailWord_1253559).sum := by decide
  have hdescent : baseEnd_1253559 < baseStart_1253559 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253570 : List Nat := [3, 5, 1, 1, 1, 2, 1, 3, 1, 1, 4]
def baseStart_1253570 : Nat := 118140960795 + 1253570 * 2 ^ 59
def prefixEnd_1253570 : Nat := 4983230072969 + 3 ^ 40 * 1253570 * 2
def baseEnd_1253570 : Nat := 643683944056765635309943

theorem tailTrace_1253570 : CollatzResearch.WordTrace tailWord_1253570 prefixEnd_1253570 643683944056765635309943 := by
  unfold tailWord_1253570
  simp only [CollatzResearch.WordTrace]
  refine ⟨11430363517134364389079541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 30480969379024971704212109 11430363517134364389079541)
  ·
    refine ⟨1071596579731346661476207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 11430363517134364389079541 1071596579731346661476207)
    ·
      refine ⟨1607394869597019992214311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071596579731346661476207 1607394869597019992214311)
      ·
        refine ⟨2411092304395529988321467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607394869597019992214311 2411092304395529988321467)
        ·
          refine ⟨3616638456593294982482201, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411092304395529988321467 3616638456593294982482201)
          ·
            refine ⟨2712478842444971236861651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3616638456593294982482201 2712478842444971236861651)
            ·
              refine ⟨4068718263667456855292477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712478842444971236861651 4068718263667456855292477)
              ·
                refine ⟨1525769348875296320734679, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4068718263667456855292477 1525769348875296320734679)
                ·
                  refine ⟨2288654023312944481102019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1525769348875296320734679 2288654023312944481102019)
                  ·
                    refine ⟨3432981034969416721653029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2288654023312944481102019 3432981034969416721653029)
                    ·
                      refine ⟨643683944056765635309943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3432981034969416721653029 643683944056765635309943)
                      ·
                        rfl

theorem cell23_1253570_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 1, 2, 1, 3, 1, 1, 4].length) (baseStart_1253570 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253570 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253570 prefixEnd_1253570 := by exact prefixLift 1253570
  have htrace : WordTrace (prefixWord ++ tailWord_1253570) baseStart_1253570 baseEnd_1253570 := by
    simpa [prefixWord, tailWord_1253570, baseEnd_1253570] using wordTrace_append hprefix tailTrace_1253570
  have hstable : (prefixWord ++ tailWord_1253570).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253570).length < 2 ^ (prefixWord ++ tailWord_1253570).sum := by decide
  have hdescent : baseEnd_1253570 < baseStart_1253570 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253570) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253580 : List Nat := [2, 2, 1, 6, 1, 2, 1, 2, 2, 4]
def baseStart_1253580 : Nat := 118140960795 + 1253580 * 2 ^ 59
def prefixEnd_1253580 : Nat := 4983230072969 + 3 ^ 40 * 1253580 * 2
def baseEnd_1253580 : Nat := 214563026287770198728299

theorem tailTrace_1253580 : CollatzResearch.WordTrace tailWord_1253580 prefixEnd_1253580 214563026287770198728299 := by
  unfold tailWord_1253580
  simp only [CollatzResearch.WordTrace]
  refine ⟨22860909399250614632091097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30481212532334152842788129 22860909399250614632091097)
  ·
    refine ⟨17145682049437960974068323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22860909399250614632091097 17145682049437960974068323)
    ·
      refine ⟨25718523074156941461102485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17145682049437960974068323 25718523074156941461102485)
      ·
        refine ⟨1205555769101106630989179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25718523074156941461102485 1205555769101106630989179)
        ·
          refine ⟨1808333653651659946483769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1205555769101106630989179 1808333653651659946483769)
          ·
            refine ⟨1356250240238744959862827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1808333653651659946483769 1356250240238744959862827)
            ·
              refine ⟨2034375360358117439794241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356250240238744959862827 2034375360358117439794241)
              ·
                refine ⟨1525781520268588079845681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2034375360358117439794241 1525781520268588079845681)
                ·
                  refine ⟨1144336140201441059884261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525781520268588079845681 1144336140201441059884261)
                  ·
                    refine ⟨214563026287770198728299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 1144336140201441059884261 214563026287770198728299)
                    ·
                      rfl

theorem cell23_1253580_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 6, 1, 2, 1, 2, 2, 4].length) (baseStart_1253580 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253580 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253580 prefixEnd_1253580 := by exact prefixLift 1253580
  have htrace : WordTrace (prefixWord ++ tailWord_1253580) baseStart_1253580 baseEnd_1253580 := by
    simpa [prefixWord, tailWord_1253580, baseEnd_1253580] using wordTrace_append hprefix tailTrace_1253580
  have hstable : (prefixWord ++ tailWord_1253580).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253580).length < 2 ^ (prefixWord ++ tailWord_1253580).sum := by decide
  have hdescent : baseEnd_1253580 < baseStart_1253580 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253580) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253632 : List Nat := [2, 1, 1, 2, 1, 1, 4, 2, 9]
def baseStart_1253632 : Nat := 118140960795 + 1253632 * 2 ^ 59
def prefixEnd_1253632 : Nat := 4983230072969 + 3 ^ 40 * 1253632 * 2
def baseEnd_1253632 : Nat := 71523975539704932526073

theorem tailTrace_1253632 : CollatzResearch.WordTrace tailWord_1253632 prefixEnd_1253632 71523975539704932526073 := by
  unfold tailWord_1253632
  simp only [CollatzResearch.WordTrace]
  refine ⟨22861857697156421072537575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30482476929541894763383433 22861857697156421072537575)
  ·
    refine ⟨34292786545734631608806363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22861857697156421072537575 34292786545734631608806363)
    ·
      refine ⟨51439179818601947413209545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34292786545734631608806363 51439179818601947413209545)
      ·
        refine ⟨38579384863951460559907159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 51439179818601947413209545 38579384863951460559907159)
        ·
          refine ⟨57869077295927190839860739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38579384863951460559907159 57869077295927190839860739)
          ·
            refine ⟨86803615943890786259791109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57869077295927190839860739 86803615943890786259791109)
            ·
              refine ⟨16275677989479522423710833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 86803615943890786259791109 16275677989479522423710833)
              ·
                refine ⟨12206758492109641817783125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 16275677989479522423710833 12206758492109641817783125)
                ·
                  refine ⟨71523975539704932526073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 12206758492109641817783125 71523975539704932526073)
                  ·
                    rfl

theorem cell23_1253632_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 2, 9].length) (baseStart_1253632 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253632 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253632 prefixEnd_1253632 := by exact prefixLift 1253632
  have htrace : WordTrace (prefixWord ++ tailWord_1253632) baseStart_1253632 baseEnd_1253632 := by
    simpa [prefixWord, tailWord_1253632, baseEnd_1253632] using wordTrace_append hprefix tailTrace_1253632
  have hstable : (prefixWord ++ tailWord_1253632).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253632).length < 2 ^ (prefixWord ++ tailWord_1253632).sum := by decide
  have hdescent : baseEnd_1253632 < baseStart_1253632 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253632) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253643 : List Nat := [1, 1, 1, 1, 5, 2, 2, 4, 2, 2, 2]
def baseStart_1253643 : Nat := 118140960795 + 1253643 * 2 ^ 59
def prefixEnd_1253643 : Nat := 4983230072969 + 3 ^ 40 * 1253643 * 2
def baseEnd_1253643 : Nat := 643721428144543849697107

theorem tailTrace_1253643 : CollatzResearch.WordTrace tailWord_1253643 prefixEnd_1253643 643721428144543849697107 := by
  unfold tailWord_1253643
  simp only [CollatzResearch.WordTrace]
  refine ⟨45724116597272991023725583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30482744398181994015817055 45724116597272991023725583)
  ·
    refine ⟨68586174895909486535588375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45724116597272991023725583 68586174895909486535588375)
    ·
      refine ⟨102879262343864229803382563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68586174895909486535588375 102879262343864229803382563)
      ·
        refine ⟨154318893515796344705073845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102879262343864229803382563 154318893515796344705073845)
        ·
          refine ⟨14467396267105907316100673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 154318893515796344705073845 14467396267105907316100673)
          ·
            refine ⟨10850547200329430487075505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14467396267105907316100673 10850547200329430487075505)
            ·
              refine ⟨8137910400247072865306629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10850547200329430487075505 8137910400247072865306629)
              ·
                refine ⟨1525858200046326162244993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8137910400247072865306629 1525858200046326162244993)
                ·
                  refine ⟨1144393650034744621683745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 1525858200046326162244993 1144393650034744621683745)
                  ·
                    refine ⟨858295237526058466262809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1144393650034744621683745 858295237526058466262809)
                    ·
                      refine ⟨643721428144543849697107, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858295237526058466262809 643721428144543849697107)
                      ·
                        rfl

theorem cell23_1253643_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 4, 2, 2, 2].length) (baseStart_1253643 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253643 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253643 prefixEnd_1253643 := by exact prefixLift 1253643
  have htrace : WordTrace (prefixWord ++ tailWord_1253643) baseStart_1253643 baseEnd_1253643 := by
    simpa [prefixWord, tailWord_1253643, baseEnd_1253643] using wordTrace_append hprefix tailTrace_1253643
  have hstable : (prefixWord ++ tailWord_1253643).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253643).length < 2 ^ (prefixWord ++ tailWord_1253643).sum := by decide
  have hdescent : baseEnd_1253643 < baseStart_1253643 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253643) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253649 : List Nat := [1, 2, 2, 1, 1, 5, 3, 1, 7]
def baseStart_1253649 : Nat := 118140960795 + 1253649 * 2 ^ 59
def prefixEnd_1253649 : Nat := 4983230072969 + 3 ^ 40 * 1253649 * 2
def baseEnd_1253649 : Nat := 71524945447607869580231

theorem tailTrace_1253649 : CollatzResearch.WordTrace tailWord_1253649 prefixEnd_1253649 71524945447607869580231 := by
  unfold tailWord_1253649
  simp only [CollatzResearch.WordTrace]
  refine ⟨45724335435251254048444001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30482890290167502698962667 45724335435251254048444001)
  ·
    refine ⟨34293251576438440536333001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45724335435251254048444001 34293251576438440536333001)
    ·
      refine ⟨25719938682328830402249751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34293251576438440536333001 25719938682328830402249751)
      ·
        refine ⟨38579908023493245603374627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 25719938682328830402249751 38579908023493245603374627)
        ·
          refine ⟨57869862035239868405061941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 38579908023493245603374627 57869862035239868405061941)
          ·
            refine ⟨5425299565803737662974557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 57869862035239868405061941 5425299565803737662974557)
            ·
              refine ⟨2034487337176401623615459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5425299565803737662974557 2034487337176401623615459)
              ·
                refine ⟨3051731005764602435423189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034487337176401623615459 3051731005764602435423189)
                ·
                  refine ⟨71524945447607869580231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3051731005764602435423189 71524945447607869580231)
                  ·
                    rfl

theorem cell23_1253649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 5, 3, 1, 7].length) (baseStart_1253649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253649 prefixEnd_1253649 := by exact prefixLift 1253649
  have htrace : WordTrace (prefixWord ++ tailWord_1253649) baseStart_1253649 baseEnd_1253649 := by
    simpa [prefixWord, tailWord_1253649, baseEnd_1253649] using wordTrace_append hprefix tailTrace_1253649
  have hstable : (prefixWord ++ tailWord_1253649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253649).length < 2 ^ (prefixWord ++ tailWord_1253649).sum := by decide
  have hdescent : baseEnd_1253649 < baseStart_1253649 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253659 : List Nat := [1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3]
def baseStart_1253659 : Nat := 118140960795 + 1253659 * 2 ^ 59
def prefixEnd_1253659 : Nat := 4983230072969 + 3 ^ 40 * 1253659 * 2
def baseEnd_1253659 : Nat := 643729643835015787097033

theorem tailTrace_1253659 : CollatzResearch.WordTrace tailWord_1253659 prefixEnd_1253659 643729643835015787097033 := by
  unfold tailWord_1253659
  simp only [CollatzResearch.WordTrace]
  refine ⟨45724700165215025756308031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30483133443476683837538687 45724700165215025756308031)
  ·
    refine ⟨68587050247822538634462047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45724700165215025756308031 68587050247822538634462047)
    ·
      refine ⟨102880575371733807951693071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 68587050247822538634462047 102880575371733807951693071)
      ·
        refine ⟨154320863057600711927539607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 102880575371733807951693071 154320863057600711927539607)
        ·
          refine ⟨231481294586401067891309411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 154320863057600711927539607 231481294586401067891309411)
          ·
            refine ⟨347221941879601601836964117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 231481294586401067891309411 347221941879601601836964117)
            ·
              refine ⟨16276028525606325086107693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 347221941879601601836964117 16276028525606325086107693)
              ·
                refine ⟨6103510697102371907290385, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 16276028525606325086107693 6103510697102371907290385)
                ·
                  refine ⟨4577633022826778930467789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 6103510697102371907290385 4577633022826778930467789)
                  ·
                    refine ⟨1716612383560042098925421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 4577633022826778930467789 1716612383560042098925421)
                    ·
                      refine ⟨643729643835015787097033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1716612383560042098925421 643729643835015787097033)
                      ·
                        rfl

theorem cell23_1253659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 6, 3, 2, 3, 3].length) (baseStart_1253659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253659 prefixEnd_1253659 := by exact prefixLift 1253659
  have htrace : WordTrace (prefixWord ++ tailWord_1253659) baseStart_1253659 baseEnd_1253659 := by
    simpa [prefixWord, tailWord_1253659, baseEnd_1253659] using wordTrace_append hprefix tailTrace_1253659
  have hstable : (prefixWord ++ tailWord_1253659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253659).length < 2 ^ (prefixWord ++ tailWord_1253659).sum := by decide
  have hdescent : baseEnd_1253659 < baseStart_1253659 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253679 : List Nat := [1, 1, 2, 1, 2, 1, 5, 3, 2, 5]
def baseStart_1253679 : Nat := 118140960795 + 1253679 * 2 ^ 59
def prefixEnd_1253679 : Nat := 4983230072969 + 3 ^ 40 * 1253679 * 2
def baseEnd_1253679 : Nat := 214579971149368569615647

theorem tailTrace_1253679 : CollatzResearch.WordTrace tailWord_1253679 prefixEnd_1253679 214579971149368569615647 := by
  unfold tailWord_1253679
  simp only [CollatzResearch.WordTrace]
  refine ⟨45725429625142569172036091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30483619750095046114690727 45725429625142569172036091)
  ·
    refine ⟨68588144437713853758054137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45725429625142569172036091 68588144437713853758054137)
    ·
      refine ⟨51441108328285390318540603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 68588144437713853758054137 51441108328285390318540603)
      ·
        refine ⟨77161662492428085477810905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51441108328285390318540603 77161662492428085477810905)
        ·
          refine ⟨57871246869321064108358179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77161662492428085477810905 57871246869321064108358179)
          ·
            refine ⟨86806870303981596162537269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 57871246869321064108358179 86806870303981596162537269)
            ·
              refine ⟨8138144090998274640237869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 86806870303981596162537269 8138144090998274640237869)
              ·
                refine ⟨3051804034124352990089201, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8138144090998274640237869 3051804034124352990089201)
                ·
                  refine ⟨2288853025593264742566901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051804034124352990089201 2288853025593264742566901)
                  ·
                    refine ⟨214579971149368569615647, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 2288853025593264742566901 214579971149368569615647)
                    ·
                      rfl

theorem cell23_1253679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 5, 3, 2, 5].length) (baseStart_1253679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253679 prefixEnd_1253679 := by exact prefixLift 1253679
  have htrace : WordTrace (prefixWord ++ tailWord_1253679) baseStart_1253679 baseEnd_1253679 := by
    simpa [prefixWord, tailWord_1253679, baseEnd_1253679] using wordTrace_append hprefix tailTrace_1253679
  have hstable : (prefixWord ++ tailWord_1253679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253679).length < 2 ^ (prefixWord ++ tailWord_1253679).sum := by decide
  have hdescent : baseEnd_1253679 < baseStart_1253679 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253700 : List Nat := [2, 3, 4, 1, 2, 1, 1, 4, 5]
def baseStart_1253700 : Nat := 118140960795 + 1253700 * 2 ^ 59
def prefixEnd_1253700 : Nat := 4983230072969 + 3 ^ 40 * 1253700 * 2
def baseEnd_1253700 : Nat := 71527855171316680742705

theorem tailTrace_1253700 : CollatzResearch.WordTrace tailWord_1253700 prefixEnd_1253700 71527855171316680742705 := by
  unfold tailWord_1253700
  simp only [CollatzResearch.WordTrace]
  refine ⟨22863097779033244879275277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30484130372044326505700369 22863097779033244879275277)
  ·
    refine ⟨8573661667137466829728229, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22863097779033244879275277 8573661667137466829728229)
    ·
      refine ⟨1607561562588275030574043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 8573661667137466829728229 1607561562588275030574043)
      ·
        refine ⟨2411342343882412545861065, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607561562588275030574043 2411342343882412545861065)
        ·
          refine ⟨1808506757911809409395799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2411342343882412545861065 1808506757911809409395799)
          ·
            refine ⟨2712760136867714114093699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1808506757911809409395799 2712760136867714114093699)
            ·
              refine ⟨4069140205301571171140549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2712760136867714114093699 4069140205301571171140549)
              ·
                refine ⟨762963788494044594588853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4069140205301571171140549 762963788494044594588853)
                ·
                  refine ⟨71527855171316680742705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 762963788494044594588853 71527855171316680742705)
                  ·
                    rfl

theorem cell23_1253700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 4, 1, 2, 1, 1, 4, 5].length) (baseStart_1253700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253700 prefixEnd_1253700 := by exact prefixLift 1253700
  have htrace : WordTrace (prefixWord ++ tailWord_1253700) baseStart_1253700 baseEnd_1253700 := by
    simpa [prefixWord, tailWord_1253700, baseEnd_1253700] using wordTrace_append hprefix tailTrace_1253700
  have hstable : (prefixWord ++ tailWord_1253700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253700).length < 2 ^ (prefixWord ++ tailWord_1253700).sum := by decide
  have hdescent : baseEnd_1253700 < baseStart_1253700 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253733 : List Nat := [1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 4]
def baseStart_1253733 : Nat := 118140960795 + 1253733 * 2 ^ 59
def prefixEnd_1253733 : Nat := 4983230072969 + 3 ^ 40 * 1253733 * 2
def baseEnd_1253733 : Nat := 643767641403448497571693

theorem tailTrace_1253733 : CollatzResearch.WordTrace tailWord_1253733 prefixEnd_1253733 643767641403448497571693 := by
  unfold tailWord_1253733
  simp only [CollatzResearch.WordTrace]
  refine ⟨45727399166946936394501853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30484932777964624263001235 45727399166946936394501853)
  ·
    refine ⟨17147774687605101147938195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 45727399166946936394501853 17147774687605101147938195)
    ·
      refine ⟨25721662031407651721907293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17147774687605101147938195 25721662031407651721907293)
      ·
        refine ⟨9645623261777869395715235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25721662031407651721907293 9645623261777869395715235)
        ·
          refine ⟨14468434892666804093572853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9645623261777869395715235 14468434892666804093572853)
          ·
            refine ⟨1356415771187512883772455, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 14468434892666804093572853 1356415771187512883772455)
            ·
              refine ⟨2034623656781269325658683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1356415771187512883772455 2034623656781269325658683)
              ·
                refine ⟨3051935485171903988488025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2034623656781269325658683 3051935485171903988488025)
                ·
                  refine ⟨2288951613878927991366019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3051935485171903988488025 2288951613878927991366019)
                  ·
                    refine ⟨3433427420818391987049029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2288951613878927991366019 3433427420818391987049029)
                    ·
                      refine ⟨643767641403448497571693, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3433427420818391987049029 643767641403448497571693)
                      ·
                        rfl

theorem cell23_1253733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 5, 1, 1, 2, 1, 4].length) (baseStart_1253733 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253733 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253733 prefixEnd_1253733 := by exact prefixLift 1253733
  have htrace : WordTrace (prefixWord ++ tailWord_1253733) baseStart_1253733 baseEnd_1253733 := by
    simpa [prefixWord, tailWord_1253733, baseEnd_1253733] using wordTrace_append hprefix tailTrace_1253733
  have hstable : (prefixWord ++ tailWord_1253733).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253733).length < 2 ^ (prefixWord ++ tailWord_1253733).sum := by decide
  have hdescent : baseEnd_1253733 < baseStart_1253733 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253783 : List Nat := [1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 3]
def baseStart_1253783 : Nat := 118140960795 + 1253783 * 2 ^ 59
def prefixEnd_1253783 : Nat := 4983230072969 + 3 ^ 40 * 1253783 * 2
def baseEnd_1253783 : Nat := 643793315436173301946463

theorem tailTrace_1253783 : CollatzResearch.WordTrace tailWord_1253783 prefixEnd_1253783 643793315436173301946463 := by
  unfold tailWord_1253783
  simp only [CollatzResearch.WordTrace]
  refine ⟨45729222816765794933822003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30486148544510529955881335 45729222816765794933822003)
  ·
    refine ⟨68593834225148692400733005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45729222816765794933822003 68593834225148692400733005)
    ·
      refine ⟨25722687834430759650274877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68593834225148692400733005 25722687834430759650274877)
      ·
        refine ⟨9646007937911534868853079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 25722687834430759650274877 9646007937911534868853079)
        ·
          refine ⟨14469011906867302303279619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9646007937911534868853079 14469011906867302303279619)
          ·
            refine ⟨21703517860300953454919429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14469011906867302303279619 21703517860300953454919429)
            ·
              refine ⟨4069409598806428772797393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 21703517860300953454919429 4069409598806428772797393)
              ·
                refine ⟨3052057199104821579598045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069409598806428772797393 3052057199104821579598045)
                ·
                  refine ⟨1144521449664308092349267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 3052057199104821579598045 1144521449664308092349267)
                  ·
                    refine ⟨1716782174496462138523901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 1144521449664308092349267 1716782174496462138523901)
                    ·
                      refine ⟨643793315436173301946463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1716782174496462138523901 643793315436173301946463)
                      ·
                        rfl

theorem cell23_1253783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 1, 4, 2, 3, 1, 3].length) (baseStart_1253783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253783 prefixEnd_1253783 := by exact prefixLift 1253783
  have htrace : WordTrace (prefixWord ++ tailWord_1253783) baseStart_1253783 baseEnd_1253783 := by
    simpa [prefixWord, tailWord_1253783, baseEnd_1253783] using wordTrace_append hprefix tailTrace_1253783
  have hstable : (prefixWord ++ tailWord_1253783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253783).length < 2 ^ (prefixWord ++ tailWord_1253783).sum := by decide
  have hdescent : baseEnd_1253783 < baseStart_1253783 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253853 : List Nat := [1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 4]
def baseStart_1253853 : Nat := 118140960795 + 1253853 * 2 ^ 59
def prefixEnd_1253853 : Nat := 4983230072969 + 3 ^ 40 * 1253853 * 2
def baseEnd_1253853 : Nat := 643829259081988028071141

theorem tailTrace_1253853 : CollatzResearch.WordTrace tailWord_1253853 prefixEnd_1253853 643829259081988028071141 := by
  unfold tailWord_1253853
  simp only [CollatzResearch.WordTrace]
  refine ⟨45731775926512196888870213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30487850617674797925913475 45731775926512196888870213)
  ·
    refine ⟨8574707986221036916663165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45731775926512196888870213 8574707986221036916663165)
    ·
      refine ⟨3215515494832888843748687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 8574707986221036916663165 3215515494832888843748687)
      ·
        refine ⟨4823273242249333265623031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3215515494832888843748687 4823273242249333265623031)
        ·
          refine ⟨7234909863373999898434547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823273242249333265623031 7234909863373999898434547)
          ·
            refine ⟨10852364795060999847651821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7234909863373999898434547 10852364795060999847651821)
            ·
              refine ⟨4069636798147874942869433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 10852364795060999847651821 4069636798147874942869433)
              ·
                refine ⟨3052227598610906207152075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069636798147874942869433 3052227598610906207152075)
                ·
                  refine ⟨4578341397916359310728113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3052227598610906207152075 4578341397916359310728113)
                  ·
                    refine ⟨3433756048437269483046085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 4578341397916359310728113 3433756048437269483046085)
                    ·
                      refine ⟨643829259081988028071141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3433756048437269483046085 643829259081988028071141)
                      ·
                        rfl

theorem cell23_1253853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 2, 4].length) (baseStart_1253853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253853 prefixEnd_1253853 := by exact prefixLift 1253853
  have htrace : WordTrace (prefixWord ++ tailWord_1253853) baseStart_1253853 baseEnd_1253853 := by
    simpa [prefixWord, tailWord_1253853, baseEnd_1253853] using wordTrace_append hprefix tailTrace_1253853
  have hstable : (prefixWord ++ tailWord_1253853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253853).length < 2 ^ (prefixWord ++ tailWord_1253853).sum := by decide
  have hdescent : baseEnd_1253853 < baseStart_1253853 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253857 : List Nat := [1, 2, 3, 1, 2, 2, 2, 5, 1, 2, 2]
def baseStart_1253857 : Nat := 118140960795 + 1253857 * 2 ^ 59
def prefixEnd_1253857 : Nat := 4983230072969 + 3 ^ 40 * 1253857 * 2
def baseEnd_1253857 : Nat := 643831313004606012421123

theorem tailTrace_1253857 : CollatzResearch.WordTrace tailWord_1253857 prefixEnd_1253857 643831313004606012421123 := by
  unfold tailWord_1253857
  simp only [CollatzResearch.WordTrace]
  refine ⟨45731921818497705572015825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30487947878998470381343883 45731921818497705572015825)
  ·
    refine ⟨34298941363873279179011869, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45731921818497705572015825 34298941363873279179011869)
    ·
      refine ⟨12862103011452479692129451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34298941363873279179011869 12862103011452479692129451)
      ·
        refine ⟨19293154517178719538194177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 12862103011452479692129451 19293154517178719538194177)
        ·
          refine ⟨14469865887884039653645633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 19293154517178719538194177 14469865887884039653645633)
          ·
            refine ⟨10852399415913029740234225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 14469865887884039653645633 10852399415913029740234225)
            ·
              refine ⟨8139299561934772305175669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 10852399415913029740234225 8139299561934772305175669)
              ·
                refine ⟨763059333931384903610219, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8139299561934772305175669 763059333931384903610219)
                ·
                  refine ⟨1144589000897077355415329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 763059333931384903610219 1144589000897077355415329)
                  ·
                    refine ⟨858441750672808016561497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 1144589000897077355415329 858441750672808016561497)
                    ·
                      refine ⟨643831313004606012421123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858441750672808016561497 643831313004606012421123)
                      ·
                        rfl

theorem cell23_1253857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 5, 1, 2, 2].length) (baseStart_1253857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253857 prefixEnd_1253857 := by exact prefixLift 1253857
  have htrace : WordTrace (prefixWord ++ tailWord_1253857) baseStart_1253857 baseEnd_1253857 := by
    simpa [prefixWord, tailWord_1253857, baseEnd_1253857] using wordTrace_append hprefix tailTrace_1253857
  have hstable : (prefixWord ++ tailWord_1253857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253857).length < 2 ^ (prefixWord ++ tailWord_1253857).sum := by decide
  have hdescent : baseEnd_1253857 < baseStart_1253857 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253894 : List Nat := [6, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3]
def baseStart_1253894 : Nat := 118140960795 + 1253894 * 2 ^ 59
def prefixEnd_1253894 : Nat := 4983230072969 + 3 ^ 40 * 1253894 * 2
def baseEnd_1253894 : Nat := 643850311788822367658453

theorem tailTrace_1253894 : CollatzResearch.WordTrace tailWord_1253894 prefixEnd_1253894 643850311788822367658453 := by
  unfold tailWord_1253894
  simp only [CollatzResearch.WordTrace]
  refine ⟨1429164728730114402847273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 30488847546242440594075157 1429164728730114402847273)
  ·
    refine ⟨1071873546547585802135455, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1429164728730114402847273 1071873546547585802135455)
    ·
      refine ⟨1607810319821378703203183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1071873546547585802135455 1607810319821378703203183)
      ·
        refine ⟨2411715479732068054804775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1607810319821378703203183 2411715479732068054804775)
        ·
          refine ⟨3617573219598102082207163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2411715479732068054804775 3617573219598102082207163)
          ·
            refine ⟨5426359829397153123310745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617573219598102082207163 5426359829397153123310745)
            ·
              refine ⟨4069769872047864842483059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426359829397153123310745 4069769872047864842483059)
              ·
                refine ⟨6104654808071797263724589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069769872047864842483059 6104654808071797263724589)
                ·
                  refine ⟨2289245553026923973896721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6104654808071797263724589 2289245553026923973896721)
                  ·
                    refine ⟨1716934164770192980422541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289245553026923973896721 1716934164770192980422541)
                    ·
                      refine ⟨643850311788822367658453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1716934164770192980422541 643850311788822367658453)
                      ·
                        rfl

theorem cell23_1253894_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 1, 2, 1, 3, 2, 3].length) (baseStart_1253894 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253894 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253894 prefixEnd_1253894 := by exact prefixLift 1253894
  have htrace : WordTrace (prefixWord ++ tailWord_1253894) baseStart_1253894 baseEnd_1253894 := by
    simpa [prefixWord, tailWord_1253894, baseEnd_1253894] using wordTrace_append hprefix tailTrace_1253894
  have hstable : (prefixWord ++ tailWord_1253894).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253894).length < 2 ^ (prefixWord ++ tailWord_1253894).sum := by decide
  have hdescent : baseEnd_1253894 < baseStart_1253894 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253894) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253896 : List Nat := [2, 1, 3, 2, 1, 1, 1, 1, 4, 3, 4]
def baseStart_1253896 : Nat := 118140960795 + 1253896 * 2 ^ 59
def prefixEnd_1253896 : Nat := 4983230072969 + 3 ^ 40 * 1253896 * 2
def baseEnd_1253896 : Nat := 643851338750131359833443

theorem tailTrace_1253896 : CollatzResearch.WordTrace tailWord_1253896 prefixEnd_1253896 643851338750131359833443 := by
  unfold tailWord_1253896
  simp only [CollatzResearch.WordTrace]
  refine ⟨22866672132678207616342771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30488896176904276821790361 22866672132678207616342771)
  ·
    refine ⟨34300008199017311424514157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22866672132678207616342771 34300008199017311424514157)
    ·
      refine ⟨12862503074631491784192809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 34300008199017311424514157 12862503074631491784192809)
      ·
        refine ⟨9646877305973618838144607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 12862503074631491784192809 9646877305973618838144607)
        ·
          refine ⟨14470315958960428257216911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 9646877305973618838144607 14470315958960428257216911)
          ·
            refine ⟨21705473938440642385825367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 14470315958960428257216911 21705473938440642385825367)
            ·
              refine ⟨32558210907660963578738051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 21705473938440642385825367 32558210907660963578738051)
              ·
                refine ⟨48837316361491445368107077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 32558210907660963578738051 48837316361491445368107077)
                ·
                  refine ⟨9156996817779646006520077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 48837316361491445368107077 9156996817779646006520077)
                  ·
                    refine ⟨3433873806667367252445029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 9156996817779646006520077 3433873806667367252445029)
                    ·
                      refine ⟨643851338750131359833443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3433873806667367252445029 643851338750131359833443)
                      ·
                        rfl

theorem cell23_1253896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 1, 1, 4, 3, 4].length) (baseStart_1253896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253896 prefixEnd_1253896 := by exact prefixLift 1253896
  have htrace : WordTrace (prefixWord ++ tailWord_1253896) baseStart_1253896 baseEnd_1253896 := by
    simpa [prefixWord, tailWord_1253896, baseEnd_1253896] using wordTrace_append hprefix tailTrace_1253896
  have hstable : (prefixWord ++ tailWord_1253896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253896).length < 2 ^ (prefixWord ++ tailWord_1253896).sum := by decide
  have hdescent : baseEnd_1253896 < baseStart_1253896 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253900 : List Nat := [2, 2, 1, 2, 4, 1, 2, 1, 3, 3, 2]
def baseStart_1253900 : Nat := 118140960795 + 1253900 * 2 ^ 59
def prefixEnd_1253900 : Nat := 4983230072969 + 3 ^ 40 * 1253900 * 2
def baseEnd_1253900 : Nat := 643853392672749344183425

theorem tailTrace_1253900 : CollatzResearch.WordTrace tailWord_1253900 prefixEnd_1253900 643853392672749344183425 := by
  unfold tailWord_1253900
  simp only [CollatzResearch.WordTrace]
  refine ⟨22866745078670961957915577, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30488993438227949277220769 22866745078670961957915577)
  ·
    refine ⟨17150058809003221468436683, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 22866745078670961957915577 17150058809003221468436683)
    ·
      refine ⟨25725088213504832202655025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 17150058809003221468436683 25725088213504832202655025)
      ·
        refine ⟨19293816160128624151991269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 25725088213504832202655025 19293816160128624151991269)
        ·
          refine ⟨3617590530024117028498363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 19293816160128624151991269 3617590530024117028498363)
          ·
            refine ⟨5426385795036175542747545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617590530024117028498363 5426385795036175542747545)
            ·
              refine ⟨4069789346277131657060659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426385795036175542747545 4069789346277131657060659)
              ·
                refine ⟨6104684019415697485590989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4069789346277131657060659 6104684019415697485590989)
                ·
                  refine ⟨2289256507280886557096621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 6104684019415697485590989 2289256507280886557096621)
                  ·
                    refine ⟨858471190230332458911233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289256507280886557096621 858471190230332458911233)
                    ·
                      refine ⟨643853392672749344183425, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858471190230332458911233 643853392672749344183425)
                      ·
                        rfl

theorem cell23_1253900_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 1, 2, 1, 3, 3, 2].length) (baseStart_1253900 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253900 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253900 prefixEnd_1253900 := by exact prefixLift 1253900
  have htrace : WordTrace (prefixWord ++ tailWord_1253900) baseStart_1253900 baseEnd_1253900 := by
    simpa [prefixWord, tailWord_1253900, baseEnd_1253900] using wordTrace_append hprefix tailTrace_1253900
  have hstable : (prefixWord ++ tailWord_1253900).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253900).length < 2 ^ (prefixWord ++ tailWord_1253900).sum := by decide
  have hdescent : baseEnd_1253900 < baseStart_1253900 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253900) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253911 : List Nat := [1, 1, 3, 6, 2, 1, 2, 1, 1, 2, 3]
def baseStart_1253911 : Nat := 118140960795 + 1253911 * 2 ^ 59
def prefixEnd_1253911 : Nat := 4983230072969 + 3 ^ 40 * 1253911 * 2
def baseEnd_1253911 : Nat := 643859040959948801145875

theorem tailTrace_1253911 : CollatzResearch.WordTrace tailWord_1253911 prefixEnd_1253911 643859040959948801145875 := by
  unfold tailWord_1253911
  simp only [CollatzResearch.WordTrace]
  refine ⟨45733891360302072794481587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30489260906868048529654391 45733891360302072794481587)
  ·
    refine ⟨68600837040453109191722381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 45733891360302072794481587 68600837040453109191722381)
    ·
      refine ⟨25725313890169915946895893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 68600837040453109191722381 25725313890169915946895893)
      ·
        refine ⟨1205874088601714810010745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 25725313890169915946895893 1205874088601714810010745)
        ·
          refine ⟨904405566451286107508059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1205874088601714810010745 904405566451286107508059)
          ·
            refine ⟨1356608349676929161262089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 904405566451286107508059 1356608349676929161262089)
            ·
              refine ⟨1017456262257696870946567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1356608349676929161262089 1017456262257696870946567)
              ·
                refine ⟨1526184393386545306419851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1017456262257696870946567 1526184393386545306419851)
                ·
                  refine ⟨2289276590079817959629777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526184393386545306419851 2289276590079817959629777)
                  ·
                    refine ⟨1716957442559863469722333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289276590079817959629777 1716957442559863469722333)
                    ·
                      refine ⟨643859040959948801145875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1716957442559863469722333 643859040959948801145875)
                      ·
                        rfl

theorem cell23_1253911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 6, 2, 1, 2, 1, 1, 2, 3].length) (baseStart_1253911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253911 prefixEnd_1253911 := by exact prefixLift 1253911
  have htrace : WordTrace (prefixWord ++ tailWord_1253911) baseStart_1253911 baseEnd_1253911 := by
    simpa [prefixWord, tailWord_1253911, baseEnd_1253911] using wordTrace_append hprefix tailTrace_1253911
  have hstable : (prefixWord ++ tailWord_1253911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253911).length < 2 ^ (prefixWord ++ tailWord_1253911).sum := by decide
  have hdescent : baseEnd_1253911 < baseStart_1253911 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253917 : List Nat := [1, 4, 2, 2, 1, 3, 1, 3, 1, 3, 2]
def baseStart_1253917 : Nat := 118140960795 + 1253917 * 2 ^ 59
def prefixEnd_1253917 : Nat := 4983230072969 + 3 ^ 40 * 1253917 * 2
def baseEnd_1253917 : Nat := 643862121843875777670847

theorem tailTrace_1253917 : CollatzResearch.WordTrace tailWord_1253917 prefixEnd_1253917 643862121843875777670847 := by
  unfold tailWord_1253917
  simp only [CollatzResearch.WordTrace]
  refine ⟨45734110198280335819200005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30489406798853557212800003 45734110198280335819200005)
  ·
    refine ⟨8575145662177562966100001, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 45734110198280335819200005 8575145662177562966100001)
    ·
      refine ⟨6431359246633172224575001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8575145662177562966100001 6431359246633172224575001)
      ·
        refine ⟨4823519434974879168431251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6431359246633172224575001 4823519434974879168431251)
        ·
          refine ⟨7235279152462318752646877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823519434974879168431251 7235279152462318752646877)
          ·
            refine ⟨2713229682173369532242579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7235279152462318752646877 2713229682173369532242579)
            ·
              refine ⟨4069844523260054298363869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2713229682173369532242579 4069844523260054298363869)
              ·
                refine ⟨1526191696222520361886451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4069844523260054298363869 1526191696222520361886451)
                ·
                  refine ⟨2289287544333780542829677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 1526191696222520361886451 2289287544333780542829677)
                  ·
                    refine ⟨858482829125167703561129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 2289287544333780542829677 858482829125167703561129)
                    ·
                      refine ⟨643862121843875777670847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 858482829125167703561129 643862121843875777670847)
                      ·
                        rfl

theorem cell23_1253917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 1, 3, 1, 3, 2].length) (baseStart_1253917 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253917 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253917 prefixEnd_1253917 := by exact prefixLift 1253917
  have htrace : WordTrace (prefixWord ++ tailWord_1253917) baseStart_1253917 baseEnd_1253917 := by
    simpa [prefixWord, tailWord_1253917, baseEnd_1253917] using wordTrace_append hprefix tailTrace_1253917
  have hstable : (prefixWord ++ tailWord_1253917).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253917).length < 2 ^ (prefixWord ++ tailWord_1253917).sum := by decide
  have hdescent : baseEnd_1253917 < baseStart_1253917 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253936 : List Nat := [2, 1, 1, 1, 2, 3, 3, 3, 7]
def baseStart_1253936 : Nat := 118140960795 + 1253936 * 2 ^ 59
def prefixEnd_1253936 : Nat := 4983230072969 + 3 ^ 40 * 1253936 * 2
def baseEnd_1253936 : Nat := 71541319775145689259251

theorem tailTrace_1253936 : CollatzResearch.WordTrace tailWord_1253936 prefixEnd_1253936 71541319775145689259251 := by
  unfold tailWord_1253936
  simp only [CollatzResearch.WordTrace]
  refine ⟨22867401592605751032070831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30489868790141001376094441 22867401592605751032070831)
  ·
    refine ⟨34301102388908626548106247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22867401592605751032070831 34301102388908626548106247)
    ·
      refine ⟨51451653583362939822159371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 34301102388908626548106247 51451653583362939822159371)
      ·
        refine ⟨77177480375044409733239057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 51451653583362939822159371 77177480375044409733239057)
        ·
          refine ⟨57883110281283307299929293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 77177480375044409733239057 57883110281283307299929293)
          ·
            refine ⟨21706166355481240237473485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 57883110281283307299929293 21706166355481240237473485)
            ·
              refine ⟨8139812383305465089052557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 21706166355481240237473485 8139812383305465089052557)
              ·
                refine ⟨3052429643739549408394709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8139812383305465089052557 3052429643739549408394709)
                ·
                  refine ⟨71541319775145689259251, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3052429643739549408394709 71541319775145689259251)
                  ·
                    rfl

theorem cell23_1253936_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 3, 3, 7].length) (baseStart_1253936 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253936 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253936 prefixEnd_1253936 := by exact prefixLift 1253936
  have htrace : WordTrace (prefixWord ++ tailWord_1253936) baseStart_1253936 baseEnd_1253936 := by
    simpa [prefixWord, tailWord_1253936, baseEnd_1253936] using wordTrace_append hprefix tailTrace_1253936
  have hstable : (prefixWord ++ tailWord_1253936).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253936).length < 2 ^ (prefixWord ++ tailWord_1253936).sum := by decide
  have hdescent : baseEnd_1253936 < baseStart_1253936 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253936) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1253953 : List Nat := [1, 2, 5, 1, 1, 2, 2, 2, 7]
def baseStart_1253953 : Nat := 118140960795 + 1253953 * 2 ^ 59
def prefixEnd_1253953 : Nat := 4983230072969 + 3 ^ 40 * 1253953 * 2
def baseEnd_1253953 : Nat := 71542289683048626313409

theorem tailTrace_1253953 : CollatzResearch.WordTrace tailWord_1253953 prefixEnd_1253953 71542289683048626313409 := by
  unfold tailWord_1253953
  simp only [CollatzResearch.WordTrace]
  refine ⟨45735423226149913967510513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 30490282150766609311673675 45735423226149913967510513)
  ·
    refine ⟨34301567419612435475632885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 45735423226149913967510513 34301567419612435475632885)
    ·
      refine ⟨3215771945588665825840583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 34301567419612435475632885 3215771945588665825840583)
      ·
        refine ⟨4823657918382998738760875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3215771945588665825840583 4823657918382998738760875)
        ·
          refine ⟨7235486877574498108141313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823657918382998738760875 7235486877574498108141313)
          ·
            refine ⟨5426615158180873581105985, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7235486877574498108141313 5426615158180873581105985)
            ·
              refine ⟨4069961368635655185829489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5426615158180873581105985 4069961368635655185829489)
              ·
                refine ⟨3052471026476741389372117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4069961368635655185829489 3052471026476741389372117)
                ·
                  refine ⟨71542289683048626313409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3052471026476741389372117 71542289683048626313409)
                  ·
                    rfl

theorem cell23_1253953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 2, 2, 2, 7].length) (baseStart_1253953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1253953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1253953 prefixEnd_1253953 := by exact prefixLift 1253953
  have htrace : WordTrace (prefixWord ++ tailWord_1253953) baseStart_1253953 baseEnd_1253953 := by
    simpa [prefixWord, tailWord_1253953, baseEnd_1253953] using wordTrace_append hprefix tailTrace_1253953
  have hstable : (prefixWord ++ tailWord_1253953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1253953).length < 2 ^ (prefixWord ++ tailWord_1253953).sum := by decide
  have hdescent : baseEnd_1253953 < baseStart_1253953 := by decide
  rcases family_descends (prefixWord ++ tailWord_1253953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254020 : List Nat := [2, 3, 2, 1, 3, 1, 1, 3, 2, 1, 4]
def baseStart_1254020 : Nat := 118140960795 + 1254020 * 2 ^ 59
def prefixEnd_1254020 : Nat := 4983230072969 + 3 ^ 40 * 1254020 * 2
def baseEnd_1254020 : Nat := 643915010351288874682873

theorem tailTrace_1254020 : CollatzResearch.WordTrace tailWord_1254020 prefixEnd_1254020 643915010351288874682873 := by
  unfold tailWord_1254020
  simp only [CollatzResearch.WordTrace]
  refine ⟨22868933458453592205099757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30491911277938122940133009 22868933458453592205099757)
  ·
    refine ⟨8575850046920097076912409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 22868933458453592205099757 8575850046920097076912409)
    ·
      refine ⟨6431887535190072807684307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 8575850046920097076912409 6431887535190072807684307)
      ·
        refine ⟨9647831302785109211526461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6431887535190072807684307 9647831302785109211526461)
        ·
          refine ⟨3617936738544415954322423, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 9647831302785109211526461 3617936738544415954322423)
          ·
            refine ⟨5426905107816623931483635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3617936738544415954322423 5426905107816623931483635)
            ·
              refine ⟨8140357661724935897225453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5426905107816623931483635 8140357661724935897225453)
              ·
                refine ⟨3052634123146850961459545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8140357661724935897225453 3052634123146850961459545)
                ·
                  refine ⟨2289475592360138221094659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052634123146850961459545 2289475592360138221094659)
                  ·
                    refine ⟨3434213388540207331641989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 2289475592360138221094659 3434213388540207331641989)
                    ·
                      refine ⟨643915010351288874682873, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 3434213388540207331641989 643915010351288874682873)
                      ·
                        rfl

theorem cell23_1254020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 3, 1, 1, 3, 2, 1, 4].length) (baseStart_1254020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254020 prefixEnd_1254020 := by exact prefixLift 1254020
  have htrace : WordTrace (prefixWord ++ tailWord_1254020) baseStart_1254020 baseEnd_1254020 := by
    simpa [prefixWord, tailWord_1254020, baseEnd_1254020] using wordTrace_append hprefix tailTrace_1254020
  have hstable : (prefixWord ++ tailWord_1254020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254020).length < 2 ^ (prefixWord ++ tailWord_1254020).sum := by decide
  have hdescent : baseEnd_1254020 < baseStart_1254020 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_1254040 : List Nat := [2, 1, 2, 4, 1, 1, 1, 4, 2, 2, 3]
def baseStart_1254040 : Nat := 118140960795 + 1254040 * 2 ^ 59
def prefixEnd_1254040 : Nat := 4983230072969 + 3 ^ 40 * 1254040 * 2
def baseEnd_1254040 : Nat := 643925279964378796432781

theorem tailTrace_1254040 : CollatzResearch.WordTrace tailWord_1254040 prefixEnd_1254040 643925279964378796432781 := by
  unfold tailWord_1254040
  simp only [CollatzResearch.WordTrace]
  refine ⟨22869298188417363912963787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 30492397584556485217285049 22869298188417363912963787)
  ·
    refine ⟨34303947282626045869445681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 22869298188417363912963787 34303947282626045869445681)
    ·
      refine ⟨25727960461969534402084261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 34303947282626045869445681 25727960461969534402084261)
      ·
        refine ⟨4823992586619287700390799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 25727960461969534402084261 4823992586619287700390799)
        ·
          refine ⟨7235988879928931550586199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 4823992586619287700390799 7235988879928931550586199)
          ·
            refine ⟨10853983319893397325879299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7235988879928931550586199 10853983319893397325879299)
            ·
              refine ⟨16280974979840095988818949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 10853983319893397325879299 16280974979840095988818949)
              ·
                refine ⟨3052682808720017997903553, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 16280974979840095988818949 3052682808720017997903553)
                ·
                  refine ⟨2289512106540013498427665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 3052682808720017997903553 2289512106540013498427665)
                  ·
                    refine ⟨1717134079905010123820749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 2289512106540013498427665 1717134079905010123820749)
                    ·
                      refine ⟨643925279964378796432781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 1717134079905010123820749 643925279964378796432781)
                      ·
                        rfl

theorem cell23_1254040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 1, 1, 1, 4, 2, 2, 3].length) (baseStart_1254040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_1254040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_1254040 prefixEnd_1254040 := by exact prefixLift 1254040
  have htrace : WordTrace (prefixWord ++ tailWord_1254040) baseStart_1254040 baseEnd_1254040 := by
    simpa [prefixWord, tailWord_1254040, baseEnd_1254040] using wordTrace_append hprefix tailTrace_1254040
  have hstable : (prefixWord ++ tailWord_1254040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_1254040).length < 2 ^ (prefixWord ++ tailWord_1254040).sum := by decide
  have hdescent : baseEnd_1254040 < baseStart_1254040 := by decide
  rcases family_descends (prefixWord ++ tailWord_1254040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
