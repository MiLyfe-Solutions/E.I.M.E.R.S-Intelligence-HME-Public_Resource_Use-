import V185TrunkScan23Chunk0565

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_3346569 : List Nat := [1, 2, 1, 1, 4, 2, 1, 2, 3, 6]
def baseStart_3346569 : Nat := 118140960795 + 3346569 * 2 ^ 59
def prefixEnd_3346569 : Nat := 4983230072969 + 3 ^ 40 * 3346569 * 2
def baseEnd_3346569 : Nat := 572799480145474089032305

theorem tailTrace_3346569 : CollatzResearch.WordTrace tailWord_3346569 prefixEnd_3346569 572799480145474089032305 := by
  unfold tailWord_3346569
  simp only [CollatzResearch.WordTrace]
  refine ⟨122059399012959536327010761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81372932675306357551340507 122059399012959536327010761)
  ·
    refine ⟨91544549259719652245258071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122059399012959536327010761 91544549259719652245258071)
    ·
      refine ⟨137316823889579478367887107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91544549259719652245258071 137316823889579478367887107)
      ·
        refine ⟨205975235834369217551830661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137316823889579478367887107 205975235834369217551830661)
        ·
          refine ⟨38620356718944228290968249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205975235834369217551830661 38620356718944228290968249)
          ·
            refine ⟨28965267539208171218226187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38620356718944228290968249 28965267539208171218226187)
            ·
              refine ⟨43447901308812256827339281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28965267539208171218226187 43447901308812256827339281)
              ·
                refine ⟨32585925981609192620504461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43447901308812256827339281 32585925981609192620504461)
                ·
                  refine ⟨12219722243103447232689173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32585925981609192620504461 12219722243103447232689173)
                  ·
                    refine ⟨572799480145474089032305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12219722243103447232689173 572799480145474089032305)
                    ·
                      rfl

theorem cell23_3346569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 2, 1, 2, 3, 6].length) (baseStart_3346569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346569 prefixEnd_3346569 := by exact prefixLift 3346569
  have htrace : WordTrace (prefixWord ++ tailWord_3346569) baseStart_3346569 baseEnd_3346569 := by
    simpa [prefixWord, tailWord_3346569, baseEnd_3346569] using wordTrace_append hprefix tailTrace_3346569
  have hstable : (prefixWord ++ tailWord_3346569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346569).length < 2 ^ (prefixWord ++ tailWord_3346569).sum := by decide
  have hdescent : baseEnd_3346569 < baseStart_3346569 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346579 : List Nat := [1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5]
def baseStart_3346579 : Nat := 118140960795 + 3346579 * 2 ^ 59
def prefixEnd_3346579 : Nat := 4983230072969 + 3 ^ 40 * 3346579 * 2
def baseEnd_3346579 : Nat := 1718403575242967227971869

theorem tailTrace_3346579 : CollatzResearch.WordTrace tailWord_3346579 prefixEnd_3346579 1718403575242967227971869 := by
  unfold tailWord_3346579
  simp only [CollatzResearch.WordTrace]
  refine ⟨122059763742923308034874791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81373175828615538689916527 122059763742923308034874791)
  ·
    refine ⟨183089645614384962052312187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122059763742923308034874791 183089645614384962052312187)
    ·
      refine ⟨274634468421577443078468281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183089645614384962052312187 274634468421577443078468281)
      ·
        refine ⟨205975851316183082308851211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274634468421577443078468281 205975851316183082308851211)
        ·
          refine ⟨308963776974274623463276817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205975851316183082308851211 308963776974274623463276817)
          ·
            refine ⟨231722832730705967597457613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 308963776974274623463276817 231722832730705967597457613)
            ·
              refine ⟨86896062274014737849046605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231722832730705967597457613 86896062274014737849046605)
              ·
                refine ⟨32586023352755526693392477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86896062274014737849046605 32586023352755526693392477)
                ·
                  refine ⟨12219758757283322510022179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32586023352755526693392477 12219758757283322510022179)
                  ·
                    refine ⟨18329638135924983765033269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12219758757283322510022179 18329638135924983765033269)
                    ·
                      refine ⟨1718403575242967227971869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18329638135924983765033269 1718403575242967227971869)
                      ·
                        rfl

theorem cell23_3346579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 3, 3, 3, 1, 5].length) (baseStart_3346579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346579 prefixEnd_3346579 := by exact prefixLift 3346579
  have htrace : WordTrace (prefixWord ++ tailWord_3346579) baseStart_3346579 baseEnd_3346579 := by
    simpa [prefixWord, tailWord_3346579, baseEnd_3346579] using wordTrace_append hprefix tailTrace_3346579
  have hstable : (prefixWord ++ tailWord_3346579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346579).length < 2 ^ (prefixWord ++ tailWord_3346579).sum := by decide
  have hdescent : baseEnd_3346579 < baseStart_3346579 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346629 : List Nat := [1, 3, 1, 1, 1, 1, 4, 1, 1, 9]
def baseStart_3346629 : Nat := 118140960795 + 3346629 * 2 ^ 59
def prefixEnd_3346629 : Nat := 4983230072969 + 3 ^ 40 * 3346629 * 2
def baseEnd_3346629 : Nat := 572809749758564010782213

theorem tailTrace_3346629 : CollatzResearch.WordTrace tailWord_3346629 prefixEnd_3346629 572809749758564010782213 := by
  unfold tailWord_3346629
  simp only [CollatzResearch.WordTrace]
  refine ⟨122061587392742166574194941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81374391595161444382796627 122061587392742166574194941)
  ·
    refine ⟨45773095272278312465323103, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122061587392742166574194941 45773095272278312465323103)
    ·
      refine ⟨68659642908417468697984655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45773095272278312465323103 68659642908417468697984655)
      ·
        refine ⟨102989464362626203046976983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68659642908417468697984655 102989464362626203046976983)
        ·
          refine ⟨154484196543939304570465475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102989464362626203046976983 154484196543939304570465475)
          ·
            refine ⟨231726294815908956855698213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154484196543939304570465475 231726294815908956855698213)
            ·
              refine ⟨43448680277982929410443415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 231726294815908956855698213 43448680277982929410443415)
              ·
                refine ⟨65173020416974394115665123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43448680277982929410443415 65173020416974394115665123)
                ·
                  refine ⟨97759530625461591173497685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65173020416974394115665123 97759530625461591173497685)
                  ·
                    refine ⟨572809749758564010782213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 97759530625461591173497685 572809749758564010782213)
                    ·
                      rfl

theorem cell23_3346629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 1, 1, 9].length) (baseStart_3346629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346629 prefixEnd_3346629 := by exact prefixLift 3346629
  have htrace : WordTrace (prefixWord ++ tailWord_3346629) baseStart_3346629 baseEnd_3346629 := by
    simpa [prefixWord, tailWord_3346629, baseEnd_3346629] using wordTrace_append hprefix tailTrace_3346629
  have hstable : (prefixWord ++ tailWord_3346629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346629).length < 2 ^ (prefixWord ++ tailWord_3346629).sum := by decide
  have hdescent : baseEnd_3346629 < baseStart_3346629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346717 : List Nat := [1, 4, 2, 3, 2, 1, 1, 2, 1, 4, 2]
def baseStart_3346717 : Nat := 118140960795 + 3346717 * 2 ^ 59
def prefixEnd_3346717 : Nat := 4983230072969 + 3 ^ 40 * 3346717 * 2
def baseEnd_3346717 : Nat := 1718474435573287688046235

theorem tailTrace_3346717 : CollatzResearch.WordTrace tailWord_3346717 prefixEnd_3346717 1718474435573287688046235 := by
  unfold tailWord_3346717
  simp only [CollatzResearch.WordTrace]
  refine ⟨122064797016423357603398405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81376531344282238402265603 122064797016423357603398405)
  ·
    refine ⟨22887149440579379550637201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122064797016423357603398405 22887149440579379550637201)
    ·
      refine ⟨17165362080434534662977901, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22887149440579379550637201 17165362080434534662977901)
      ·
        refine ⟨6437010780162950498616713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17165362080434534662977901 6437010780162950498616713)
        ·
          refine ⟨4827758085122212873962535, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6437010780162950498616713 4827758085122212873962535)
          ·
            refine ⟨7241637127683319310943803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4827758085122212873962535 7241637127683319310943803)
            ·
              refine ⟨10862455691524978966415705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241637127683319310943803 10862455691524978966415705)
              ·
                refine ⟨8146841768643734224811779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10862455691524978966415705 8146841768643734224811779)
                ·
                  refine ⟨12220262652965601337217669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8146841768643734224811779 12220262652965601337217669)
                  ·
                    refine ⟨2291299247431050250728313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12220262652965601337217669 2291299247431050250728313)
                    ·
                      refine ⟨1718474435573287688046235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291299247431050250728313 1718474435573287688046235)
                      ·
                        rfl

theorem cell23_3346717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 1, 1, 2, 1, 4, 2].length) (baseStart_3346717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346717 prefixEnd_3346717 := by exact prefixLift 3346717
  have htrace : WordTrace (prefixWord ++ tailWord_3346717) baseStart_3346717 baseEnd_3346717 := by
    simpa [prefixWord, tailWord_3346717, baseEnd_3346717] using wordTrace_append hprefix tailTrace_3346717
  have hstable : (prefixWord ++ tailWord_3346717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346717).length < 2 ^ (prefixWord ++ tailWord_3346717).sum := by decide
  have hdescent : baseEnd_3346717 < baseStart_3346717 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346723 : List Nat := [1, 1, 1, 4, 2, 2, 2, 5, 5]
def baseStart_3346723 : Nat := 118140960795 + 3346723 * 2 ^ 59
def prefixEnd_3346723 : Nat := 4983230072969 + 3 ^ 40 * 3346723 * 2
def baseEnd_3346723 : Nat := 190941946273023851619023

theorem tailTrace_3346723 : CollatzResearch.WordTrace tailWord_3346723 prefixEnd_3346723 190941946273023851619023 := by
  unfold tailWord_3346723
  simp only [CollatzResearch.WordTrace]
  refine ⟨122065015854401620628116823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81376677236267747085411215 122065015854401620628116823)
  ·
    refine ⟨183097523781602430942175235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122065015854401620628116823 183097523781602430942175235)
    ·
      refine ⟨274646285672403646413262853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183097523781602430942175235 274646285672403646413262853)
      ·
        refine ⟨51496178563575683702486785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274646285672403646413262853 51496178563575683702486785)
        ·
          refine ⟨38622133922681762776865089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51496178563575683702486785 38622133922681762776865089)
          ·
            refine ⟨28966600442011322082648817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38622133922681762776865089 28966600442011322082648817)
            ·
              refine ⟨21724950331508491561986613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28966600442011322082648817 21724950331508491561986613)
              ·
                refine ⟨2036714093578921083936245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21724950331508491561986613 2036714093578921083936245)
                ·
                  refine ⟨190941946273023851619023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2036714093578921083936245 190941946273023851619023)
                  ·
                    rfl

theorem cell23_3346723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 2, 5, 5].length) (baseStart_3346723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346723 prefixEnd_3346723 := by exact prefixLift 3346723
  have htrace : WordTrace (prefixWord ++ tailWord_3346723) baseStart_3346723 baseEnd_3346723 := by
    simpa [prefixWord, tailWord_3346723, baseEnd_3346723] using wordTrace_append hprefix tailTrace_3346723
  have hstable : (prefixWord ++ tailWord_3346723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346723).length < 2 ^ (prefixWord ++ tailWord_3346723).sum := by decide
  have hdescent : baseEnd_3346723 < baseStart_3346723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346736 : List Nat := [2, 1, 1, 1, 2, 2, 2, 3, 4, 5]
def baseStart_3346736 : Nat := 118140960795 + 3346736 * 2 ^ 59
def prefixEnd_3346736 : Nat := 4983230072969 + 3 ^ 40 * 3346736 * 2
def baseEnd_3346736 : Nat := 572828063901907704569549

theorem tailTrace_3346736 : CollatzResearch.WordTrace tailWord_3346736 prefixEnd_3346736 572828063901907704569549 := by
  unfold tailWord_3346736
  simp only [CollatzResearch.WordTrace]
  refine ⟨61032745001677261924170031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81376993335569682565560041 61032745001677261924170031)
  ·
    refine ⟨91549117502515892886255047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61032745001677261924170031 91549117502515892886255047)
    ·
      refine ⟨137323676253773839329382571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91549117502515892886255047 137323676253773839329382571)
      ·
        refine ⟨205985514380660758994073857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137323676253773839329382571 205985514380660758994073857)
        ·
          refine ⟨154489135785495569245555393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 205985514380660758994073857 154489135785495569245555393)
          ·
            refine ⟨115866851839121676934166545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154489135785495569245555393 115866851839121676934166545)
            ·
              refine ⟨86900138879341257700624909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115866851839121676934166545 86900138879341257700624909)
              ·
                refine ⟨32587552079752971637734341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86900138879341257700624909 32587552079752971637734341)
                ·
                  refine ⟨6110166014953682182075189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32587552079752971637734341 6110166014953682182075189)
                  ·
                    refine ⟨572828063901907704569549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6110166014953682182075189 572828063901907704569549)
                    ·
                      rfl

theorem cell23_3346736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 2, 3, 4, 5].length) (baseStart_3346736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346736 prefixEnd_3346736 := by exact prefixLift 3346736
  have htrace : WordTrace (prefixWord ++ tailWord_3346736) baseStart_3346736 baseEnd_3346736 := by
    simpa [prefixWord, tailWord_3346736, baseEnd_3346736] using wordTrace_append hprefix tailTrace_3346736
  have hstable : (prefixWord ++ tailWord_3346736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346736).length < 2 ^ (prefixWord ++ tailWord_3346736).sum := by decide
  have hdescent : baseEnd_3346736 < baseStart_3346736 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346750 : List Nat := [4, 2, 1, 2, 1, 3, 1, 1, 2, 3, 3]
def baseStart_3346750 : Nat := 118140960795 + 3346750 * 2 ^ 59
def prefixEnd_3346750 : Nat := 4983230072969 + 3 ^ 40 * 3346750 * 2
def baseEnd_3346750 : Nat := 1718491380434886058933583

theorem tailTrace_3346750 : CollatzResearch.WordTrace tailWord_3346750 prefixEnd_3346750 1718491380434886058933583 := by
  unfold tailWord_3346750
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258250078162975529918713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81377333750202536159566469 15258250078162975529918713)
  ·
    refine ⟨11443687558622231647439035, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15258250078162975529918713 11443687558622231647439035)
    ·
      refine ⟨17165531337933347471158553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11443687558622231647439035 17165531337933347471158553)
      ·
        refine ⟨12874148503450010603368915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17165531337933347471158553 12874148503450010603368915)
        ·
          refine ⟨19311222755175015905053373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12874148503450010603368915 19311222755175015905053373)
          ·
            refine ⟨7241708533190630964395015, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19311222755175015905053373 7241708533190630964395015)
            ·
              refine ⟨10862562799785946446592523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7241708533190630964395015 10862562799785946446592523)
              ·
                refine ⟨16293844199678919669888785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10862562799785946446592523 16293844199678919669888785)
                ·
                  refine ⟨12220383149759189752416589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16293844199678919669888785 12220383149759189752416589)
                  ·
                    refine ⟨4582643681159696157156221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12220383149759189752416589 4582643681159696157156221)
                    ·
                      refine ⟨1718491380434886058933583, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4582643681159696157156221 1718491380434886058933583)
                      ·
                        rfl

theorem cell23_3346750_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_3346750 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346750 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346750 prefixEnd_3346750 := by exact prefixLift 3346750
  have htrace : WordTrace (prefixWord ++ tailWord_3346750) baseStart_3346750 baseEnd_3346750 := by
    simpa [prefixWord, tailWord_3346750, baseEnd_3346750] using wordTrace_append hprefix tailTrace_3346750
  have hstable : (prefixWord ++ tailWord_3346750).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346750).length < 2 ^ (prefixWord ++ tailWord_3346750).sum := by decide
  have hdescent : baseEnd_3346750 < baseStart_3346750 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346750) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346766 : List Nat := [4, 1, 1, 1, 1, 1, 2, 1, 1, 10]
def baseStart_3346766 : Nat := 118140960795 + 3346766 * 2 ^ 59
def prefixEnd_3346766 : Nat := 4983230072969 + 3 ^ 40 * 3346766 * 2
def baseEnd_3346766 : Nat := 572833198708452665444503

theorem tailTrace_3346766 : CollatzResearch.WordTrace tailWord_3346766 prefixEnd_3346766 572833198708452665444503 := by
  unfold tailWord_3346766
  simp only [CollatzResearch.WordTrace]
  refine ⟨15258323024155729871491519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81377722795497225981288101 15258323024155729871491519)
  ·
    refine ⟨22887484536233594807237279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15258323024155729871491519 22887484536233594807237279)
    ·
      refine ⟨34331226804350392210855919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22887484536233594807237279 34331226804350392210855919)
      ·
        refine ⟨51496840206525588316283879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34331226804350392210855919 51496840206525588316283879)
        ·
          refine ⟨77245260309788382474425819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51496840206525588316283879 77245260309788382474425819)
          ·
            refine ⟨115867890464682573711638729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77245260309788382474425819 115867890464682573711638729)
            ·
              refine ⟨86900917848511930283729047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115867890464682573711638729 86900917848511930283729047)
              ·
                refine ⟨130351376772767895425593571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 86900917848511930283729047 130351376772767895425593571)
                ·
                  refine ⟨195527065159151843138390357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130351376772767895425593571 195527065159151843138390357)
                  ·
                    refine ⟨572833198708452665444503, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 195527065159151843138390357 572833198708452665444503)
                    ·
                      rfl

theorem cell23_3346766_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 2, 1, 1, 10].length) (baseStart_3346766 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346766 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346766 prefixEnd_3346766 := by exact prefixLift 3346766
  have htrace : WordTrace (prefixWord ++ tailWord_3346766) baseStart_3346766 baseEnd_3346766 := by
    simpa [prefixWord, tailWord_3346766, baseEnd_3346766] using wordTrace_append hprefix tailTrace_3346766
  have hstable : (prefixWord ++ tailWord_3346766).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346766).length < 2 ^ (prefixWord ++ tailWord_3346766).sum := by decide
  have hdescent : baseEnd_3346766 < baseStart_3346766 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346766) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346776 : List Nat := [2, 1, 2, 2, 1, 1, 2, 2, 2, 3, 5]
def baseStart_3346776 : Nat := 118140960795 + 3346776 * 2 ^ 59
def prefixEnd_3346776 : Nat := 4983230072969 + 3 ^ 40 * 3346776 * 2
def baseEnd_3346776 : Nat := 1718504730931902957208463

theorem tailTrace_3346776 : CollatzResearch.WordTrace tailWord_3346776 prefixEnd_3346776 1718504730931902957208463 := by
  unfold tailWord_3346776
  simp only [CollatzResearch.WordTrace]
  refine ⟨61033474461604805339898091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81377965948806407119864121 61033474461604805339898091)
  ·
    refine ⟨91550211692407208009847137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61033474461604805339898091 91550211692407208009847137)
    ·
      refine ⟨68662658769305406007385353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91550211692407208009847137 68662658769305406007385353)
      ·
        refine ⟨51496994076979054505539015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68662658769305406007385353 51496994076979054505539015)
        ·
          refine ⟨77245491115468581758308523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51496994076979054505539015 77245491115468581758308523)
          ·
            refine ⟨115868236673202872637462785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77245491115468581758308523 115868236673202872637462785)
            ·
              refine ⟨86901177504902154478097089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115868236673202872637462785 86901177504902154478097089)
              ·
                refine ⟨65175883128676615858572817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86901177504902154478097089 65175883128676615858572817)
                ·
                  refine ⟨48881912346507461893929613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65175883128676615858572817 48881912346507461893929613)
                  ·
                    refine ⟨18330717129940298210223605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48881912346507461893929613 18330717129940298210223605)
                    ·
                      refine ⟨1718504730931902957208463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18330717129940298210223605 1718504730931902957208463)
                      ·
                        rfl

theorem cell23_3346776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 2, 2, 3, 5].length) (baseStart_3346776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346776 prefixEnd_3346776 := by exact prefixLift 3346776
  have htrace : WordTrace (prefixWord ++ tailWord_3346776) baseStart_3346776 baseEnd_3346776 := by
    simpa [prefixWord, tailWord_3346776, baseEnd_3346776] using wordTrace_append hprefix tailTrace_3346776
  have hstable : (prefixWord ++ tailWord_3346776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346776).length < 2 ^ (prefixWord ++ tailWord_3346776).sum := by decide
  have hdescent : baseEnd_3346776 < baseStart_3346776 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346793 : List Nat := [1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 3]
def baseStart_3346793 : Nat := 118140960795 + 3346793 * 2 ^ 59
def prefixEnd_3346793 : Nat := 4983230072969 + 3 ^ 40 * 3346793 * 2
def baseEnd_3346793 : Nat := 1718513460103029390695885

theorem tailTrace_3346793 : CollatzResearch.WordTrace tailWord_3346793 prefixEnd_3346793 1718513460103029390695885 := by
  unfold tailWord_3346793
  simp only [CollatzResearch.WordTrace]
  refine ⟨122067568964148022583165033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81378379309432015055443355 122067568964148022583165033)
  ·
    refine ⟨91550676723111016937373775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122067568964148022583165033 91550676723111016937373775)
    ·
      refine ⟨137326015084666525406060663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91550676723111016937373775 137326015084666525406060663)
      ·
        refine ⟨205989022626999788109090995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137326015084666525406060663 205989022626999788109090995)
        ·
          refine ⟨308983533940499682163636493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205989022626999788109090995 308983533940499682163636493)
          ·
            refine ⟨115868825227687380811363685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 308983533940499682163636493 115868825227687380811363685)
            ·
              refine ⟨21725404730191383902130691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115868825227687380811363685 21725404730191383902130691)
              ·
                refine ⟨32588107095287075853196037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21725404730191383902130691 32588107095287075853196037)
                ·
                  refine ⟨6110270080366326722474257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32588107095287075853196037 6110270080366326722474257)
                  ·
                    refine ⟨4582702560274745041855693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6110270080366326722474257 4582702560274745041855693)
                    ·
                      refine ⟨1718513460103029390695885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4582702560274745041855693 1718513460103029390695885)
                      ·
                        rfl

theorem cell23_3346793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 4, 1, 4, 2, 3].length) (baseStart_3346793 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346793 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346793 prefixEnd_3346793 := by exact prefixLift 3346793
  have htrace : WordTrace (prefixWord ++ tailWord_3346793) baseStart_3346793 baseEnd_3346793 := by
    simpa [prefixWord, tailWord_3346793, baseEnd_3346793] using wordTrace_append hprefix tailTrace_3346793
  have hstable : (prefixWord ++ tailWord_3346793).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346793).length < 2 ^ (prefixWord ++ tailWord_3346793).sum := by decide
  have hdescent : baseEnd_3346793 < baseStart_3346793 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346800 : List Nat := [2, 1, 1, 1, 4, 4, 2, 1, 3, 4]
def baseStart_3346800 : Nat := 118140960795 + 3346800 * 2 ^ 59
def prefixEnd_3346800 : Nat := 4983230072969 + 3 ^ 40 * 3346800 * 2
def baseEnd_3346800 : Nat := 572839018155870287769451

theorem tailTrace_3346800 : CollatzResearch.WordTrace tailWord_3346800 prefixEnd_3346800 572839018155870287769451 := by
  unfold tailWord_3346800
  simp only [CollatzResearch.WordTrace]
  refine ⟨61033912137561331389334927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81378549516748441852446569 61033912137561331389334927)
  ·
    refine ⟨91550868206341997084002391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61033912137561331389334927 91550868206341997084002391)
    ·
      refine ⟨137326302309512995626003587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91550868206341997084002391 137326302309512995626003587)
      ·
        refine ⟨205989453464269493439005381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137326302309512995626003587 205989453464269493439005381)
        ·
          refine ⟨38623022524550530019813509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 205989453464269493439005381 38623022524550530019813509)
          ·
            refine ⟨7241816723353224378715033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38623022524550530019813509 7241816723353224378715033)
            ·
              refine ⟨5431362542514918284036275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7241816723353224378715033 5431362542514918284036275)
              ·
                refine ⟨8147043813772377426054413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5431362542514918284036275 8147043813772377426054413)
                ·
                  refine ⟨3055141430164641534770405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8147043813772377426054413 3055141430164641534770405)
                  ·
                    refine ⟨572839018155870287769451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3055141430164641534770405 572839018155870287769451)
                    ·
                      rfl

theorem cell23_3346800_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 4, 2, 1, 3, 4].length) (baseStart_3346800 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346800 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346800 prefixEnd_3346800 := by exact prefixLift 3346800
  have htrace : WordTrace (prefixWord ++ tailWord_3346800) baseStart_3346800 baseEnd_3346800 := by
    simpa [prefixWord, tailWord_3346800, baseEnd_3346800] using wordTrace_append hprefix tailTrace_3346800
  have hstable : (prefixWord ++ tailWord_3346800).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346800).length < 2 ^ (prefixWord ++ tailWord_3346800).sum := by decide
  have hdescent : baseEnd_3346800 < baseStart_3346800 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346800) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346823 : List Nat := [1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 3]
def baseStart_3346823 : Nat := 118140960795 + 3346823 * 2 ^ 59
def prefixEnd_3346823 : Nat := 4983230072969 + 3 ^ 40 * 3346823 * 2
def baseEnd_3346823 : Nat := 1718528864522664273320747

theorem tailTrace_3346823 : CollatzResearch.WordTrace tailWord_3346823 prefixEnd_3346823 1718528864522664273320747 := by
  unfold tailWord_3346823
  simp only [CollatzResearch.WordTrace]
  refine ⟨122068663154039337706757123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81379108769359558471171415 122068663154039337706757123)
  ·
    refine ⟨183102994731059006560135685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122068663154039337706757123 183102994731059006560135685)
    ·
      refine ⟨34331811512073563730025441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183102994731059006560135685 34331811512073563730025441)
      ·
        refine ⟨25748858634055172797519081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34331811512073563730025441 25748858634055172797519081)
        ·
          refine ⟨19311643975541379598139311, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25748858634055172797519081 19311643975541379598139311)
          ·
            refine ⟨28967465963312069397208967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19311643975541379598139311 28967465963312069397208967)
            ·
              refine ⟨43451198944968104095813451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28967465963312069397208967 43451198944968104095813451)
              ·
                refine ⟨65176798417452156143720177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43451198944968104095813451 65176798417452156143720177)
                ·
                  refine ⟨48882598813089117107790133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65176798417452156143720177 48882598813089117107790133)
                  ·
                    refine ⟨4582743638727104728855325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48882598813089117107790133 4582743638727104728855325)
                    ·
                      refine ⟨1718528864522664273320747, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4582743638727104728855325 1718528864522664273320747)
                      ·
                        rfl

theorem cell23_3346823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 1, 2, 5, 3].length) (baseStart_3346823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346823 prefixEnd_3346823 := by exact prefixLift 3346823
  have htrace : WordTrace (prefixWord ++ tailWord_3346823) baseStart_3346823 baseEnd_3346823 := by
    simpa [prefixWord, tailWord_3346823, baseEnd_3346823] using wordTrace_append hprefix tailTrace_3346823
  have hstable : (prefixWord ++ tailWord_3346823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346823).length < 2 ^ (prefixWord ++ tailWord_3346823).sum := by decide
  have hdescent : baseEnd_3346823 < baseStart_3346823 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346857 : List Nat := [1, 2, 1, 1, 1, 1, 3, 8, 1, 1, 3]
def baseStart_3346857 : Nat := 118140960795 + 3346857 * 2 ^ 59
def prefixEnd_3346857 : Nat := 4983230072969 + 3 ^ 40 * 3346857 * 2
def baseEnd_3346857 : Nat := 1718546322864917140295591

theorem tailTrace_3346857 : CollatzResearch.WordTrace tailWord_3346857 prefixEnd_3346857 1718546322864917140295591 := by
  unfold tailWord_3346857
  simp only [CollatzResearch.WordTrace]
  refine ⟨122069903235916161513494825, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81379935490610774342329883 122069903235916161513494825)
  ·
    refine ⟨91552427426937121135121119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122069903235916161513494825 91552427426937121135121119)
    ·
      refine ⟨137328641140405681702681679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91552427426937121135121119 137328641140405681702681679)
      ·
        refine ⟨205992961710608522554022519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137328641140405681702681679 205992961710608522554022519)
        ·
          refine ⟨308989442565912783831033779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205992961710608522554022519 308989442565912783831033779)
          ·
            refine ⟨463484163848869175746550669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 308989442565912783831033779 463484163848869175746550669)
            ·
              refine ⟨173806561443325940904956501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 463484163848869175746550669 173806561443325940904956501)
              ·
                refine ⟨2036795641913975869979959, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 173806561443325940904956501 2036795641913975869979959)
                ·
                  refine ⟨3055193462870963804969939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036795641913975869979959 3055193462870963804969939)
                  ·
                    refine ⟨4582790194306445707454909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3055193462870963804969939 4582790194306445707454909)
                    ·
                      refine ⟨1718546322864917140295591, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4582790194306445707454909 1718546322864917140295591)
                      ·
                        rfl

theorem cell23_3346857_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 8, 1, 1, 3].length) (baseStart_3346857 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346857 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346857 prefixEnd_3346857 := by exact prefixLift 3346857
  have htrace : WordTrace (prefixWord ++ tailWord_3346857) baseStart_3346857 baseEnd_3346857 := by
    simpa [prefixWord, tailWord_3346857, baseEnd_3346857] using wordTrace_append hprefix tailTrace_3346857
  have hstable : (prefixWord ++ tailWord_3346857).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346857).length < 2 ^ (prefixWord ++ tailWord_3346857).sum := by decide
  have hdescent : baseEnd_3346857 < baseStart_3346857 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346857) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346877 : List Nat := [1, 4, 1, 2, 2, 4, 1, 2, 1, 5]
def baseStart_3346877 : Nat := 118140960795 + 3346877 * 2 ^ 59
def prefixEnd_3346877 : Nat := 4983230072969 + 3 ^ 40 * 3346877 * 2
def baseEnd_3346877 : Nat := 572852197492669020681833

theorem tailTrace_3346877 : CollatzResearch.WordTrace tailWord_3346877 prefixEnd_3346877 572852197492669020681833 := by
  unfold tailWord_3346877
  simp only [CollatzResearch.WordTrace]
  refine ⟨122070632695843704929222885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81380421797229136619481923 122070632695843704929222885)
  ·
    refine ⟨22888243630470694674229291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122070632695843704929222885 22888243630470694674229291)
    ·
      refine ⟨34332365445706042011343937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22888243630470694674229291 34332365445706042011343937)
      ·
        refine ⟨25749274084279531508507953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34332365445706042011343937 25749274084279531508507953)
        ·
          refine ⟨19311955563209648631380965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25749274084279531508507953 19311955563209648631380965)
          ·
            refine ⟨3620991668101809118383931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19311955563209648631380965 3620991668101809118383931)
            ·
              refine ⟨5431487502152713677575897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3620991668101809118383931 5431487502152713677575897)
              ·
                refine ⟨4073615626614535258181923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5431487502152713677575897 4073615626614535258181923)
                ·
                  refine ⟨6110423439921802887272885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073615626614535258181923 6110423439921802887272885)
                  ·
                    refine ⟨572852197492669020681833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6110423439921802887272885 572852197492669020681833)
                    ·
                      rfl

theorem cell23_3346877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 4, 1, 2, 1, 5].length) (baseStart_3346877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346877 prefixEnd_3346877 := by exact prefixLift 3346877
  have htrace : WordTrace (prefixWord ++ tailWord_3346877) baseStart_3346877 baseEnd_3346877 := by
    simpa [prefixWord, tailWord_3346877, baseEnd_3346877] using wordTrace_append hprefix tailTrace_3346877
  have hstable : (prefixWord ++ tailWord_3346877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346877).length < 2 ^ (prefixWord ++ tailWord_3346877).sum := by decide
  have hdescent : baseEnd_3346877 < baseStart_3346877 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346920 : List Nat := [2, 1, 4, 1, 1, 5, 1, 8]
def baseStart_3346920 : Nat := 118140960795 + 3346920 * 2 ^ 59
def prefixEnd_3346920 : Nat := 4983230072969 + 3 ^ 40 * 3346920 * 2
def baseEnd_3346920 : Nat := 63651061931338903474363

theorem tailTrace_3346920 : CollatzResearch.WordTrace tailWord_3346920 prefixEnd_3346920 63651061931338903474363 := by
  unfold tailWord_3346920
  simp only [CollatzResearch.WordTrace]
  refine ⟨61036100517343961636519107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81381467356458615515358809 61036100517343961636519107)
  ·
    refine ⟨91554150776015942454778661, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61036100517343961636519107 91554150776015942454778661)
    ·
      refine ⟨17166403270502989210270999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91554150776015942454778661 17166403270502989210270999)
      ·
        refine ⟨25749604905754483815406499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17166403270502989210270999 25749604905754483815406499)
        ·
          refine ⟨38624407358631725723109749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25749604905754483815406499 38624407358631725723109749)
          ·
            refine ⟨3621038189871724286541539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 38624407358631725723109749 3621038189871724286541539)
            ·
              refine ⟨5431557284807586429812309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3621038189871724286541539 5431557284807586429812309)
              ·
                refine ⟨63651061931338903474363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 5431557284807586429812309 63651061931338903474363)
                ·
                  rfl

theorem cell23_3346920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 5, 1, 8].length) (baseStart_3346920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346920 prefixEnd_3346920 := by exact prefixLift 3346920
  have htrace : WordTrace (prefixWord ++ tailWord_3346920) baseStart_3346920 baseEnd_3346920 := by
    simpa [prefixWord, tailWord_3346920, baseEnd_3346920] using wordTrace_append hprefix tailTrace_3346920
  have hstable : (prefixWord ++ tailWord_3346920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346920).length < 2 ^ (prefixWord ++ tailWord_3346920).sum := by decide
  have hdescent : baseEnd_3346920 < baseStart_3346920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346943 : List Nat := [1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 5]
def baseStart_3346943 : Nat := 118140960795 + 3346943 * 2 ^ 59
def prefixEnd_3346943 : Nat := 4983230072969 + 3 ^ 40 * 3346943 * 2
def baseEnd_3346943 : Nat := 1718590482201203803820195

theorem tailTrace_3346943 : CollatzResearch.WordTrace tailWord_3346943 prefixEnd_3346943 1718590482201203803820195 := by
  unfold tailWord_3346943
  simp only [CollatzResearch.WordTrace]
  refine ⟨122073039913604598201125483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81382026609069732134083655 122073039913604598201125483)
  ·
    refine ⟨183109559870406897301688225, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122073039913604598201125483 183109559870406897301688225)
    ·
      refine ⟨137332169902805172976266169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183109559870406897301688225 137332169902805172976266169)
      ·
        refine ⟨102999127427103879732199627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137332169902805172976266169 102999127427103879732199627)
        ·
          refine ⟨154498691140655819598299441, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 102999127427103879732199627 154498691140655819598299441)
          ·
            refine ⟨115874018355491864698724581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154498691140655819598299441 115874018355491864698724581)
            ·
              refine ⟨21726378441654724631010859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115874018355491864698724581 21726378441654724631010859)
              ·
                refine ⟨32589567662482086946516289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21726378441654724631010859 32589567662482086946516289)
                ·
                  refine ⟨24442175746861565209887217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32589567662482086946516289 24442175746861565209887217)
                  ·
                    refine ⟨18331631810146173907415413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24442175746861565209887217 18331631810146173907415413)
                    ·
                      refine ⟨1718590482201203803820195, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18331631810146173907415413 1718590482201203803820195)
                      ·
                        rfl

theorem cell23_3346943_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 4, 1, 2, 2, 5].length) (baseStart_3346943 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346943 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346943 prefixEnd_3346943 := by exact prefixLift 3346943
  have htrace : WordTrace (prefixWord ++ tailWord_3346943) baseStart_3346943 baseEnd_3346943 := by
    simpa [prefixWord, tailWord_3346943, baseEnd_3346943] using wordTrace_append hprefix tailTrace_3346943
  have hstable : (prefixWord ++ tailWord_3346943).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346943).length < 2 ^ (prefixWord ++ tailWord_3346943).sum := by decide
  have hdescent : baseEnd_3346943 < baseStart_3346943 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346943) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346948 : List Nat := [2, 3, 2, 3, 1, 2, 2, 3, 1, 2, 2]
def baseStart_3346948 : Nat := 118140960795 + 3346948 * 2 ^ 59
def prefixEnd_3346948 : Nat := 4983230072969 + 3 ^ 40 * 3346948 * 2
def baseEnd_3346948 : Nat := 1718593049604476284257673

theorem tailTrace_3346948 : CollatzResearch.WordTrace tailWord_3346948 prefixEnd_3346948 1718593049604476284257673 := by
  unfold tailWord_3346948
  simp only [CollatzResearch.WordTrace]
  refine ⟨61036611139293242027528749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81382148185724322703371665 61036611139293242027528749)
  ·
    refine ⟨22888729177234965760323281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61036611139293242027528749 22888729177234965760323281)
    ·
      refine ⟨17166546882926224320242461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22888729177234965760323281 17166546882926224320242461)
      ·
        refine ⟨6437455081097334120090923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17166546882926224320242461 6437455081097334120090923)
        ·
          refine ⟨9656182621646001180136385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6437455081097334120090923 9656182621646001180136385)
          ·
            refine ⟨7242136966234500885102289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9656182621646001180136385 7242136966234500885102289)
            ·
              refine ⟨5431602724675875663826717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7242136966234500885102289 5431602724675875663826717)
              ·
                refine ⟨2036851021753453373935019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5431602724675875663826717 2036851021753453373935019)
                ·
                  refine ⟨3055276532630180060902529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2036851021753453373935019 3055276532630180060902529)
                  ·
                    refine ⟨2291457399472635045676897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3055276532630180060902529 2291457399472635045676897)
                    ·
                      refine ⟨1718593049604476284257673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291457399472635045676897 1718593049604476284257673)
                      ·
                        rfl

theorem cell23_3346948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 3, 1, 2, 2, 3, 1, 2, 2].length) (baseStart_3346948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346948 prefixEnd_3346948 := by exact prefixLift 3346948
  have htrace : WordTrace (prefixWord ++ tailWord_3346948) baseStart_3346948 baseEnd_3346948 := by
    simpa [prefixWord, tailWord_3346948, baseEnd_3346948] using wordTrace_append hprefix tailTrace_3346948
  have hstable : (prefixWord ++ tailWord_3346948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346948).length < 2 ^ (prefixWord ++ tailWord_3346948).sum := by decide
  have hdescent : baseEnd_3346948 < baseStart_3346948 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346951 : List Nat := [1, 1, 4, 3, 3, 2, 2, 1, 1, 2, 3]
def baseStart_3346951 : Nat := 118140960795 + 3346951 * 2 ^ 59
def prefixEnd_3346951 : Nat := 4983230072969 + 3 ^ 40 * 3346951 * 2
def baseEnd_3346951 : Nat := 1718594590046439772520159

theorem tailTrace_3346951 : CollatzResearch.WordTrace tailWord_3346951 prefixEnd_3346951 1718594590046439772520159 := by
  unfold tailWord_3346951
  simp only [CollatzResearch.WordTrace]
  refine ⟨122073331697575615567416707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81382221131717077044944471 122073331697575615567416707)
  ·
    refine ⟨183109997546363423351125061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122073331697575615567416707 183109997546363423351125061)
    ·
      refine ⟨34333124539943141878335949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183109997546363423351125061 34333124539943141878335949)
      ·
        refine ⟨12874921702478678204375981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34333124539943141878335949 12874921702478678204375981)
        ·
          refine ⟨4828095638429504326640993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12874921702478678204375981 4828095638429504326640993)
          ·
            refine ⟨3621071728822128244980745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4828095638429504326640993 3621071728822128244980745)
            ·
              refine ⟨2715803796616596183735559, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621071728822128244980745 2715803796616596183735559)
              ·
                refine ⟨4073705694924894275603339, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2715803796616596183735559 4073705694924894275603339)
                ·
                  refine ⟨6110558542387341413405009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4073705694924894275603339 6110558542387341413405009)
                  ·
                    refine ⟨4582918906790506060053757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6110558542387341413405009 4582918906790506060053757)
                    ·
                      refine ⟨1718594590046439772520159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4582918906790506060053757 1718594590046439772520159)
                      ·
                        rfl

theorem cell23_3346951_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 3, 2, 2, 1, 1, 2, 3].length) (baseStart_3346951 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346951 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346951 prefixEnd_3346951 := by exact prefixLift 3346951
  have htrace : WordTrace (prefixWord ++ tailWord_3346951) baseStart_3346951 baseEnd_3346951 := by
    simpa [prefixWord, tailWord_3346951, baseEnd_3346951] using wordTrace_append hprefix tailTrace_3346951
  have hstable : (prefixWord ++ tailWord_3346951).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346951).length < 2 ^ (prefixWord ++ tailWord_3346951).sum := by decide
  have hdescent : baseEnd_3346951 < baseStart_3346951 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346951) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346953 : List Nat := [1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 4]
def baseStart_3346953 : Nat := 118140960795 + 3346953 * 2 ^ 59
def prefixEnd_3346953 : Nat := 4983230072969 + 3 ^ 40 * 3346953 * 2
def baseEnd_3346953 : Nat := 1718595617007748764695149

theorem tailTrace_3346953 : CollatzResearch.WordTrace tailWord_3346953 prefixEnd_3346953 1718595617007748764695149 := by
  unfold tailWord_3346953
  simp only [CollatzResearch.WordTrace]
  refine ⟨122073404643568369908989513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81382269762378913272659675 122073404643568369908989513)
  ·
    refine ⟨91555053482676277431742135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122073404643568369908989513 91555053482676277431742135)
    ·
      refine ⟨137332580224014416147613203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91555053482676277431742135 137332580224014416147613203)
      ·
        refine ⟨205998870336021624221419805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137332580224014416147613203 205998870336021624221419805)
        ·
          refine ⟨77249576376008109083032427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 205998870336021624221419805 77249576376008109083032427)
          ·
            refine ⟨115874364564012163624548641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77249576376008109083032427 115874364564012163624548641)
            ·
              refine ⟨86905773423009122718411481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115874364564012163624548641 86905773423009122718411481)
              ·
                refine ⟨65179330067256842038808611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86905773423009122718411481 65179330067256842038808611)
                ·
                  refine ⟨97768995100885263058212917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 65179330067256842038808611 97768995100885263058212917)
                  ·
                    refine ⟨9165843290707993411707461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 97768995100885263058212917 9165843290707993411707461)
                    ·
                      refine ⟨1718595617007748764695149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9165843290707993411707461 1718595617007748764695149)
                      ·
                        rfl

theorem cell23_3346953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 2, 1, 5, 4].length) (baseStart_3346953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346953 prefixEnd_3346953 := by exact prefixLift 3346953
  have htrace : WordTrace (prefixWord ++ tailWord_3346953) baseStart_3346953 baseEnd_3346953 := by
    simpa [prefixWord, tailWord_3346953, baseEnd_3346953] using wordTrace_append hprefix tailTrace_3346953
  have hstable : (prefixWord ++ tailWord_3346953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346953).length < 2 ^ (prefixWord ++ tailWord_3346953).sum := by decide
  have hdescent : baseEnd_3346953 < baseStart_3346953 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3346963 : List Nat := [1, 1, 1, 2, 1, 5, 1, 1, 4, 6]
def baseStart_3346963 : Nat := 118140960795 + 3346963 * 2 ^ 59
def prefixEnd_3346963 : Nat := 4983230072969 + 3 ^ 40 * 3346963 * 2
def baseEnd_3346963 : Nat := 572866917271431241856701

theorem tailTrace_3346963 : CollatzResearch.WordTrace tailWord_3346963 prefixEnd_3346963 572866917271431241856701 := by
  unfold tailWord_3346963
  simp only [CollatzResearch.WordTrace]
  refine ⟨122073769373532141616853543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81382512915688094411235695 122073769373532141616853543)
  ·
    refine ⟨183110654060298212425280315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122073769373532141616853543 183110654060298212425280315)
    ·
      refine ⟨274665981090447318637920473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183110654060298212425280315 274665981090447318637920473)
      ·
        refine ⟨205999485817835488978440355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274665981090447318637920473 205999485817835488978440355)
        ·
          refine ⟨308999228726753233467660533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 205999485817835488978440355 308999228726753233467660533)
          ·
            refine ⟨28968677693133115637593175, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 308999228726753233467660533 28968677693133115637593175)
            ·
              refine ⟨43453016539699673456389763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28968677693133115637593175 43453016539699673456389763)
              ·
                refine ⟨65179524809549510184584645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43453016539699673456389763 65179524809549510184584645)
                ·
                  refine ⟨12221160901790533159609621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65179524809549510184584645 12221160901790533159609621)
                  ·
                    refine ⟨572866917271431241856701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12221160901790533159609621 572866917271431241856701)
                    ·
                      rfl

theorem cell23_3346963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 4, 6].length) (baseStart_3346963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3346963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3346963 prefixEnd_3346963 := by exact prefixLift 3346963
  have htrace : WordTrace (prefixWord ++ tailWord_3346963) baseStart_3346963 baseEnd_3346963 := by
    simpa [prefixWord, tailWord_3346963, baseEnd_3346963] using wordTrace_append hprefix tailTrace_3346963
  have hstable : (prefixWord ++ tailWord_3346963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3346963).length < 2 ^ (prefixWord ++ tailWord_3346963).sum := by decide
  have hdescent : baseEnd_3346963 < baseStart_3346963 := by decide
  rcases family_descends (prefixWord ++ tailWord_3346963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347004 : List Nat := [2, 2, 2, 2, 3, 1, 1, 2, 4, 2, 2]
def baseStart_3347004 : Nat := 118140960795 + 3347004 * 2 ^ 59
def prefixEnd_3347004 : Nat := 4983230072969 + 3 ^ 40 * 3347004 * 2
def baseEnd_3347004 : Nat := 1718621804521128065157415

theorem tailTrace_3347004 : CollatzResearch.WordTrace tailWord_3347004 prefixEnd_3347004 1718621804521128065157415 := by
  unfold tailWord_3347004
  simp only [CollatzResearch.WordTrace]
  refine ⟨61037632383191802809548033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81383509844255737079397377 61037632383191802809548033)
  ·
    refine ⟨45778224287393852107161025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61037632383191802809548033 45778224287393852107161025)
    ·
      refine ⟨34333668215545389080370769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45778224287393852107161025 34333668215545389080370769)
      ·
        refine ⟨25750251161659041810278077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34333668215545389080370769 25750251161659041810278077)
        ·
          refine ⟨9656344185622140678854279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25750251161659041810278077 9656344185622140678854279)
          ·
            refine ⟨14484516278433211018281419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9656344185622140678854279 14484516278433211018281419)
            ·
              refine ⟨21726774417649816527422129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14484516278433211018281419 21726774417649816527422129)
              ·
                refine ⟨16295080813237362395566597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21726774417649816527422129 16295080813237362395566597)
                ·
                  refine ⟨3055327652482005449168737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16295080813237362395566597 3055327652482005449168737)
                  ·
                    refine ⟨2291495739361504086876553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3055327652482005449168737 2291495739361504086876553)
                    ·
                      refine ⟨1718621804521128065157415, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291495739361504086876553 1718621804521128065157415)
                      ·
                        rfl

theorem cell23_3347004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 3, 1, 1, 2, 4, 2, 2].length) (baseStart_3347004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347004 prefixEnd_3347004 := by exact prefixLift 3347004
  have htrace : WordTrace (prefixWord ++ tailWord_3347004) baseStart_3347004 baseEnd_3347004 := by
    simpa [prefixWord, tailWord_3347004, baseEnd_3347004] using wordTrace_append hprefix tailTrace_3347004
  have hstable : (prefixWord ++ tailWord_3347004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347004).length < 2 ^ (prefixWord ++ tailWord_3347004).sum := by decide
  have hdescent : baseEnd_3347004 < baseStart_3347004 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347021 : List Nat := [1, 6, 1, 1, 2, 1, 2, 1, 4, 2, 2]
def baseStart_3347021 : Nat := 118140960795 + 3347021 * 2 ^ 59
def prefixEnd_3347021 : Nat := 4983230072969 + 3 ^ 40 * 3347021 * 2
def baseEnd_3347021 : Nat := 1718630533692254498644837

theorem tailTrace_3347021 : CollatzResearch.WordTrace tailWord_3347021 prefixEnd_3347021 1718630533692254498644837 := by
  unfold tailWord_3347021
  simp only [CollatzResearch.WordTrace]
  refine ⟨122075884807322017522464917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81383923204881345014976611 122075884807322017522464917)
  ·
    refine ⟨5722307100343219571365543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122075884807322017522464917 5722307100343219571365543)
    ·
      refine ⟨8583460650514829357048315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5722307100343219571365543 8583460650514829357048315)
      ·
        refine ⟨12875190975772244035572473, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8583460650514829357048315 12875190975772244035572473)
        ·
          refine ⟨9656393231829183026679355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12875190975772244035572473 9656393231829183026679355)
          ·
            refine ⟨14484589847743774540019033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9656393231829183026679355 14484589847743774540019033)
            ·
              refine ⟨10863442385807830905014275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14484589847743774540019033 10863442385807830905014275)
              ·
                refine ⟨16295163578711746357521413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10863442385807830905014275 16295163578711746357521413)
                ·
                  refine ⟨3055343171008452442035265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16295163578711746357521413 3055343171008452442035265)
                  ·
                    refine ⟨2291507378256339331526449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3055343171008452442035265 2291507378256339331526449)
                    ·
                      refine ⟨1718630533692254498644837, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291507378256339331526449 1718630533692254498644837)
                      ·
                        rfl

theorem cell23_3347021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 2, 1, 2, 1, 4, 2, 2].length) (baseStart_3347021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347021 prefixEnd_3347021 := by exact prefixLift 3347021
  have htrace : WordTrace (prefixWord ++ tailWord_3347021) baseStart_3347021 baseEnd_3347021 := by
    simpa [prefixWord, tailWord_3347021, baseEnd_3347021] using wordTrace_append hprefix tailTrace_3347021
  have hstable : (prefixWord ++ tailWord_3347021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347021).length < 2 ^ (prefixWord ++ tailWord_3347021).sum := by decide
  have hdescent : baseEnd_3347021 < baseStart_3347021 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347050 : List Nat := [3, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7]
def baseStart_3347050 : Nat := 118140960795 + 3347050 * 2 ^ 59
def prefixEnd_3347050 : Nat := 4983230072969 + 3 ^ 40 * 3347050 * 2
def baseEnd_3347050 : Nat := 1718645424631234885182203

theorem tailTrace_3347050 : CollatzResearch.WordTrace tailWord_3347050 prefixEnd_3347050 1718645424631234885182203 := by
  unfold tailWord_3347050
  simp only [CollatzResearch.WordTrace]
  refine ⟨30519235631054238868817651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81384628349477970316847069 30519235631054238868817651)
  ·
    refine ⟨45778853446581358303226477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30519235631054238868817651 45778853446581358303226477)
    ·
      refine ⟨17167070042468009363709929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45778853446581358303226477 17167070042468009363709929)
      ·
        refine ⟨12875302531851007022782447, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17167070042468009363709929 12875302531851007022782447)
        ·
          refine ⟨19312953797776510534173671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875302531851007022782447 19312953797776510534173671)
          ·
            refine ⟨28969430696664765801260507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19312953797776510534173671 28969430696664765801260507)
            ·
              refine ⟨43454146044997148701890761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28969430696664765801260507 43454146044997148701890761)
              ·
                refine ⟨32590609533747861526418071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43454146044997148701890761 32590609533747861526418071)
                ·
                  refine ⟨48885914300621792289627107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32590609533747861526418071 48885914300621792289627107)
                  ·
                    refine ⟨73328871450932688434440661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48885914300621792289627107 73328871450932688434440661)
                    ·
                      refine ⟨1718645424631234885182203, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73328871450932688434440661 1718645424631234885182203)
                      ·
                        rfl

theorem cell23_3347050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 1, 2, 1, 1, 7].length) (baseStart_3347050 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347050 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347050 prefixEnd_3347050 := by exact prefixLift 3347050
  have htrace : WordTrace (prefixWord ++ tailWord_3347050) baseStart_3347050 baseEnd_3347050 := by
    simpa [prefixWord, tailWord_3347050, baseEnd_3347050] using wordTrace_append hprefix tailTrace_3347050
  have hstable : (prefixWord ++ tailWord_3347050).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347050).length < 2 ^ (prefixWord ++ tailWord_3347050).sum := by decide
  have hdescent : baseEnd_3347050 < baseStart_3347050 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347077 : List Nat := [1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 4]
def baseStart_3347077 : Nat := 118140960795 + 3347077 * 2 ^ 59
def prefixEnd_3347077 : Nat := 4983230072969 + 3 ^ 40 * 3347077 * 2
def baseEnd_3347077 : Nat := 1718659288608906279544579

theorem tailTrace_3347077 : CollatzResearch.WordTrace tailWord_3347077 prefixEnd_3347077 1718659288608906279544579 := by
  unfold tailWord_3347077
  simp only [CollatzResearch.WordTrace]
  refine ⟨122077927295119139086503485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81385284863412759391002323 122077927295119139086503485)
  ·
    refine ⟨45779222735669677157438807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122077927295119139086503485 45779222735669677157438807)
    ·
      refine ⟨68668834103504515736158211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45779222735669677157438807 68668834103504515736158211)
      ·
        refine ⟨103003251155256773604237317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68668834103504515736158211 103003251155256773604237317)
        ·
          refine ⟨19313109591610645050794497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103003251155256773604237317 19313109591610645050794497)
          ·
            refine ⟨14484832193707983788095873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19313109591610645050794497 14484832193707983788095873)
            ·
              refine ⟨10863624145280987841071905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14484832193707983788095873 10863624145280987841071905)
              ·
                refine ⟨8147718108960740880803929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10863624145280987841071905 8147718108960740880803929)
                ·
                  refine ⟨6110788581720555660602947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8147718108960740880803929 6110788581720555660602947)
                  ·
                    refine ⟨9166182872580833490904421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6110788581720555660602947 9166182872580833490904421)
                    ·
                      refine ⟨1718659288608906279544579, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9166182872580833490904421 1718659288608906279544579)
                      ·
                        rfl

theorem cell23_3347077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 2, 2, 2, 2, 1, 4].length) (baseStart_3347077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347077 prefixEnd_3347077 := by exact prefixLift 3347077
  have htrace : WordTrace (prefixWord ++ tailWord_3347077) baseStart_3347077 baseEnd_3347077 := by
    simpa [prefixWord, tailWord_3347077, baseEnd_3347077] using wordTrace_append hprefix tailTrace_3347077
  have hstable : (prefixWord ++ tailWord_3347077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347077).length < 2 ^ (prefixWord ++ tailWord_3347077).sum := by decide
  have hdescent : baseEnd_3347077 < baseStart_3347077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347104 : List Nat := [2, 1, 1, 4, 4, 1, 1, 2, 3, 4]
def baseStart_3347104 : Nat := 118140960795 + 3347104 * 2 ^ 59
def prefixEnd_3347104 : Nat := 4983230072969 + 3 ^ 40 * 3347104 * 2
def baseEnd_3347104 : Nat := 572891050862192557968985

theorem tailTrace_3347104 : CollatzResearch.WordTrace tailWord_3347104 prefixEnd_3347104 572891050862192557968985 := by
  unfold tailWord_3347104
  simp only [CollatzResearch.WordTrace]
  refine ⟨61039456033010661348868183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81385941377347548465157577 61039456033010661348868183)
  ·
    refine ⟨91559184049515992023302275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61039456033010661348868183 91559184049515992023302275)
    ·
      refine ⟨137338776074273988034953413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91559184049515992023302275 137338776074273988034953413)
      ·
        refine ⟨25751020513926372756553765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137338776074273988034953413 25751020513926372756553765)
        ·
          refine ⟨4828316346361194891853831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25751020513926372756553765 4828316346361194891853831)
          ·
            refine ⟨7242474519541792337780747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828316346361194891853831 7242474519541792337780747)
            ·
              refine ⟨10863711779312688506671121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242474519541792337780747 10863711779312688506671121)
              ·
                refine ⟨8147783834484516380003341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10863711779312688506671121 8147783834484516380003341)
                ·
                  refine ⟨3055418937931693642501253, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8147783834484516380003341 3055418937931693642501253)
                  ·
                    refine ⟨572891050862192557968985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3055418937931693642501253 572891050862192557968985)
                    ·
                      rfl

theorem cell23_3347104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 4, 1, 1, 2, 3, 4].length) (baseStart_3347104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347104 prefixEnd_3347104 := by exact prefixLift 3347104
  have htrace : WordTrace (prefixWord ++ tailWord_3347104) baseStart_3347104 baseEnd_3347104 := by
    simpa [prefixWord, tailWord_3347104, baseEnd_3347104] using wordTrace_append hprefix tailTrace_3347104
  have hstable : (prefixWord ++ tailWord_3347104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347104).length < 2 ^ (prefixWord ++ tailWord_3347104).sum := by decide
  have hdescent : baseEnd_3347104 < baseStart_3347104 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347144 : List Nat := [2, 1, 3, 1, 2, 3, 1, 3, 3, 1, 3]
def baseStart_3347144 : Nat := 118140960795 + 3347144 * 2 ^ 59
def prefixEnd_3347144 : Nat := 4983230072969 + 3 ^ 40 * 3347144 * 2
def baseEnd_3347144 : Nat := 1718693691812757517406771

theorem tailTrace_3347144 : CollatzResearch.WordTrace tailWord_3347144 prefixEnd_3347144 1718693691812757517406771 := by
  unfold tailWord_3347144
  simp only [CollatzResearch.WordTrace]
  refine ⟨61040185492938204764596243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81386913990584273019461657 61040185492938204764596243)
  ·
    refine ⟨91560278239407307146894365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61040185492938204764596243 91560278239407307146894365)
    ·
      refine ⟨34335104339777740180085387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91560278239407307146894365 34335104339777740180085387)
      ·
        refine ⟨51502656509666610270128081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34335104339777740180085387 51502656509666610270128081)
        ·
          refine ⟨38626992382249957702596061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51502656509666610270128081 38626992382249957702596061)
          ·
            refine ⟨14485122143343734138473523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38626992382249957702596061 14485122143343734138473523)
            ·
              refine ⟨21727683215015601207710285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485122143343734138473523 21727683215015601207710285)
              ·
                refine ⟨8147881205630850452891357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21727683215015601207710285 8147881205630850452891357)
                ·
                  refine ⟨3055455452111568919834259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8147881205630850452891357 3055455452111568919834259)
                  ·
                    refine ⟨4583183178167353379751389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3055455452111568919834259 4583183178167353379751389)
                    ·
                      refine ⟨1718693691812757517406771, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583183178167353379751389 1718693691812757517406771)
                      ·
                        rfl

theorem cell23_3347144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 1, 3, 3, 1, 3].length) (baseStart_3347144 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347144 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347144 prefixEnd_3347144 := by exact prefixLift 3347144
  have htrace : WordTrace (prefixWord ++ tailWord_3347144) baseStart_3347144 baseEnd_3347144 := by
    simpa [prefixWord, tailWord_3347144, baseEnd_3347144] using wordTrace_append hprefix tailTrace_3347144
  have hstable : (prefixWord ++ tailWord_3347144).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347144).length < 2 ^ (prefixWord ++ tailWord_3347144).sum := by decide
  have hdescent : baseEnd_3347144 < baseStart_3347144 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347177 : List Nat := [1, 2, 1, 1, 1, 2, 5, 2, 4, 4]
def baseStart_3347177 : Nat := 118140960795 + 3347177 * 2 ^ 59
def prefixEnd_3347177 : Nat := 4983230072969 + 3 ^ 40 * 3347177 * 2
def baseEnd_3347177 : Nat := 572903545558118629431373

theorem tailTrace_3347177 : CollatzResearch.WordTrace tailWord_3347177 prefixEnd_3347177 572903545558118629431373 := by
  unfold tailWord_3347177
  simp only [CollatzResearch.WordTrace]
  refine ⟨122081574594756856165143785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81387716396504570776762523 122081574594756856165143785)
  ·
    refine ⟨91561180946067642123857839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122081574594756856165143785 91561180946067642123857839)
    ·
      refine ⟨137341771419101463185786759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91561180946067642123857839 137341771419101463185786759)
      ·
        refine ⟨206012657128652194778680139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137341771419101463185786759 206012657128652194778680139)
        ·
          refine ⟨309018985692978292168020209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206012657128652194778680139 309018985692978292168020209)
          ·
            refine ⟨231764239269733719126015157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309018985692978292168020209 231764239269733719126015157)
            ·
              refine ⟨21727897431537536168063921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231764239269733719126015157 21727897431537536168063921)
              ·
                refine ⟨16295923073653152126047941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21727897431537536168063921 16295923073653152126047941)
                ·
                  refine ⟨3055485576309966023633989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16295923073653152126047941 3055485576309966023633989)
                  ·
                    refine ⟨572903545558118629431373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3055485576309966023633989 572903545558118629431373)
                    ·
                      rfl

theorem cell23_3347177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 5, 2, 4, 4].length) (baseStart_3347177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347177 prefixEnd_3347177 := by exact prefixLift 3347177
  have htrace : WordTrace (prefixWord ++ tailWord_3347177) baseStart_3347177 baseEnd_3347177 := by
    simpa [prefixWord, tailWord_3347177, baseEnd_3347177] using wordTrace_append hprefix tailTrace_3347177
  have hstable : (prefixWord ++ tailWord_3347177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347177).length < 2 ^ (prefixWord ++ tailWord_3347177).sum := by decide
  have hdescent : baseEnd_3347177 < baseStart_3347177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347187 : List Nat := [1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 3]
def baseStart_3347187 : Nat := 118140960795 + 3347187 * 2 ^ 59
def prefixEnd_3347187 : Nat := 4983230072969 + 3 ^ 40 * 3347187 * 2
def baseEnd_3347187 : Nat := 1718715771480900849169073

theorem tailTrace_3347187 : CollatzResearch.WordTrace tailWord_3347187 prefixEnd_3347187 1718715771480900849169073 := by
  unfold tailWord_3347187
  simp only [CollatzResearch.WordTrace]
  refine ⟨122081939324720627873007815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81387959549813751915338543 122081939324720627873007815)
  ·
    refine ⟨183122908987080941809511723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122081939324720627873007815 183122908987080941809511723)
    ·
      refine ⟨274684363480621412714267585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183122908987080941809511723 274684363480621412714267585)
      ·
        refine ⟨206013272610466059535700689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274684363480621412714267585 206013272610466059535700689)
        ·
          refine ⟨154509954457849544651775517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206013272610466059535700689 154509954457849544651775517)
          ·
            refine ⟨57941232921693579244415819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154509954457849544651775517 57941232921693579244415819)
            ·
              refine ⟨86911849382540368866623729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57941232921693579244415819 86911849382540368866623729)
              ·
                refine ⟨65183887036905276649967797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86911849382540368866623729 65183887036905276649967797)
                ·
                  refine ⟨6110989409709869685934481, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65183887036905276649967797 6110989409709869685934481)
                  ·
                    refine ⟨4583242057282402264450861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6110989409709869685934481 4583242057282402264450861)
                    ·
                      refine ⟨1718715771480900849169073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583242057282402264450861 1718715771480900849169073)
                      ·
                        rfl

theorem cell23_3347187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 1, 2, 5, 2, 3].length) (baseStart_3347187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347187 prefixEnd_3347187 := by exact prefixLift 3347187
  have htrace : WordTrace (prefixWord ++ tailWord_3347187) baseStart_3347187 baseEnd_3347187 := by
    simpa [prefixWord, tailWord_3347187, baseEnd_3347187] using wordTrace_append hprefix tailTrace_3347187
  have hstable : (prefixWord ++ tailWord_3347187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347187).length < 2 ^ (prefixWord ++ tailWord_3347187).sum := by decide
  have hdescent : baseEnd_3347187 < baseStart_3347187 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347200 : List Nat := [2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7]
def baseStart_3347200 : Nat := 118140960795 + 3347200 * 2 ^ 59
def prefixEnd_3347200 : Nat := 4983230072969 + 3 ^ 40 * 3347200 * 2
def baseEnd_3347200 : Nat := 1718722446729409298306513

theorem tailTrace_3347200 : CollatzResearch.WordTrace tailWord_3347200 prefixEnd_3347200 1718722446729409298306513 := by
  unfold tailWord_3347200
  simp only [CollatzResearch.WordTrace]
  refine ⟨61041206736836765546615527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81388275649115687395487369 61041206736836765546615527)
  ·
    refine ⟨91561810105255148319923291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61041206736836765546615527 91561810105255148319923291)
    ·
      refine ⟨137342715157882722479884937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91561810105255148319923291 137342715157882722479884937)
      ·
        refine ⟨103007036368412041859913703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137342715157882722479884937 103007036368412041859913703)
        ·
          refine ⟨154510554552618062789870555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103007036368412041859913703 154510554552618062789870555)
          ·
            refine ⟨231765831828927094184805833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154510554552618062789870555 231765831828927094184805833)
            ·
              refine ⟨173824373871695320638604375, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231765831828927094184805833 173824373871695320638604375)
              ·
                refine ⟨260736560807542980957906563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173824373871695320638604375 260736560807542980957906563)
                ·
                  refine ⟨391104841211314471436859845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 260736560807542980957906563 391104841211314471436859845)
                  ·
                    refine ⟨73332157727121463394411221, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 391104841211314471436859845 73332157727121463394411221)
                    ·
                      refine ⟨1718722446729409298306513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73332157727121463394411221 1718722446729409298306513)
                      ·
                        rfl

theorem cell23_3347200_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 1, 1, 4, 7].length) (baseStart_3347200 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347200 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347200 prefixEnd_3347200 := by exact prefixLift 3347200
  have htrace : WordTrace (prefixWord ++ tailWord_3347200) baseStart_3347200 baseEnd_3347200 := by
    simpa [prefixWord, tailWord_3347200, baseEnd_3347200] using wordTrace_append hprefix tailTrace_3347200
  have hstable : (prefixWord ++ tailWord_3347200).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347200).length < 2 ^ (prefixWord ++ tailWord_3347200).sum := by decide
  have hdescent : baseEnd_3347200 < baseStart_3347200 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347200) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347204 : List Nat := [2, 3, 2, 2, 1, 1, 2, 2, 3, 2, 3]
def baseStart_3347204 : Nat := 118140960795 + 3347204 * 2 ^ 59
def prefixEnd_3347204 : Nat := 4983230072969 + 3 ^ 40 * 3347204 * 2
def baseEnd_3347204 : Nat := 1718724500652027282656495

theorem tailTrace_3347204 : CollatzResearch.WordTrace tailWord_3347204 prefixEnd_3347204 1718724500652027282656495 := by
  unfold tailWord_3347204
  simp only [CollatzResearch.WordTrace]
  refine ⟨61041279682829519888188333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81388372910439359850917777 61041279682829519888188333)
  ·
    refine ⟨22890479881061069958070625, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61041279682829519888188333 22890479881061069958070625)
    ·
      refine ⟨17167859910795802468552969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22890479881061069958070625 17167859910795802468552969)
      ·
        refine ⟨12875894933096851851414727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17167859910795802468552969 12875894933096851851414727)
        ·
          refine ⟨19313842399645277777122091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12875894933096851851414727 19313842399645277777122091)
          ·
            refine ⟨28970763599467916665683137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19313842399645277777122091 28970763599467916665683137)
            ·
              refine ⟨21728072699600937499262353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28970763599467916665683137 21728072699600937499262353)
              ·
                refine ⟨16296054524700703124446765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21728072699600937499262353 16296054524700703124446765)
                ·
                  refine ⟨6111020446762763671667537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16296054524700703124446765 6111020446762763671667537)
                  ·
                    refine ⟨4583265335072072753750653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6111020446762763671667537 4583265335072072753750653)
                    ·
                      refine ⟨1718724500652027282656495, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583265335072072753750653 1718724500652027282656495)
                      ·
                        rfl

theorem cell23_3347204_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 1, 2, 2, 3, 2, 3].length) (baseStart_3347204 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347204 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347204 prefixEnd_3347204 := by exact prefixLift 3347204
  have htrace : WordTrace (prefixWord ++ tailWord_3347204) baseStart_3347204 baseEnd_3347204 := by
    simpa [prefixWord, tailWord_3347204, baseEnd_3347204] using wordTrace_append hprefix tailTrace_3347204
  have hstable : (prefixWord ++ tailWord_3347204).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347204).length < 2 ^ (prefixWord ++ tailWord_3347204).sum := by decide
  have hdescent : baseEnd_3347204 < baseStart_3347204 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347204) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347207 : List Nat := [1, 1, 4, 4, 1, 1, 1, 10]
def baseStart_3347207 : Nat := 118140960795 + 3347207 * 2 ^ 59
def prefixEnd_3347207 : Nat := 4983230072969 + 3 ^ 40 * 3347207 * 2
def baseEnd_3347207 : Nat := 63656520040518176700703

theorem tailTrace_3347207 : CollatzResearch.WordTrace tailWord_3347207 prefixEnd_3347207 63656520040518176700703 := by
  unfold tailWord_3347207
  simp only [CollatzResearch.WordTrace]
  refine ⟨122082668784648171288735875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81388445856432114192490583 122082668784648171288735875)
  ·
    refine ⟨183124003176972256933103813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122082668784648171288735875 183124003176972256933103813)
    ·
      refine ⟨34335750595682298174956965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183124003176972256933103813 34335750595682298174956965)
      ·
        refine ⟨6437953236690430907804431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34335750595682298174956965 6437953236690430907804431)
        ·
          refine ⟨9656929855035646361706647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6437953236690430907804431 9656929855035646361706647)
          ·
            refine ⟨14485394782553469542559971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9656929855035646361706647 14485394782553469542559971)
            ·
              refine ⟨21728092173830204313839957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485394782553469542559971 21728092173830204313839957)
              ·
                refine ⟨63656520040518176700703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 21728092173830204313839957 63656520040518176700703)
                ·
                  rfl

theorem cell23_3347207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 1, 10].length) (baseStart_3347207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347207 prefixEnd_3347207 := by exact prefixLift 3347207
  have htrace : WordTrace (prefixWord ++ tailWord_3347207) baseStart_3347207 baseEnd_3347207 := by
    simpa [prefixWord, tailWord_3347207, baseEnd_3347207] using wordTrace_append hprefix tailTrace_3347207
  have hstable : (prefixWord ++ tailWord_3347207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347207).length < 2 ^ (prefixWord ++ tailWord_3347207).sum := by decide
  have hdescent : baseEnd_3347207 < baseStart_3347207 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347234 : List Nat := [3, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3]
def baseStart_3347234 : Nat := 118140960795 + 3347234 * 2 ^ 59
def prefixEnd_3347234 : Nat := 4983230072969 + 3 ^ 40 * 3347234 * 2
def baseEnd_3347234 : Nat := 1718739905071662165281357

theorem tailTrace_3347234 : CollatzResearch.WordTrace tailWord_3347234 prefixEnd_3347234 1718739905071662165281357 := by
  unfold tailWord_3347234
  simp only [CollatzResearch.WordTrace]
  refine ⟨30520913388887588724992189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81389102370366903266645837 30520913388887588724992189)
  ·
    refine ⟨11445342520832845771872071, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30520913388887588724992189 11445342520832845771872071)
    ·
      refine ⟨17168013781249268657808107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11445342520832845771872071 17168013781249268657808107)
      ·
        refine ⟨25752020671873902986712161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17168013781249268657808107 25752020671873902986712161)
        ·
          refine ⟨19314015503905427240034121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25752020671873902986712161 19314015503905427240034121)
          ·
            refine ⟨14485511627929070430025591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19314015503905427240034121 14485511627929070430025591)
            ·
              refine ⟨21728267441893605645038387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485511627929070430025591 21728267441893605645038387)
              ·
                refine ⟨32592401162840408467557581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21728267441893605645038387 32592401162840408467557581)
                ·
                  refine ⟨12222150436065153175334093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32592401162840408467557581 12222150436065153175334093)
                  ·
                    refine ⟨4583306413524432440750285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12222150436065153175334093 4583306413524432440750285)
                    ·
                      refine ⟨1718739905071662165281357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583306413524432440750285 1718739905071662165281357)
                      ·
                        rfl

theorem cell23_3347234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3].length) (baseStart_3347234 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347234 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347234 prefixEnd_3347234 := by exact prefixLift 3347234
  have htrace : WordTrace (prefixWord ++ tailWord_3347234) baseStart_3347234 baseEnd_3347234 := by
    simpa [prefixWord, tailWord_3347234, baseEnd_3347234] using wordTrace_append hprefix tailTrace_3347234
  have hstable : (prefixWord ++ tailWord_3347234).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347234).length < 2 ^ (prefixWord ++ tailWord_3347234).sum := by decide
  have hdescent : baseEnd_3347234 < baseStart_3347234 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347245 : List Nat := [1, 5, 3, 2, 1, 1, 2, 2, 2, 4]
def baseStart_3347245 : Nat := 118140960795 + 3347245 * 2 ^ 59
def prefixEnd_3347245 : Nat := 4983230072969 + 3 ^ 40 * 3347245 * 2
def baseEnd_3347245 : Nat := 572915184452953874081269

theorem tailTrace_3347245 : CollatzResearch.WordTrace tailWord_3347245 prefixEnd_3347245 572915184452953874081269 := by
  unfold tailWord_3347245
  simp only [CollatzResearch.WordTrace]
  refine ⟨122084054758510503778619189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81389369839007002519079459 122084054758510503778619189)
  ·
    refine ⟨11445380133610359729245549, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122084054758510503778619189 11445380133610359729245549)
    ·
      refine ⟨4292017550103884898467081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11445380133610359729245549 4292017550103884898467081)
      ·
        refine ⟨3219013162577913673850311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4292017550103884898467081 3219013162577913673850311)
        ·
          refine ⟨4828519743866870510775467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219013162577913673850311 4828519743866870510775467)
          ·
            refine ⟨7242779615800305766163201, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828519743866870510775467 7242779615800305766163201)
            ·
              refine ⟨5432084711850229324622401, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7242779615800305766163201 5432084711850229324622401)
              ·
                refine ⟨4074063533887671993466801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5432084711850229324622401 4074063533887671993466801)
                ·
                  refine ⟨3055547650415753995100101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074063533887671993466801 3055547650415753995100101)
                  ·
                    refine ⟨572915184452953874081269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3055547650415753995100101 572915184452953874081269)
                    ·
                      rfl

theorem cell23_3347245_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 2, 1, 1, 2, 2, 2, 4].length) (baseStart_3347245 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347245 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347245 prefixEnd_3347245 := by exact prefixLift 3347245
  have htrace : WordTrace (prefixWord ++ tailWord_3347245) baseStart_3347245 baseEnd_3347245 := by
    simpa [prefixWord, tailWord_3347245, baseEnd_3347245] using wordTrace_append hprefix tailTrace_3347245
  have hstable : (prefixWord ++ tailWord_3347245).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347245).length < 2 ^ (prefixWord ++ tailWord_3347245).sum := by decide
  have hdescent : baseEnd_3347245 < baseStart_3347245 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347245) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347251 : List Nat := [1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 3]
def baseStart_3347251 : Nat := 118140960795 + 3347251 * 2 ^ 59
def prefixEnd_3347251 : Nat := 4983230072969 + 3 ^ 40 * 3347251 * 2
def baseEnd_3347251 : Nat := 1718748634242788598768779

theorem tailTrace_3347251 : CollatzResearch.WordTrace tailWord_3347251 prefixEnd_3347251 1718748634242788598768779 := by
  unfold tailWord_3347251
  simp only [CollatzResearch.WordTrace]
  refine ⟨122084273596488766803337607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81389515730992511202225071 122084273596488766803337607)
  ·
    refine ⟨183126410394733150205006411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122084273596488766803337607 183126410394733150205006411)
    ·
      refine ⟨274689615592099725307509617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183126410394733150205006411 274689615592099725307509617)
      ·
        refine ⟨206017211694074793980632213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274689615592099725307509617 206017211694074793980632213)
        ·
          refine ⟨9657056798159755967842135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 206017211694074793980632213 9657056798159755967842135)
          ·
            refine ⟨14485585197239633951763203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9657056798159755967842135 14485585197239633951763203)
            ·
              refine ⟨21728377795859450927644805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485585197239633951763203 21728377795859450927644805)
              ·
                refine ⟨4074070836723647048933401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21728377795859450927644805 4074070836723647048933401)
                ·
                  refine ⟨3055553127542735286700051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074070836723647048933401 3055553127542735286700051)
                  ·
                    refine ⟨4583329691314102930050077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3055553127542735286700051 4583329691314102930050077)
                    ·
                      refine ⟨1718748634242788598768779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583329691314102930050077 1718748634242788598768779)
                      ·
                        rfl

theorem cell23_3347251_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 6, 1, 1, 4, 2, 1, 3].length) (baseStart_3347251 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347251 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347251 prefixEnd_3347251 := by exact prefixLift 3347251
  have htrace : WordTrace (prefixWord ++ tailWord_3347251) baseStart_3347251 baseEnd_3347251 := by
    simpa [prefixWord, tailWord_3347251, baseEnd_3347251] using wordTrace_append hprefix tailTrace_3347251
  have hstable : (prefixWord ++ tailWord_3347251).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347251).length < 2 ^ (prefixWord ++ tailWord_3347251).sum := by decide
  have hdescent : baseEnd_3347251 < baseStart_3347251 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347251) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347252 : List Nat := [2, 5, 1, 1, 3, 1, 1, 4, 1, 2, 2]
def baseStart_3347252 : Nat := 118140960795 + 3347252 * 2 ^ 59
def prefixEnd_3347252 : Nat := 4983230072969 + 3 ^ 40 * 3347252 * 2
def baseEnd_3347252 : Nat := 1718749147723443094856275

theorem tailTrace_3347252 : CollatzResearch.WordTrace tailWord_3347252 prefixEnd_3347252 1718749147723443094856275 := by
  unfold tailWord_3347252
  simp only [CollatzResearch.WordTrace]
  refine ⟨61042155034742571987062005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81389540046323429316082673 61042155034742571987062005)
  ·
    refine ⟨5722702034507116123787063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 61042155034742571987062005 5722702034507116123787063)
    ·
      refine ⟨8584053051760674185680595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5722702034507116123787063 8584053051760674185680595)
      ·
        refine ⟨12876079577641011278520893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584053051760674185680595 12876079577641011278520893)
        ·
          refine ⟨4828529841615379229445335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 12876079577641011278520893 4828529841615379229445335)
          ·
            refine ⟨7242794762423068844168003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4828529841615379229445335 7242794762423068844168003)
            ·
              refine ⟨10864192143634603266252005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7242794762423068844168003 10864192143634603266252005)
              ·
                refine ⟨2037036026931488112422251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10864192143634603266252005 2037036026931488112422251)
                ·
                  refine ⟨3055554040397232168633377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037036026931488112422251 3055554040397232168633377)
                  ·
                    refine ⟨2291665530297924126475033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3055554040397232168633377 2291665530297924126475033)
                    ·
                      refine ⟨1718749147723443094856275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291665530297924126475033 1718749147723443094856275)
                      ·
                        rfl

theorem cell23_3347252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 1, 1, 4, 1, 2, 2].length) (baseStart_3347252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347252 prefixEnd_3347252 := by exact prefixLift 3347252
  have htrace : WordTrace (prefixWord ++ tailWord_3347252) baseStart_3347252 baseEnd_3347252 := by
    simpa [prefixWord, tailWord_3347252, baseEnd_3347252] using wordTrace_append hprefix tailTrace_3347252
  have hstable : (prefixWord ++ tailWord_3347252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347252).length < 2 ^ (prefixWord ++ tailWord_3347252).sum := by decide
  have hdescent : baseEnd_3347252 < baseStart_3347252 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347267 : List Nat := [1, 1, 1, 3, 1, 4, 3, 1, 2, 6]
def baseStart_3347267 : Nat := 118140960795 + 3347267 * 2 ^ 59
def prefixEnd_3347267 : Nat := 4983230072969 + 3 ^ 40 * 3347267 * 2
def baseEnd_3347267 : Nat := 572918949977753512056235

theorem tailTrace_3347267 : CollatzResearch.WordTrace tailWord_3347267 prefixEnd_3347267 572918949977753512056235 := by
  unfold tailWord_3347267
  simp only [CollatzResearch.WordTrace]
  refine ⟨122084857164430801535920055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81389904776287201023946703 122084857164430801535920055)
  ·
    refine ⟨183127285746646202303880083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122084857164430801535920055 183127285746646202303880083)
    ·
      refine ⟨274690928619969303455820125, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183127285746646202303880083 274690928619969303455820125)
      ·
        refine ⟨103009098232488488795932547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274690928619969303455820125 103009098232488488795932547)
        ·
          refine ⟨154513647348732733193898821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103009098232488488795932547 154513647348732733193898821)
          ·
            refine ⟨28971308877887387473856029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154513647348732733193898821 28971308877887387473856029)
            ·
              refine ⟨10864240829207770302696011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28971308877887387473856029 10864240829207770302696011)
              ·
                refine ⟨16296361243811655454044017, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10864240829207770302696011 16296361243811655454044017)
                ·
                  refine ⟨12222270932858741590533013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16296361243811655454044017 12222270932858741590533013)
                  ·
                    refine ⟨572918949977753512056235, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12222270932858741590533013 572918949977753512056235)
                    ·
                      rfl

theorem cell23_3347267_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 3, 1, 2, 6].length) (baseStart_3347267 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347267 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347267 prefixEnd_3347267 := by exact prefixLift 3347267
  have htrace : WordTrace (prefixWord ++ tailWord_3347267) baseStart_3347267 baseEnd_3347267 := by
    simpa [prefixWord, tailWord_3347267, baseEnd_3347267] using wordTrace_append hprefix tailTrace_3347267
  have hstable : (prefixWord ++ tailWord_3347267).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347267).length < 2 ^ (prefixWord ++ tailWord_3347267).sum := by decide
  have hdescent : baseEnd_3347267 < baseStart_3347267 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347267) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347304 : List Nat := [2, 1, 4, 2, 1, 2, 1, 2, 2, 2, 4]
def baseStart_3347304 : Nat := 118140960795 + 3347304 * 2 ^ 59
def prefixEnd_3347304 : Nat := 4983230072969 + 3 ^ 40 * 3347304 * 2
def baseEnd_3347304 : Nat := 1718775848717476891406035

theorem tailTrace_3347304 : CollatzResearch.WordTrace tailWord_3347304 prefixEnd_3347304 1718775848717476891406035 := by
  unfold tailWord_3347304
  simp only [CollatzResearch.WordTrace]
  refine ⟨61043103332648378427508483, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81390804443531171236677977 61043103332648378427508483)
  ·
    refine ⟨91564654998972567641262725, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61043103332648378427508483 91564654998972567641262725)
    ·
      refine ⟨17168372812307356432736761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91564654998972567641262725 17168372812307356432736761)
      ·
        refine ⟨12876279609230517324552571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17168372812307356432736761 12876279609230517324552571)
        ·
          refine ⟨19314419413845775986828857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12876279609230517324552571 19314419413845775986828857)
          ·
            refine ⟨14485814560384331990121643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19314419413845775986828857 14485814560384331990121643)
            ·
              refine ⟨21728721840576497985182465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14485814560384331990121643 21728721840576497985182465)
              ·
                refine ⟨16296541380432373488886849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21728721840576497985182465 16296541380432373488886849)
                ·
                  refine ⟨12222406035324280116665137, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16296541380432373488886849 12222406035324280116665137)
                  ·
                    refine ⟨9166804526493210087498853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12222406035324280116665137 9166804526493210087498853)
                    ·
                      refine ⟨1718775848717476891406035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9166804526493210087498853 1718775848717476891406035)
                      ·
                        rfl

theorem cell23_3347304_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 1, 2, 2, 2, 4].length) (baseStart_3347304 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347304 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347304 prefixEnd_3347304 := by exact prefixLift 3347304
  have htrace : WordTrace (prefixWord ++ tailWord_3347304) baseStart_3347304 baseEnd_3347304 := by
    simpa [prefixWord, tailWord_3347304, baseEnd_3347304] using wordTrace_append hprefix tailTrace_3347304
  have hstable : (prefixWord ++ tailWord_3347304).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347304).length < 2 ^ (prefixWord ++ tailWord_3347304).sum := by decide
  have hdescent : baseEnd_3347304 < baseStart_3347304 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347304) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347327 : List Nat := [1, 1, 2, 2, 1, 1, 5, 2, 1, 7]
def baseStart_3347327 : Nat := 118140960795 + 3347327 * 2 ^ 59
def prefixEnd_3347327 : Nat := 4983230072969 + 3 ^ 40 * 3347327 * 2
def baseEnd_3347327 : Nat := 572929219590843433806143

theorem tailTrace_3347327 : CollatzResearch.WordTrace tailWord_3347327 prefixEnd_3347327 572929219590843433806143 := by
  unfold tailWord_3347327
  simp only [CollatzResearch.WordTrace]
  refine ⟨122087045544213431783104235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81391363696142287855402823 122087045544213431783104235)
  ·
    refine ⟨183130568316320147674656353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122087045544213431783104235 183130568316320147674656353)
    ·
      refine ⟨137347926237240110755992265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183130568316320147674656353 137347926237240110755992265)
      ·
        refine ⟨103010944677930083066994199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137347926237240110755992265 103010944677930083066994199)
        ·
          refine ⟨154516417016895124600491299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103010944677930083066994199 154516417016895124600491299)
          ·
            refine ⟨231774625525342686900736949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154516417016895124600491299 231774625525342686900736949)
            ·
              refine ⟨21728871143000876896944089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231774625525342686900736949 21728871143000876896944089)
              ·
                refine ⟨16296653357250657672708067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21728871143000876896944089 16296653357250657672708067)
                ·
                  refine ⟨24444980035875986509062101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16296653357250657672708067 24444980035875986509062101)
                  ·
                    refine ⟨572929219590843433806143, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24444980035875986509062101 572929219590843433806143)
                    ·
                      rfl

theorem cell23_3347327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 5, 2, 1, 7].length) (baseStart_3347327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347327 prefixEnd_3347327 := by exact prefixLift 3347327
  have htrace : WordTrace (prefixWord ++ tailWord_3347327) baseStart_3347327 baseEnd_3347327 := by
    simpa [prefixWord, tailWord_3347327, baseEnd_3347327] using wordTrace_append hprefix tailTrace_3347327
  have hstable : (prefixWord ++ tailWord_3347327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347327).length < 2 ^ (prefixWord ++ tailWord_3347327).sum := by decide
  have hdescent : baseEnd_3347327 < baseStart_3347327 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347361 : List Nat := [1, 2, 3, 4, 1, 2, 1, 2, 2, 5]
def baseStart_3347361 : Nat := 118140960795 + 3347361 * 2 ^ 59
def prefixEnd_3347361 : Nat := 4983230072969 + 3 ^ 40 * 3347361 * 2
def baseEnd_3347361 : Nat := 572935039038261056131091

theorem tailTrace_3347361 : CollatzResearch.WordTrace tailWord_3347361 prefixEnd_3347361 572935039038261056131091 := by
  unfold tailWord_3347361
  simp only [CollatzResearch.WordTrace]
  refine ⟨122088285626090255589841937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81392190417393503726561291 122088285626090255589841937)
  ·
    refine ⟨91566214219567691692381453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122088285626090255589841937 91566214219567691692381453)
    ·
      refine ⟨34337330332337884384643045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91566214219567691692381453 34337330332337884384643045)
      ·
        refine ⟨6438249437313353322120571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34337330332337884384643045 6438249437313353322120571)
        ·
          refine ⟨9657374155970029983180857, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6438249437313353322120571 9657374155970029983180857)
          ·
            refine ⟨7243030616977522487385643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9657374155970029983180857 7243030616977522487385643)
            ·
              refine ⟨10864545925466283731078465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243030616977522487385643 10864545925466283731078465)
              ·
                refine ⟨8148409444099712798308849, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10864545925466283731078465 8148409444099712798308849)
                ·
                  refine ⟨6111307083074784598731637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8148409444099712798308849 6111307083074784598731637)
                  ·
                    refine ⟨572935039038261056131091, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6111307083074784598731637 572935039038261056131091)
                    ·
                      rfl

theorem cell23_3347361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 4, 1, 2, 1, 2, 2, 5].length) (baseStart_3347361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347361 prefixEnd_3347361 := by exact prefixLift 3347361
  have htrace : WordTrace (prefixWord ++ tailWord_3347361) baseStart_3347361 baseEnd_3347361 := by
    simpa [prefixWord, tailWord_3347361, baseEnd_3347361] using wordTrace_append hprefix tailTrace_3347361
  have hstable : (prefixWord ++ tailWord_3347361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347361).length < 2 ^ (prefixWord ++ tailWord_3347361).sum := by decide
  have hdescent : baseEnd_3347361 < baseStart_3347361 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347381 : List Nat := [1, 3, 3, 2, 1, 1, 2, 1, 1, 6, 2]
def baseStart_3347381 : Nat := 118140960795 + 3347381 * 2 ^ 59
def prefixEnd_3347381 : Nat := 4983230072969 + 3 ^ 40 * 3347381 * 2
def baseEnd_3347381 : Nat := 1718815386727873090143181

theorem tailTrace_3347381 : CollatzResearch.WordTrace tailWord_3347381 prefixEnd_3347381 1718815386727873090143181 := by
  unfold tailWord_3347381
  simp only [CollatzResearch.WordTrace]
  refine ⟨122089015086017799005569997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81392676724011866003713331 122089015086017799005569997)
  ·
    refine ⟨45783380657256674627088749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122089015086017799005569997 45783380657256674627088749)
    ·
      refine ⟨17168767746471252985158281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45783380657256674627088749 17168767746471252985158281)
      ·
        refine ⟨12876575809853439738868711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17168767746471252985158281 12876575809853439738868711)
        ·
          refine ⟨19314863714780159608303067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12876575809853439738868711 19314863714780159608303067)
          ·
            refine ⟨28972295572170239412454601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19314863714780159608303067 28972295572170239412454601)
            ·
              refine ⟨21729221679127679559340951, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28972295572170239412454601 21729221679127679559340951)
              ·
                refine ⟨32593832518691519339011427, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21729221679127679559340951 32593832518691519339011427)
                ·
                  refine ⟨48890748778037279008517141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32593832518691519339011427 48890748778037279008517141)
                  ·
                    refine ⟨2291753848970497453524241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48890748778037279008517141 2291753848970497453524241)
                    ·
                      refine ⟨1718815386727873090143181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291753848970497453524241 1718815386727873090143181)
                      ·
                        rfl

theorem cell23_3347381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 2, 1, 1, 6, 2].length) (baseStart_3347381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347381 prefixEnd_3347381 := by exact prefixLift 3347381
  have htrace : WordTrace (prefixWord ++ tailWord_3347381) baseStart_3347381 baseEnd_3347381 := by
    simpa [prefixWord, tailWord_3347381, baseEnd_3347381] using wordTrace_append hprefix tailTrace_3347381
  have hstable : (prefixWord ++ tailWord_3347381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347381).length < 2 ^ (prefixWord ++ tailWord_3347381).sum := by decide
  have hdescent : baseEnd_3347381 < baseStart_3347381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347421 : List Nat := [1, 4, 3, 1, 2, 1, 1, 4, 6]
def baseStart_3347421 : Nat := 118140960795 + 3347421 * 2 ^ 59
def prefixEnd_3347421 : Nat := 4983230072969 + 3 ^ 40 * 3347421 * 2
def baseEnd_3347421 : Nat := 190981769550450325960333

theorem tailTrace_3347421 : CollatzResearch.WordTrace tailWord_3347421 prefixEnd_3347421 190981769550450325960333 := by
  unfold tailWord_3347421
  simp only [CollatzResearch.WordTrace]
  refine ⟨122090474005872885837026117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81393649337248590558017411 122090474005872885837026117)
  ·
    refine ⟨22891963876101166094442397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122090474005872885837026117 22891963876101166094442397)
    ·
      refine ⟨8584486453537937285415899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22891963876101166094442397 8584486453537937285415899)
      ·
        refine ⟨12876729680306905928123849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8584486453537937285415899 12876729680306905928123849)
        ·
          refine ⟨9657547260230179446092887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12876729680306905928123849 9657547260230179446092887)
          ·
            refine ⟨14486320890345269169139331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9657547260230179446092887 14486320890345269169139331)
            ·
              refine ⟨21729481335517903753708997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14486320890345269169139331 21729481335517903753708997)
              ·
                refine ⟨4074277750409606953820437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21729481335517903753708997 4074277750409606953820437)
                ·
                  refine ⟨190981769550450325960333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4074277750409606953820437 190981769550450325960333)
                  ·
                    rfl

theorem cell23_3347421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 2, 1, 1, 4, 6].length) (baseStart_3347421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347421 prefixEnd_3347421 := by exact prefixLift 3347421
  have htrace : WordTrace (prefixWord ++ tailWord_3347421) baseStart_3347421 baseEnd_3347421 := by
    simpa [prefixWord, tailWord_3347421, baseEnd_3347421] using wordTrace_append hprefix tailTrace_3347421
  have hstable : (prefixWord ++ tailWord_3347421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347421).length < 2 ^ (prefixWord ++ tailWord_3347421).sum := by decide
  have hdescent : baseEnd_3347421 < baseStart_3347421 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347468 : List Nat := [2, 2, 1, 2, 3, 2, 4, 1, 1, 5]
def baseStart_3347468 : Nat := 118140960795 + 3347468 * 2 ^ 59
def prefixEnd_3347468 : Nat := 4983230072969 + 3 ^ 40 * 3347468 * 2
def baseEnd_3347468 : Nat := 572953353181604749918427

theorem tailTrace_3347468 : CollatzResearch.WordTrace tailWord_3347468 prefixEnd_3347468 572953353181604749918427 := by
  unfold tailWord_3347468
  simp only [CollatzResearch.WordTrace]
  refine ⟨61046094118351306431993529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81394792157801741909324705 61046094118351306431993529)
  ·
    refine ⟨45784570588763479823995147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61046094118351306431993529 45784570588763479823995147)
    ·
      refine ⟨68676855883145219735992721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45784570588763479823995147 68676855883145219735992721)
      ·
        refine ⟨51507641912358914801994541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68676855883145219735992721 51507641912358914801994541)
        ·
          refine ⟨19315365717134593050747953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51507641912358914801994541 19315365717134593050747953)
          ·
            refine ⟨14486524287850944788060965, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19315365717134593050747953 14486524287850944788060965)
            ·
              refine ⟨2716223303972052147761431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14486524287850944788060965 2716223303972052147761431)
              ·
                refine ⟨4074334955958078221642147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716223303972052147761431 4074334955958078221642147)
                ·
                  refine ⟨6111502433937117332463221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074334955958078221642147 6111502433937117332463221)
                  ·
                    refine ⟨572953353181604749918427, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6111502433937117332463221 572953353181604749918427)
                    ·
                      rfl

theorem cell23_3347468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 4, 1, 1, 5].length) (baseStart_3347468 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347468 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347468 prefixEnd_3347468 := by exact prefixLift 3347468
  have htrace : WordTrace (prefixWord ++ tailWord_3347468) baseStart_3347468 baseEnd_3347468 := by
    simpa [prefixWord, tailWord_3347468, baseEnd_3347468] using wordTrace_append hprefix tailTrace_3347468
  have hstable : (prefixWord ++ tailWord_3347468).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347468).length < 2 ^ (prefixWord ++ tailWord_3347468).sum := by decide
  have hdescent : baseEnd_3347468 < baseStart_3347468 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347491 : List Nat := [1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5]
def baseStart_3347491 : Nat := 118140960795 + 3347491 * 2 ^ 59
def prefixEnd_3347491 : Nat := 4983230072969 + 3 ^ 40 * 3347491 * 2
def baseEnd_3347491 : Nat := 1718871869599867659767675

theorem tailTrace_3347491 : CollatzResearch.WordTrace tailWord_3347491 prefixEnd_3347491 1718871869599867659767675 := by
  unfold tailWord_3347491
  simp only [CollatzResearch.WordTrace]
  refine ⟨122093027115619287792074327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81395351410412858528049551 122093027115619287792074327)
  ·
    refine ⟨183139540673428931688111491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122093027115619287792074327 183139540673428931688111491)
    ·
      refine ⟨274709311010143397532167237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183139540673428931688111491 274709311010143397532167237)
      ·
        refine ⟨51507995814401887037281357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274709311010143397532167237 51507995814401887037281357)
        ·
          refine ⟨19315498430400707638980509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51507995814401887037281357 19315498430400707638980509)
          ·
            refine ⟨7243311911400265364617691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19315498430400707638980509 7243311911400265364617691)
            ·
              refine ⟨10864967867100398046926537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243311911400265364617691 10864967867100398046926537)
              ·
                refine ⟨8148725900325298535194903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10864967867100398046926537 8148725900325298535194903)
                ·
                  refine ⟨12223088850487947802792355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8148725900325298535194903 12223088850487947802792355)
                  ·
                    refine ⟨18334633275731921704188533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12223088850487947802792355 18334633275731921704188533)
                    ·
                      refine ⟨1718871869599867659767675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18334633275731921704188533 1718871869599867659767675)
                      ·
                        rfl

theorem cell23_3347491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 3, 1, 2, 1, 1, 5].length) (baseStart_3347491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347491 prefixEnd_3347491 := by exact prefixLift 3347491
  have htrace : WordTrace (prefixWord ++ tailWord_3347491) baseStart_3347491 baseEnd_3347491 := by
    simpa [prefixWord, tailWord_3347491, baseEnd_3347491] using wordTrace_append hprefix tailTrace_3347491
  have hstable : (prefixWord ++ tailWord_3347491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347491).length < 2 ^ (prefixWord ++ tailWord_3347491).sum := by decide
  have hdescent : baseEnd_3347491 < baseStart_3347491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347549 : List Nat := [1, 4, 4, 1, 2, 2, 2, 1, 2, 4]
def baseStart_3347549 : Nat := 118140960795 + 3347549 * 2 ^ 59
def prefixEnd_3347549 : Nat := 4983230072969 + 3 ^ 40 * 3347549 * 2
def baseEnd_3347549 : Nat := 572967217159276144280803

theorem tailTrace_3347549 : CollatzResearch.WordTrace tailWord_3347549 prefixEnd_3347549 572967217159276144280803 := by
  unfold tailWord_3347549
  simp only [CollatzResearch.WordTrace]
  refine ⟨122095142549409163697685701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81396761699606109131790467 122095142549409163697685701)
  ·
    refine ⟨22892839228014218193316069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122095142549409163697685701 22892839228014218193316069)
    ·
      refine ⟨4292407355252665911246763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 22892839228014218193316069 4292407355252665911246763)
      ·
        refine ⟨6438611032878998866870145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4292407355252665911246763 6438611032878998866870145)
        ·
          refine ⟨4828958274659249150152609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6438611032878998866870145 4828958274659249150152609)
          ·
            refine ⟨3621718705994436862614457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4828958274659249150152609 3621718705994436862614457)
            ·
              refine ⟨2716289029495827646960843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3621718705994436862614457 2716289029495827646960843)
              ·
                refine ⟨4074433544243741470441265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716289029495827646960843 4074433544243741470441265)
                ·
                  refine ⟨3055825158182806102830949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074433544243741470441265 3055825158182806102830949)
                  ·
                    refine ⟨572967217159276144280803, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3055825158182806102830949 572967217159276144280803)
                    ·
                      rfl

theorem cell23_3347549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 2, 2, 2, 1, 2, 4].length) (baseStart_3347549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347549 prefixEnd_3347549 := by exact prefixLift 3347549
  have htrace : WordTrace (prefixWord ++ tailWord_3347549) baseStart_3347549 baseEnd_3347549 := by
    simpa [prefixWord, tailWord_3347549, baseEnd_3347549] using wordTrace_append hprefix tailTrace_3347549
  have hstable : (prefixWord ++ tailWord_3347549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347549).length < 2 ^ (prefixWord ++ tailWord_3347549).sum := by decide
  have hdescent : baseEnd_3347549 < baseStart_3347549 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347565 : List Nat := [1, 5, 1, 1, 2, 3, 1, 1, 3, 3, 2]
def baseStart_3347565 : Nat := 118140960795 + 3347565 * 2 ^ 59
def prefixEnd_3347565 : Nat := 4983230072969 + 3 ^ 40 * 3347565 * 2
def baseEnd_3347565 : Nat := 1718909867168300370242335

theorem tailTrace_3347565 : CollatzResearch.WordTrace tailWord_3347565 prefixEnd_3347565 1718909867168300370242335 := by
  unfold tailWord_3347565
  simp only [CollatzResearch.WordTrace]
  refine ⟨122095726117351198430268149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81397150744900798953512099 122095726117351198430268149)
  ·
    refine ⟨11446474323501674852837639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122095726117351198430268149 11446474323501674852837639)
    ·
      refine ⟨17169711485252512279256459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11446474323501674852837639 17169711485252512279256459)
      ·
        refine ⟨25754567227878768418884689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17169711485252512279256459 25754567227878768418884689)
        ·
          refine ⟨19315925420909076314163517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25754567227878768418884689 19315925420909076314163517)
          ·
            refine ⟨7243472032840903617811319, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19315925420909076314163517 7243472032840903617811319)
            ·
              refine ⟨10865208049261355426716979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243472032840903617811319 10865208049261355426716979)
              ·
                refine ⟨16297812073892033140075469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865208049261355426716979 16297812073892033140075469)
                ·
                  refine ⟨6111679527709512427528301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16297812073892033140075469 6111679527709512427528301)
                  ·
                    refine ⟨2291879822891067160323113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6111679527709512427528301 2291879822891067160323113)
                    ·
                      refine ⟨1718909867168300370242335, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291879822891067160323113 1718909867168300370242335)
                      ·
                        rfl

theorem cell23_3347565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 3, 1, 1, 3, 3, 2].length) (baseStart_3347565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347565 prefixEnd_3347565 := by exact prefixLift 3347565
  have htrace : WordTrace (prefixWord ++ tailWord_3347565) baseStart_3347565 baseEnd_3347565 := by
    simpa [prefixWord, tailWord_3347565, baseEnd_3347565] using wordTrace_append hprefix tailTrace_3347565
  have hstable : (prefixWord ++ tailWord_3347565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347565).length < 2 ^ (prefixWord ++ tailWord_3347565).sum := by decide
  have hdescent : baseEnd_3347565 < baseStart_3347565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347581 : List Nat := [1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 5]
def baseStart_3347581 : Nat := 118140960795 + 3347581 * 2 ^ 59
def prefixEnd_3347581 : Nat := 4983230072969 + 3 ^ 40 * 3347581 * 2
def baseEnd_3347581 : Nat := 1718918082858772307642261

theorem tailTrace_3347581 : CollatzResearch.WordTrace tailWord_3347581 prefixEnd_3347581 1718918082858772307642261 := by
  unfold tailWord_3347581
  simp only [CollatzResearch.WordTrace]
  refine ⟨122096309685293233162850597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81397539790195488775233731 122096309685293233162850597)
  ·
    refine ⟨22893058065992481218034487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122096309685293233162850597 22893058065992481218034487)
    ·
      refine ⟨34339587098988721827051731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22893058065992481218034487 34339587098988721827051731)
      ·
        refine ⟨51509380648483082740577597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34339587098988721827051731 51509380648483082740577597)
        ·
          refine ⟨19316017743181156027716599, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51509380648483082740577597 19316017743181156027716599)
          ·
            refine ⟨28974026614771734041574899, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19316017743181156027716599 28974026614771734041574899)
            ·
              refine ⟨43461039922157601062362349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28974026614771734041574899 43461039922157601062362349)
              ·
                refine ⟨16297889970809100398385881, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43461039922157601062362349 16297889970809100398385881)
                ·
                  refine ⟨12223417478106825298789411, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16297889970809100398385881 12223417478106825298789411)
                  ·
                    refine ⟨18335126217160237948184117, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12223417478106825298789411 18335126217160237948184117)
                    ·
                      refine ⟨1718918082858772307642261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18335126217160237948184117 1718918082858772307642261)
                      ·
                        rfl

theorem cell23_3347581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 3, 1, 1, 3, 2, 1, 5].length) (baseStart_3347581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347581 prefixEnd_3347581 := by exact prefixLift 3347581
  have htrace : WordTrace (prefixWord ++ tailWord_3347581) baseStart_3347581 baseEnd_3347581 := by
    simpa [prefixWord, tailWord_3347581, baseEnd_3347581] using wordTrace_append hprefix tailTrace_3347581
  have hstable : (prefixWord ++ tailWord_3347581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347581).length < 2 ^ (prefixWord ++ tailWord_3347581).sum := by decide
  have hdescent : baseEnd_3347581 < baseStart_3347581 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347591 : List Nat := [1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 4]
def baseStart_3347591 : Nat := 118140960795 + 3347591 * 2 ^ 59
def prefixEnd_3347591 : Nat := 4983230072969 + 3 ^ 40 * 3347591 * 2
def baseEnd_3347591 : Nat := 1718923217665317268517215

theorem tailTrace_3347591 : CollatzResearch.WordTrace tailWord_3347591 prefixEnd_3347591 1718923217665317268517215 := by
  unfold tailWord_3347591
  simp only [CollatzResearch.WordTrace]
  refine ⟨122096674415257004870714627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81397782943504669913809751 122096674415257004870714627)
  ·
    refine ⟨183145011622885507306071941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122096674415257004870714627 183145011622885507306071941)
    ·
      refine ⟨34339689679291032619888489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183145011622885507306071941 34339689679291032619888489)
      ·
        refine ⟨25754767259468274464916367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34339689679291032619888489 25754767259468274464916367)
        ·
          refine ⟨38632150889202411697374551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25754767259468274464916367 38632150889202411697374551)
          ·
            refine ⟨57948226333803617546061827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38632150889202411697374551 57948226333803617546061827)
            ·
              refine ⟨86922339500705426319092741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57948226333803617546061827 86922339500705426319092741)
              ·
                refine ⟨16297938656382267434829889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86922339500705426319092741 16297938656382267434829889)
                ·
                  refine ⟨12223453992286700576122417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16297938656382267434829889 12223453992286700576122417)
                  ·
                    refine ⟨9167590494215025432091813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12223453992286700576122417 9167590494215025432091813)
                    ·
                      refine ⟨1718923217665317268517215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9167590494215025432091813 1718923217665317268517215)
                      ·
                        rfl

theorem cell23_3347591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 1, 4, 2, 2, 4].length) (baseStart_3347591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347591 prefixEnd_3347591 := by exact prefixLift 3347591
  have htrace : WordTrace (prefixWord ++ tailWord_3347591) baseStart_3347591 baseEnd_3347591 := by
    simpa [prefixWord, tailWord_3347591, baseEnd_3347591] using wordTrace_append hprefix tailTrace_3347591
  have hstable : (prefixWord ++ tailWord_3347591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347591).length < 2 ^ (prefixWord ++ tailWord_3347591).sum := by decide
  have hdescent : baseEnd_3347591 < baseStart_3347591 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347598 : List Nat := [4, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3]
def baseStart_3347598 : Nat := 118140960795 + 3347598 * 2 ^ 59
def prefixEnd_3347598 : Nat := 4983230072969 + 3 ^ 40 * 3347598 * 2
def baseEnd_3347598 : Nat := 1718926812029898741129683

theorem tailTrace_3347598 : CollatzResearch.WordTrace tailWord_3347598 prefixEnd_3347598 1718926812029898741129683 := by
  unfold tailWord_3347598
  simp only [CollatzResearch.WordTrace]
  refine ⟨15262116215778955633277431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81397953150821096710812965 15262116215778955633277431)
  ·
    refine ⟨22893174323668433449916147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15262116215778955633277431 22893174323668433449916147)
    ·
      refine ⟨34339761485502650174874221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22893174323668433449916147 34339761485502650174874221)
      ·
        refine ⟨12877410557063493815577833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34339761485502650174874221 12877410557063493815577833)
        ·
          refine ⟨9658057917797620361683375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12877410557063493815577833 9658057917797620361683375)
          ·
            refine ⟨14487086876696430542525063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9658057917797620361683375 14487086876696430542525063)
            ·
              refine ⟨21730630315044645813787595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14487086876696430542525063 21730630315044645813787595)
              ·
                refine ⟨32595945472566968720681393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21730630315044645813787595 32595945472566968720681393)
                ·
                  refine ⟨24446959104425226540511045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32595945472566968720681393 24446959104425226540511045)
                  ·
                    refine ⟨4583804832079729976345821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24446959104425226540511045 4583804832079729976345821)
                    ·
                      refine ⟨1718926812029898741129683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583804832079729976345821 1718926812029898741129683)
                      ·
                        rfl

theorem cell23_3347598_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 2, 1, 1, 1, 2, 4, 3].length) (baseStart_3347598 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347598 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347598 prefixEnd_3347598 := by exact prefixLift 3347598
  have htrace : WordTrace (prefixWord ++ tailWord_3347598) baseStart_3347598 baseEnd_3347598 := by
    simpa [prefixWord, tailWord_3347598, baseEnd_3347598] using wordTrace_append hprefix tailTrace_3347598
  have hstable : (prefixWord ++ tailWord_3347598).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347598).length < 2 ^ (prefixWord ++ tailWord_3347598).sum := by decide
  have hdescent : baseEnd_3347598 < baseStart_3347598 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347598) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347608 : List Nat := [2, 1, 2, 4, 2, 2, 1, 1, 2, 2, 4]
def baseStart_3347608 : Nat := 118140960795 + 3347608 * 2 ^ 59
def prefixEnd_3347608 : Nat := 4983230072969 + 3 ^ 40 * 3347608 * 2
def baseEnd_3347608 : Nat := 1718931946836443702004637

theorem tailTrace_3347608 : CollatzResearch.WordTrace tailWord_3347608 prefixEnd_3347608 1718931946836443702004637 := by
  unfold tailWord_3347608
  simp only [CollatzResearch.WordTrace]
  refine ⟨61048647228097708387041739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81398196304130277849388985 61048647228097708387041739)
  ·
    refine ⟨91572970842146562580562609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61048647228097708387041739 91572970842146562580562609)
    ·
      refine ⟨68679728131609921935421957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91572970842146562580562609 68679728131609921935421957)
      ·
        refine ⟨12877449024676860362891617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68679728131609921935421957 12877449024676860362891617)
        ·
          refine ⟨9658086768507645272168713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12877449024676860362891617 9658086768507645272168713)
          ·
            refine ⟨7243565076380733954126535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9658086768507645272168713 7243565076380733954126535)
            ·
              refine ⟨10865347614571100931189803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7243565076380733954126535 10865347614571100931189803)
              ·
                refine ⟨16298021421856651396784705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10865347614571100931189803 16298021421856651396784705)
                ·
                  refine ⟨12223516066392488547588529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16298021421856651396784705 12223516066392488547588529)
                  ·
                    refine ⟨9167637049794366410691397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12223516066392488547588529 9167637049794366410691397)
                    ·
                      refine ⟨1718931946836443702004637, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9167637049794366410691397 1718931946836443702004637)
                      ·
                        rfl

theorem cell23_3347608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 1, 1, 2, 2, 4].length) (baseStart_3347608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347608 prefixEnd_3347608 := by exact prefixLift 3347608
  have htrace : WordTrace (prefixWord ++ tailWord_3347608) baseStart_3347608 baseEnd_3347608 := by
    simpa [prefixWord, tailWord_3347608, baseEnd_3347608] using wordTrace_append hprefix tailTrace_3347608
  have hstable : (prefixWord ++ tailWord_3347608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347608).length < 2 ^ (prefixWord ++ tailWord_3347608).sum := by decide
  have hdescent : baseEnd_3347608 < baseStart_3347608 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347612 : List Nat := [2, 2, 3, 2, 1, 2, 2, 3, 2, 2, 2]
def baseStart_3347612 : Nat := 118140960795 + 3347612 * 2 ^ 59
def prefixEnd_3347612 : Nat := 4983230072969 + 3 ^ 40 * 3347612 * 2
def baseEnd_3347612 : Nat := 1718934000759061686354619

theorem tailTrace_3347612 : CollatzResearch.WordTrace tailWord_3347612 prefixEnd_3347612 1718934000759061686354619 := by
  unfold tailWord_3347612
  simp only [CollatzResearch.WordTrace]
  refine ⟨61048720174090462728614545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81398293565453950304819393 61048720174090462728614545)
  ·
    refine ⟨45786540130567847046460909, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61048720174090462728614545 45786540130567847046460909)
    ·
      refine ⟨17169952548962942642422841, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45786540130567847046460909 17169952548962942642422841)
      ·
        refine ⟨12877464411722206981817131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17169952548962942642422841 12877464411722206981817131)
        ·
          refine ⟨19316196617583310472725697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877464411722206981817131 19316196617583310472725697)
          ·
            refine ⟨14487147463187482854544273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19316196617583310472725697 14487147463187482854544273)
            ·
              refine ⟨10865360597390612140908205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14487147463187482854544273 10865360597390612140908205)
              ·
                refine ⟨4074510224021479552840577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10865360597390612140908205 4074510224021479552840577)
                ·
                  refine ⟨3055882668016109664630433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074510224021479552840577 3055882668016109664630433)
                  ·
                    refine ⟨2291912001012082248472825, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3055882668016109664630433 2291912001012082248472825)
                    ·
                      refine ⟨1718934000759061686354619, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2291912001012082248472825 1718934000759061686354619)
                      ·
                        rfl

theorem cell23_3347612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 2, 2, 3, 2, 2, 2].length) (baseStart_3347612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347612 prefixEnd_3347612 := by exact prefixLift 3347612
  have htrace : WordTrace (prefixWord ++ tailWord_3347612) baseStart_3347612 baseEnd_3347612 := by
    simpa [prefixWord, tailWord_3347612, baseEnd_3347612] using wordTrace_append hprefix tailTrace_3347612
  have hstable : (prefixWord ++ tailWord_3347612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347612).length < 2 ^ (prefixWord ++ tailWord_3347612).sum := by decide
  have hdescent : baseEnd_3347612 < baseStart_3347612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347688 : List Nat := [2, 1, 4, 1, 2, 1, 1, 3, 1, 4, 3]
def baseStart_3347688 : Nat := 118140960795 + 3347688 * 2 ^ 59
def prefixEnd_3347688 : Nat := 4983230072969 + 3 ^ 40 * 3347688 * 2
def baseEnd_3347688 : Nat := 1718973025288803389004269

theorem tailTrace_3347688 : CollatzResearch.WordTrace tailWord_3347688 prefixEnd_3347688 1718973025288803389004269 := by
  unfold tailWord_3347688
  simp only [CollatzResearch.WordTrace]
  refine ⟨61050106147952795218497859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81400141530603726957997145 61050106147952795218497859)
  ·
    refine ⟨91575159221929192827746789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61050106147952795218497859 91575159221929192827746789)
    ·
      refine ⟨17170342354111723655202523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91575159221929192827746789 17170342354111723655202523)
      ·
        refine ⟨25755513531167585482803785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17170342354111723655202523 25755513531167585482803785)
        ·
          refine ⟨19316635148375689112102839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25755513531167585482803785 19316635148375689112102839)
          ·
            refine ⟨28974952722563533668154259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19316635148375689112102839 28974952722563533668154259)
            ·
              refine ⟨43462429083845300502231389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28974952722563533668154259 43462429083845300502231389)
              ·
                refine ⟨16298410906441987688336771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43462429083845300502231389 16298410906441987688336771)
                ·
                  refine ⟨24447616359662981532505157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16298410906441987688336771 24447616359662981532505157)
                  ·
                    refine ⟨4583928067436809037344717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24447616359662981532505157 4583928067436809037344717)
                    ·
                      refine ⟨1718973025288803389004269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583928067436809037344717 1718973025288803389004269)
                      ·
                        rfl

theorem cell23_3347688_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 1, 1, 3, 1, 4, 3].length) (baseStart_3347688 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347688 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347688 prefixEnd_3347688 := by exact prefixLift 3347688
  have htrace : WordTrace (prefixWord ++ tailWord_3347688) baseStart_3347688 baseEnd_3347688 := by
    simpa [prefixWord, tailWord_3347688, baseEnd_3347688] using wordTrace_append hprefix tailTrace_3347688
  have hstable : (prefixWord ++ tailWord_3347688).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347688).length < 2 ^ (prefixWord ++ tailWord_3347688).sum := by decide
  have hdescent : baseEnd_3347688 < baseStart_3347688 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347688) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347691 : List Nat := [1, 1, 1, 1, 2, 6, 1, 2, 8]
def baseStart_3347691 : Nat := 118140960795 + 3347691 * 2 ^ 59
def prefixEnd_3347691 : Nat := 4983230072969 + 3 ^ 40 * 3347691 * 2
def baseEnd_3347691 : Nat := 190997173970085208585195

theorem tailTrace_3347691 : CollatzResearch.WordTrace tailWord_3347691 prefixEnd_3347691 190997173970085208585195 := by
  unfold tailWord_3347691
  simp only [CollatzResearch.WordTrace]
  refine ⟨122100321714894721949354927, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81400214476596481299569951 122100321714894721949354927)
  ·
    refine ⟨183150482572342082924032391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122100321714894721949354927 183150482572342082924032391)
    ·
      refine ⟨274725723858513124386048587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183150482572342082924032391 274725723858513124386048587)
      ·
        refine ⟨412088585787769686579072881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274725723858513124386048587 412088585787769686579072881)
        ·
          refine ⟨309066439340827264934304661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412088585787769686579072881 309066439340827264934304661)
          ·
            refine ⟨14487489344101278043795531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 309066439340827264934304661 14487489344101278043795531)
            ·
              refine ⟨21731234016151917065693297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14487489344101278043795531 21731234016151917065693297)
              ·
                refine ⟨16298425512113937799269973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21731234016151917065693297 16298425512113937799269973)
                ·
                  refine ⟨190997173970085208585195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16298425512113937799269973 190997173970085208585195)
                  ·
                    rfl

theorem cell23_3347691_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 6, 1, 2, 8].length) (baseStart_3347691 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347691 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347691 prefixEnd_3347691 := by exact prefixLift 3347691
  have htrace : WordTrace (prefixWord ++ tailWord_3347691) baseStart_3347691 baseEnd_3347691 := by
    simpa [prefixWord, tailWord_3347691, baseEnd_3347691] using wordTrace_append hprefix tailTrace_3347691
  have hstable : (prefixWord ++ tailWord_3347691).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347691).length < 2 ^ (prefixWord ++ tailWord_3347691).sum := by decide
  have hdescent : baseEnd_3347691 < baseStart_3347691 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347691) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347735 : List Nat := [1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 3]
def baseStart_3347735 : Nat := 118140960795 + 3347735 * 2 ^ 59
def prefixEnd_3347735 : Nat := 4983230072969 + 3 ^ 40 * 3347735 * 2
def baseEnd_3347735 : Nat := 1718997158879564705116553

theorem tailTrace_3347735 : CollatzResearch.WordTrace tailWord_3347735 prefixEnd_3347735 1718997158879564705116553 := by
  unfold tailWord_3347735
  simp only [CollatzResearch.WordTrace]
  refine ⟨122101926526735317463956659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81401284351156878309304439 122101926526735317463956659)
  ·
    refine ⟨183152889790102976195934989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122101926526735317463956659 183152889790102976195934989)
    ·
      refine ⟨68682333671288616073475621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183152889790102976195934989 68682333671288616073475621)
      ·
        refine ⟨12877937563366615513776679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68682333671288616073475621 12877937563366615513776679)
        ·
          refine ⟨19316906345049923270665019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12877937563366615513776679 19316906345049923270665019)
          ·
            refine ⟨28975359517574884905997529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19316906345049923270665019 28975359517574884905997529)
            ·
              refine ⟨21731519638181163679498147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28975359517574884905997529 21731519638181163679498147)
              ·
                refine ⟨32597279457271745519247221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21731519638181163679498147 32597279457271745519247221)
                ·
                  refine ⟨3055994949119226142429427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32597279457271745519247221 3055994949119226142429427)
                  ·
                    refine ⟨4583992423678839213644141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3055994949119226142429427 4583992423678839213644141)
                    ·
                      refine ⟨1718997158879564705116553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4583992423678839213644141 1718997158879564705116553)
                      ·
                        rfl

theorem cell23_3347735_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 1, 2, 1, 5, 1, 3].length) (baseStart_3347735 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347735 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347735 prefixEnd_3347735 := by exact prefixLift 3347735
  have htrace : WordTrace (prefixWord ++ tailWord_3347735) baseStart_3347735 baseEnd_3347735 := by
    simpa [prefixWord, tailWord_3347735, baseEnd_3347735] using wordTrace_append hprefix tailTrace_3347735
  have hstable : (prefixWord ++ tailWord_3347735).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347735).length < 2 ^ (prefixWord ++ tailWord_3347735).sum := by decide
  have hdescent : baseEnd_3347735 < baseStart_3347735 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347735) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347762 : List Nat := [3, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2]
def baseStart_3347762 : Nat := 118140960795 + 3347762 * 2 ^ 59
def prefixEnd_3347762 : Nat := 4983230072969 + 3 ^ 40 * 3347762 * 2
def baseEnd_3347762 : Nat := 1719011022857236099478929

theorem tailTrace_3347762 : CollatzResearch.WordTrace tailWord_3347762 prefixEnd_3347762 1719011022857236099478929 := by
  unfold tailWord_3347762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30525727824409375268797385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81401940865091667383459693 30525727824409375268797385)
  ·
    refine ⟨22894295868307031451598039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30525727824409375268797385 22894295868307031451598039)
    ·
      refine ⟨34341443802460547177397059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22894295868307031451598039 34341443802460547177397059)
      ·
        refine ⟨51512165703690820766095589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34341443802460547177397059 51512165703690820766095589)
        ·
          refine ⟨9658531069442028893642923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51512165703690820766095589 9658531069442028893642923)
          ·
            refine ⟨14487796604163043340464385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9658531069442028893642923 14487796604163043340464385)
            ·
              refine ⟨10865847453122282505348289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14487796604163043340464385 10865847453122282505348289)
              ·
                refine ⟨8149385589841711879011217, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10865847453122282505348289 8149385589841711879011217)
                ·
                  refine ⟨6112039192381283909258413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149385589841711879011217 6112039192381283909258413)
                  ·
                    refine ⟨2292014697142981465971905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6112039192381283909258413 2292014697142981465971905)
                    ·
                      refine ⟨1719011022857236099478929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292014697142981465971905 1719011022857236099478929)
                      ·
                        rfl

theorem cell23_3347762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 1, 2, 2, 2, 3, 2].length) (baseStart_3347762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347762 prefixEnd_3347762 := by exact prefixLift 3347762
  have htrace : WordTrace (prefixWord ++ tailWord_3347762) baseStart_3347762 baseEnd_3347762 := by
    simpa [prefixWord, tailWord_3347762, baseEnd_3347762] using wordTrace_append hprefix tailTrace_3347762
  have hstable : (prefixWord ++ tailWord_3347762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347762).length < 2 ^ (prefixWord ++ tailWord_3347762).sum := by decide
  have hdescent : baseEnd_3347762 < baseStart_3347762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347785 : List Nat := [1, 2, 1, 1, 2, 3, 4, 3, 2, 4]
def baseStart_3347785 : Nat := 118140960795 + 3347785 * 2 ^ 59
def prefixEnd_3347785 : Nat := 4983230072969 + 3 ^ 40 * 3347785 * 2
def baseEnd_3347785 : Nat := 573007610970763169830441

theorem tailTrace_3347785 : CollatzResearch.WordTrace tailWord_3347785 prefixEnd_3347785 573007610970763169830441 := by
  unfold tailWord_3347785
  simp only [CollatzResearch.WordTrace]
  refine ⟨122103750176554176003276809, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81402500117702784002184539 122103750176554176003276809)
  ·
    refine ⟨91577812632415632002457607, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122103750176554176003276809 91577812632415632002457607)
    ·
      refine ⟨137366718948623448003686411, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91577812632415632002457607 137366718948623448003686411)
      ·
        refine ⟨206050078422935172005529617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137366718948623448003686411 206050078422935172005529617)
        ·
          refine ⟨154537558817201379004147213, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206050078422935172005529617 154537558817201379004147213)
          ·
            refine ⟨57951584556450517126555205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154537558817201379004147213 57951584556450517126555205)
            ·
              refine ⟨10865922104334471961229101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57951584556450517126555205 10865922104334471961229101)
              ·
                refine ⟨4074720789125426985460913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10865922104334471961229101 4074720789125426985460913)
                ·
                  refine ⟨3056040591844070239095685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4074720789125426985460913 3056040591844070239095685)
                  ·
                    refine ⟨573007610970763169830441, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3056040591844070239095685 573007610970763169830441)
                    ·
                      rfl

theorem cell23_3347785_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 3, 4, 3, 2, 4].length) (baseStart_3347785 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347785 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347785 prefixEnd_3347785 := by exact prefixLift 3347785
  have htrace : WordTrace (prefixWord ++ tailWord_3347785) baseStart_3347785 baseEnd_3347785 := by
    simpa [prefixWord, tailWord_3347785, baseEnd_3347785] using wordTrace_append hprefix tailTrace_3347785
  have hstable : (prefixWord ++ tailWord_3347785).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347785).length < 2 ^ (prefixWord ++ tailWord_3347785).sum := by decide
  have hdescent : baseEnd_3347785 < baseStart_3347785 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347785) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347792 : List Nat := [2, 1, 1, 1, 1, 5, 3, 2, 3, 2, 2]
def baseStart_3347792 : Nat := 118140960795 + 3347792 * 2 ^ 59
def prefixEnd_3347792 : Nat := 4983230072969 + 3 ^ 40 * 3347792 * 2
def baseEnd_3347792 : Nat := 1719026427276870982103791

theorem tailTrace_3347792 : CollatzResearch.WordTrace tailWord_3347792 prefixEnd_3347792 1719026427276870982103791 := by
  unfold tailWord_3347792
  simp only [CollatzResearch.WordTrace]
  refine ⟨61052002743764408099390815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81402670325019210799187753 61052002743764408099390815)
  ·
    refine ⟨91578004115646612149086223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61052002743764408099390815 91578004115646612149086223)
    ·
      refine ⟨137367006173469918223629335, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91578004115646612149086223 137367006173469918223629335)
      ·
        refine ⟨206050509260204877335444003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137367006173469918223629335 206050509260204877335444003)
        ·
          refine ⟨309075763890307316003166005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206050509260204877335444003 309075763890307316003166005)
          ·
            refine ⟨28975852864716310875296813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 309075763890307316003166005 28975852864716310875296813)
            ·
              refine ⟨10865944824268616578236305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28975852864716310875296813 10865944824268616578236305)
              ·
                refine ⟨8149458618201462433677229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10865944824268616578236305 8149458618201462433677229)
                ·
                  refine ⟨3056046981825548412628961, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8149458618201462433677229 3056046981825548412628961)
                  ·
                    refine ⟨2292035236369161309471721, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056046981825548412628961 2292035236369161309471721)
                    ·
                      refine ⟨1719026427276870982103791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292035236369161309471721 1719026427276870982103791)
                      ·
                        rfl

theorem cell23_3347792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 3, 2, 3, 2, 2].length) (baseStart_3347792 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347792 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347792 prefixEnd_3347792 := by exact prefixLift 3347792
  have htrace : WordTrace (prefixWord ++ tailWord_3347792) baseStart_3347792 baseEnd_3347792 := by
    simpa [prefixWord, tailWord_3347792, baseEnd_3347792] using wordTrace_append hprefix tailTrace_3347792
  have hstable : (prefixWord ++ tailWord_3347792).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347792).length < 2 ^ (prefixWord ++ tailWord_3347792).sum := by decide
  have hdescent : baseEnd_3347792 < baseStart_3347792 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347795 : List Nat := [1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 3]
def baseStart_3347795 : Nat := 118140960795 + 3347795 * 2 ^ 59
def prefixEnd_3347795 : Nat := 4983230072969 + 3 ^ 40 * 3347795 * 2
def baseEnd_3347795 : Nat := 1719027967718834470366277

theorem tailTrace_3347795 : CollatzResearch.WordTrace tailWord_3347795 prefixEnd_3347795 1719027967718834470366277 := by
  unfold tailWord_3347795
  simp only [CollatzResearch.WordTrace]
  refine ⟨122104114906517947711140839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81402743271011965140760559 122104114906517947711140839)
  ·
    refine ⟨183156172359776921566711259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122104114906517947711140839 183156172359776921566711259)
    ·
      refine ⟨274734258539665382350066889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183156172359776921566711259 274734258539665382350066889)
      ·
        refine ⟨206050693904749036762550167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274734258539665382350066889 206050693904749036762550167)
        ·
          refine ⟨309076040857123555143825251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206050693904749036762550167 309076040857123555143825251)
          ·
            refine ⟨463614061285685332715737877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309076040857123555143825251 463614061285685332715737877)
            ·
              refine ⟨21731909122766499971050213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 463614061285685332715737877 21731909122766499971050213)
              ·
                refine ⟨4074732960518718744571915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21731909122766499971050213 4074732960518718744571915)
                ·
                  refine ⟨6112099440778078116857873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074732960518718744571915 6112099440778078116857873)
                  ·
                    refine ⟨4584074580583558587643405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112099440778078116857873 4584074580583558587643405)
                    ·
                      refine ⟨1719027967718834470366277, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584074580583558587643405 1719027967718834470366277)
                      ·
                        rfl

theorem cell23_3347795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 6, 4, 1, 2, 3].length) (baseStart_3347795 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347795 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347795 prefixEnd_3347795 := by exact prefixLift 3347795
  have htrace : WordTrace (prefixWord ++ tailWord_3347795) baseStart_3347795 baseEnd_3347795 := by
    simpa [prefixWord, tailWord_3347795, baseEnd_3347795] using wordTrace_append hprefix tailTrace_3347795
  have hstable : (prefixWord ++ tailWord_3347795).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347795).length < 2 ^ (prefixWord ++ tailWord_3347795).sum := by decide
  have hdescent : baseEnd_3347795 < baseStart_3347795 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347812 : List Nat := [2, 3, 1, 1, 3, 3, 1, 3, 1, 2, 3]
def baseStart_3347812 : Nat := 118140960795 + 3347812 * 2 ^ 59
def prefixEnd_3347812 : Nat := 4983230072969 + 3 ^ 40 * 3347812 * 2
def baseEnd_3347812 : Nat := 1719036696889960903853699

theorem tailTrace_3347812 : CollatzResearch.WordTrace tailWord_3347812 prefixEnd_3347812 1719036696889960903853699 := by
  unfold tailWord_3347812
  simp only [CollatzResearch.WordTrace]
  refine ⟨61052367473728179807254845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81403156631637573076339793 61052367473728179807254845)
  ·
    refine ⟨22894637802648067427720567, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61052367473728179807254845 22894637802648067427720567)
    ·
      refine ⟨34341956703972101141580851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22894637802648067427720567 34341956703972101141580851)
      ·
        refine ⟨51512935055958151712371277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34341956703972101141580851 51512935055958151712371277)
        ·
          refine ⟨19317350645984306892139229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51512935055958151712371277 19317350645984306892139229)
          ·
            refine ⟨7244006492244115084552211, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19317350645984306892139229 7244006492244115084552211)
            ·
              refine ⟨10866009738366172626828317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244006492244115084552211 10866009738366172626828317)
              ·
                refine ⟨4074753651887314735060619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10866009738366172626828317 4074753651887314735060619)
                ·
                  refine ⟨6112130477830972102590929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074753651887314735060619 6112130477830972102590929)
                  ·
                    refine ⟨4584097858373229076943197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112130477830972102590929 4584097858373229076943197)
                    ·
                      refine ⟨1719036696889960903853699, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584097858373229076943197 1719036696889960903853699)
                      ·
                        rfl

theorem cell23_3347812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 3, 1, 3, 1, 2, 3].length) (baseStart_3347812 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347812 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347812 prefixEnd_3347812 := by exact prefixLift 3347812
  have htrace : WordTrace (prefixWord ++ tailWord_3347812) baseStart_3347812 baseEnd_3347812 := by
    simpa [prefixWord, tailWord_3347812, baseEnd_3347812] using wordTrace_append hprefix tailTrace_3347812
  have hstable : (prefixWord ++ tailWord_3347812).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347812).length < 2 ^ (prefixWord ++ tailWord_3347812).sum := by decide
  have hdescent : baseEnd_3347812 < baseStart_3347812 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347869 : List Nat := [1, 4, 2, 1, 3, 1, 2, 3, 1, 3, 2]
def baseStart_3347869 : Nat := 118140960795 + 3347869 * 2 ^ 59
def prefixEnd_3347869 : Nat := 4983230072969 + 3 ^ 40 * 3347869 * 2
def baseEnd_3347869 : Nat := 1719065965287267180840937

theorem tailTrace_3347869 : CollatzResearch.WordTrace tailWord_3347869 prefixEnd_3347869 1719065965287267180840937 := by
  unfold tailWord_3347869
  simp only [CollatzResearch.WordTrace]
  refine ⟨122106813908249858349334661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81404542605499905566223107 122106813908249858349334661)
  ·
    refine ⟨22895027607796848440500249, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122106813908249858349334661 22895027607796848440500249)
    ·
      refine ⟨17171270705847636330375187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22895027607796848440500249 17171270705847636330375187)
      ·
        refine ⟨25756906058771454495562781, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171270705847636330375187 25756906058771454495562781)
        ·
          refine ⟨9658839772039295435836043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25756906058771454495562781 9658839772039295435836043)
          ·
            refine ⟨14488259658058943153754065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9658839772039295435836043 14488259658058943153754065)
            ·
              refine ⟨10866194743544207365315549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14488259658058943153754065 10866194743544207365315549)
              ·
                refine ⟨4074823028829077761993331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10866194743544207365315549 4074823028829077761993331)
                ·
                  refine ⟨6112234543243616642989997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4074823028829077761993331 6112234543243616642989997)
                  ·
                    refine ⟨2292087953716356241121249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6112234543243616642989997 2292087953716356241121249)
                    ·
                      refine ⟨1719065965287267180840937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292087953716356241121249 1719065965287267180840937)
                      ·
                        rfl

theorem cell23_3347869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 3, 1, 2, 3, 1, 3, 2].length) (baseStart_3347869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347869 prefixEnd_3347869 := by exact prefixLift 3347869
  have htrace : WordTrace (prefixWord ++ tailWord_3347869) baseStart_3347869 baseEnd_3347869 := by
    simpa [prefixWord, tailWord_3347869, baseEnd_3347869] using wordTrace_append hprefix tailTrace_3347869
  have hstable : (prefixWord ++ tailWord_3347869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347869).length < 2 ^ (prefixWord ++ tailWord_3347869).sum := by decide
  have hdescent : baseEnd_3347869 < baseStart_3347869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347888 : List Nat := [2, 1, 1, 1, 2, 1, 1, 7, 7]
def baseStart_3347888 : Nat := 118140960795 + 3347888 * 2 ^ 59
def prefixEnd_3347888 : Nat := 4983230072969 + 3 ^ 40 * 3347888 * 2
def baseEnd_3347888 : Nat := 191008413491078067389261

theorem tailTrace_3347888 : CollatzResearch.WordTrace tailWord_3347888 prefixEnd_3347888 191008413491078067389261 := by
  unfold tailWord_3347888
  simp only [CollatzResearch.WordTrace]
  refine ⟨61053753447590512297138159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81405004596787349729517545 61053753447590512297138159)
  ·
    refine ⟨91580630171385768445707239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61053753447590512297138159 91580630171385768445707239)
    ·
      refine ⟨137370945257078652668560859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91580630171385768445707239 137370945257078652668560859)
      ·
        refine ⟨206056417885617979002841289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137370945257078652668560859 206056417885617979002841289)
        ·
          refine ⟨154542313414213484252130967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206056417885617979002841289 154542313414213484252130967)
          ·
            refine ⟨231813470121320226378196451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154542313414213484252130967 231813470121320226378196451)
            ·
              refine ⟨347720205181980339567294677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231813470121320226378196451 347720205181980339567294677)
              ·
                refine ⟨8149692308952664208608469, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 347720205181980339567294677 8149692308952664208608469)
                ·
                  refine ⟨191008413491078067389261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8149692308952664208608469 191008413491078067389261)
                  ·
                    rfl

theorem cell23_3347888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 7, 7].length) (baseStart_3347888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347888 prefixEnd_3347888 := by exact prefixLift 3347888
  have htrace : WordTrace (prefixWord ++ tailWord_3347888) baseStart_3347888 baseEnd_3347888 := by
    simpa [prefixWord, tailWord_3347888, baseEnd_3347888] using wordTrace_append hprefix tailTrace_3347888
  have hstable : (prefixWord ++ tailWord_3347888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347888).length < 2 ^ (prefixWord ++ tailWord_3347888).sum := by decide
  have hdescent : baseEnd_3347888 < baseStart_3347888 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347935 : List Nat := [1, 1, 2, 3, 3, 1, 1, 4, 2, 5]
def baseStart_3347935 : Nat := 118140960795 + 3347935 * 2 ^ 59
def prefixEnd_3347935 : Nat := 4983230072969 + 3 ^ 40 * 3347935 * 2
def baseEnd_3347935 : Nat := 573033285003487974205211

theorem tailTrace_3347935 : CollatzResearch.WordTrace tailWord_3347935 prefixEnd_3347935 573033285003487974205211 := by
  unfold tailWord_3347935
  simp only [CollatzResearch.WordTrace]
  refine ⟨122109221126010751621237259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81406147417340501080824839 122109221126010751621237259)
  ·
    refine ⟨183163831689016127431855889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122109221126010751621237259 183163831689016127431855889)
    ·
      refine ⟨137372873766762095573891917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183163831689016127431855889 137372873766762095573891917)
      ·
        refine ⟨51514827662535785840209469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137372873766762095573891917 51514827662535785840209469)
        ·
          refine ⟨19318060373450919690078551, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51514827662535785840209469 19318060373450919690078551)
          ·
            refine ⟨28977090560176379535117827, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19318060373450919690078551 28977090560176379535117827)
            ·
              refine ⟨43465635840264569302676741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28977090560176379535117827 43465635840264569302676741)
              ·
                refine ⟨8149806720049606744251889, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43465635840264569302676741 8149806720049606744251889)
                ·
                  refine ⟨6112355040037205058188917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149806720049606744251889 6112355040037205058188917)
                  ·
                    refine ⟨573033285003487974205211, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6112355040037205058188917 573033285003487974205211)
                    ·
                      rfl

theorem cell23_3347935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 1, 1, 4, 2, 5].length) (baseStart_3347935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347935 prefixEnd_3347935 := by exact prefixLift 3347935
  have htrace : WordTrace (prefixWord ++ tailWord_3347935) baseStart_3347935 baseEnd_3347935 := by
    simpa [prefixWord, tailWord_3347935, baseEnd_3347935] using wordTrace_append hprefix tailTrace_3347935
  have hstable : (prefixWord ++ tailWord_3347935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347935).length < 2 ^ (prefixWord ++ tailWord_3347935).sum := by decide
  have hdescent : baseEnd_3347935 < baseStart_3347935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347939 : List Nat := [1, 1, 1, 6, 2, 1, 4, 2, 5]
def baseStart_3347939 : Nat := 118140960795 + 3347939 * 2 ^ 59
def prefixEnd_3347939 : Nat := 4983230072969 + 3 ^ 40 * 3347939 * 2
def baseEnd_3347939 : Nat := 191011323214786878551735

theorem tailTrace_3347939 : CollatzResearch.WordTrace tailWord_3347939 prefixEnd_3347939 191011323214786878551735 := by
  unfold tailWord_3347939
  simp only [CollatzResearch.WordTrace]
  refine ⟨122109367017996260304382871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81406244678664173536255247 122109367017996260304382871)
  ·
    refine ⟨183164050526994390456574307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122109367017996260304382871 183164050526994390456574307)
    ·
      refine ⟨274746075790491585684861461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183164050526994390456574307 274746075790491585684861461)
      ·
        refine ⟨12878722302679293078977881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 274746075790491585684861461 12878722302679293078977881)
        ·
          refine ⟨9659041727009469809233411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12878722302679293078977881 9659041727009469809233411)
          ·
            refine ⟨14488562590514204713850117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9659041727009469809233411 14488562590514204713850117)
            ·
              refine ⟨2716605485721413383846897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14488562590514204713850117 2716605485721413383846897)
              ·
                refine ⟨2037454114291060037885173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2716605485721413383846897 2037454114291060037885173)
                ·
                  refine ⟨191011323214786878551735, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037454114291060037885173 191011323214786878551735)
                  ·
                    rfl

theorem cell23_3347939_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 2, 1, 4, 2, 5].length) (baseStart_3347939 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347939 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347939 prefixEnd_3347939 := by exact prefixLift 3347939
  have htrace : WordTrace (prefixWord ++ tailWord_3347939) baseStart_3347939 baseEnd_3347939 := by
    simpa [prefixWord, tailWord_3347939, baseEnd_3347939] using wordTrace_append hprefix tailTrace_3347939
  have hstable : (prefixWord ++ tailWord_3347939).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347939).length < 2 ^ (prefixWord ++ tailWord_3347939).sum := by decide
  have hdescent : baseEnd_3347939 < baseStart_3347939 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347939) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347949 : List Nat := [1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 3]
def baseStart_3347949 : Nat := 118140960795 + 3347949 * 2 ^ 59
def prefixEnd_3347949 : Nat := 4983230072969 + 3 ^ 40 * 3347949 * 2
def baseEnd_3347949 : Nat := 1719107043739626867840569

theorem tailTrace_3347949 : CollatzResearch.WordTrace tailWord_3347949 prefixEnd_3347949 1719107043739626867840569 := by
  unfold tailWord_3347949
  simp only [CollatzResearch.WordTrace]
  refine ⟨122109731747960032012246901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81406487831973354674831267 122109731747960032012246901)
  ·
    refine ⟨11447787351371253001148147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122109731747960032012246901 11447787351371253001148147)
    ·
      refine ⟨17171681027056879501722221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11447787351371253001148147 17171681027056879501722221)
      ·
        refine ⟨6439380385146329813145833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17171681027056879501722221 6439380385146329813145833)
        ·
          refine ⟨4829535288859747359859375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6439380385146329813145833 4829535288859747359859375)
          ·
            refine ⟨7244302933289621039789063, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829535288859747359859375 7244302933289621039789063)
            ·
              refine ⟨10866454399934431559683595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244302933289621039789063 10866454399934431559683595)
              ·
                refine ⟨16299681599901647339525393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10866454399934431559683595 16299681599901647339525393)
                ·
                  refine ⟨12224761199926235504644045, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16299681599901647339525393 12224761199926235504644045)
                  ·
                    refine ⟨4584285449972338314241517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12224761199926235504644045 4584285449972338314241517)
                    ·
                      refine ⟨1719107043739626867840569, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584285449972338314241517 1719107043739626867840569)
                      ·
                        rfl

theorem cell23_3347949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 1, 1, 1, 2, 3, 3].length) (baseStart_3347949 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347949 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347949 prefixEnd_3347949 := by exact prefixLift 3347949
  have htrace : WordTrace (prefixWord ++ tailWord_3347949) baseStart_3347949 baseEnd_3347949 := by
    simpa [prefixWord, tailWord_3347949, baseEnd_3347949] using wordTrace_append hprefix tailTrace_3347949
  have hstable : (prefixWord ++ tailWord_3347949).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347949).length < 2 ^ (prefixWord ++ tailWord_3347949).sum := by decide
  have hdescent : baseEnd_3347949 < baseStart_3347949 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347969 : List Nat := [1, 2, 4, 1, 4, 2, 1, 1, 2, 5]
def baseStart_3347969 : Nat := 118140960795 + 3347969 * 2 ^ 59
def prefixEnd_3347969 : Nat := 4983230072969 + 3 ^ 40 * 3347969 * 2
def baseEnd_3347969 : Nat := 573039104450905596530159

theorem tailTrace_3347969 : CollatzResearch.WordTrace tailWord_3347969 prefixEnd_3347969 573039104450905596530159 := by
  unfold tailWord_3347969
  simp only [CollatzResearch.WordTrace]
  refine ⟨122110461207887575427974961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81406974138591716951983307 122110461207887575427974961)
  ·
    refine ⟨91582845905915681570981221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122110461207887575427974961 91582845905915681570981221)
    ·
      refine ⟨17171783607359190294558979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91582845905915681570981221 17171783607359190294558979)
      ·
        refine ⟨25757675411038785441838469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17171783607359190294558979 25757675411038785441838469)
        ·
          refine ⟨4829564139569772270344713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25757675411038785441838469 4829564139569772270344713)
          ·
            refine ⟨3622173104677329202758535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4829564139569772270344713 3622173104677329202758535)
            ·
              refine ⟨5433259657015993804137803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3622173104677329202758535 5433259657015993804137803)
              ·
                refine ⟨8149889485523990706206705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433259657015993804137803 8149889485523990706206705)
                ·
                  refine ⟨6112417114142993029655029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8149889485523990706206705 6112417114142993029655029)
                  ·
                    refine ⟨573039104450905596530159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6112417114142993029655029 573039104450905596530159)
                    ·
                      rfl

theorem cell23_3347969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 2, 1, 1, 2, 5].length) (baseStart_3347969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347969 prefixEnd_3347969 := by exact prefixLift 3347969
  have htrace : WordTrace (prefixWord ++ tailWord_3347969) baseStart_3347969 baseEnd_3347969 := by
    simpa [prefixWord, tailWord_3347969, baseEnd_3347969] using wordTrace_append hprefix tailTrace_3347969
  have hstable : (prefixWord ++ tailWord_3347969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347969).length < 2 ^ (prefixWord ++ tailWord_3347969).sum := by decide
  have hdescent : baseEnd_3347969 < baseStart_3347969 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3347999 : List Nat := [1, 1, 2, 4, 1, 1, 4, 4, 1, 4]
def baseStart_3347999 : Nat := 118140960795 + 3347999 * 2 ^ 59
def prefixEnd_3347999 : Nat := 4983230072969 + 3 ^ 40 * 3347999 * 2
def baseEnd_3347999 : Nat := 573044239257450557405113

theorem tailTrace_3347999 : CollatzResearch.WordTrace tailWord_3347999 prefixEnd_3347999 573044239257450557405113 := by
  unfold tailWord_3347999
  simp only [CollatzResearch.WordTrace]
  refine ⟨122111555397778890551567051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81407703598519260367711367 122111555397778890551567051)
  ·
    refine ⟨183167333096668335827350577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122111555397778890551567051 183167333096668335827350577)
    ·
      refine ⟨137375499822501251870512933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183167333096668335827350577 137375499822501251870512933)
      ·
        refine ⟨25757906216718984725721175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137375499822501251870512933 25757906216718984725721175)
        ·
          refine ⟨38636859325078477088581763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25757906216718984725721175 38636859325078477088581763)
          ·
            refine ⟨57955288987617715632872645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38636859325078477088581763 57955288987617715632872645)
            ·
              refine ⟨10866616685178321681163621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57955288987617715632872645 10866616685178321681163621)
              ·
                refine ⟨2037490628470935315218179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10866616685178321681163621 2037490628470935315218179)
                ·
                  refine ⟨3056235942706402972827269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2037490628470935315218179 3056235942706402972827269)
                  ·
                    refine ⟨573044239257450557405113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3056235942706402972827269 573044239257450557405113)
                    ·
                      rfl

theorem cell23_3347999_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 4, 4, 1, 4].length) (baseStart_3347999 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3347999 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3347999 prefixEnd_3347999 := by exact prefixLift 3347999
  have htrace : WordTrace (prefixWord ++ tailWord_3347999) baseStart_3347999 baseEnd_3347999 := by
    simpa [prefixWord, tailWord_3347999, baseEnd_3347999] using wordTrace_append hprefix tailTrace_3347999
  have hstable : (prefixWord ++ tailWord_3347999).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3347999).length < 2 ^ (prefixWord ++ tailWord_3347999).sum := by decide
  have hdescent : baseEnd_3347999 < baseStart_3347999 := by decide
  rcases family_descends (prefixWord ++ tailWord_3347999) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348042 : List Nat := [3, 1, 2, 1, 1, 3, 1, 5, 1, 5]
def baseStart_3348042 : Nat := 118140960795 + 3348042 * 2 ^ 59
def prefixEnd_3348042 : Nat := 4983230072969 + 3 ^ 40 * 3348042 * 2
def baseEnd_3348042 : Nat := 573051599146831667992547

theorem tailTrace_3348042 : CollatzResearch.WordTrace tailWord_3348042 prefixEnd_3348042 573051599146831667992547 := by
  unfold tailWord_3348042
  simp only [CollatzResearch.WordTrace]
  refine ⟨30528280934155777223845595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81408749157748739263588253 30528280934155777223845595)
  ·
    refine ⟨45792421401233665835768393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30528280934155777223845595 45792421401233665835768393)
    ·
      refine ⟨34344316050925249376826295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45792421401233665835768393 34344316050925249376826295)
      ·
        refine ⟨51516474076387874065239443, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34344316050925249376826295 51516474076387874065239443)
        ·
          refine ⟨77274711114581811097859165, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51516474076387874065239443 77274711114581811097859165)
          ·
            refine ⟨28978016667968179161697187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77274711114581811097859165 28978016667968179161697187)
            ·
              refine ⟨43467025001952268742545781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28978016667968179161697187 43467025001952268742545781)
              ·
                refine ⟨4075033593933025194613667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43467025001952268742545781 4075033593933025194613667)
                ·
                  refine ⟨6112550390899537791920501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075033593933025194613667 6112550390899537791920501)
                  ·
                    refine ⟨573051599146831667992547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6112550390899537791920501 573051599146831667992547)
                    ·
                      rfl

theorem cell23_3348042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_3348042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348042 prefixEnd_3348042 := by exact prefixLift 3348042
  have htrace : WordTrace (prefixWord ++ tailWord_3348042) baseStart_3348042 baseEnd_3348042 := by
    simpa [prefixWord, tailWord_3348042, baseEnd_3348042] using wordTrace_append hprefix tailTrace_3348042
  have hstable : (prefixWord ++ tailWord_3348042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348042).length < 2 ^ (prefixWord ++ tailWord_3348042).sum := by decide
  have hdescent : baseEnd_3348042 < baseStart_3348042 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348049 : List Nat := [1, 2, 2, 1, 3, 2, 3, 2, 2, 3, 2]
def baseStart_3348049 : Nat := 118140960795 + 3348049 * 2 ^ 59
def prefixEnd_3348049 : Nat := 4983230072969 + 3 ^ 40 * 3348049 * 2
def baseEnd_3348049 : Nat := 1719158391805076476590109

theorem tailTrace_3348049 : CollatzResearch.WordTrace tailWord_3348049 prefixEnd_3348049 1719158391805076476590109 := by
  unfold tailWord_3348049
  simp only [CollatzResearch.WordTrace]
  refine ⟨122113379047597749090887201, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81408919365065166060591467 122113379047597749090887201)
  ·
    refine ⟨91585034285698311818165401, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122113379047597749090887201 91585034285698311818165401)
    ·
      refine ⟨68688775714273733863624051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91585034285698311818165401 68688775714273733863624051)
      ·
        refine ⟨103033163571410600795436077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68688775714273733863624051 103033163571410600795436077)
        ·
          refine ⟨38637436339278975298288529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103033163571410600795436077 38637436339278975298288529)
          ·
            refine ⟨28978077254459231473716397, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38637436339278975298288529 28978077254459231473716397)
            ·
              refine ⟨10866778970422211802643649, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28978077254459231473716397 10866778970422211802643649)
              ·
                refine ⟨8150084227816658851982737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10866778970422211802643649 8150084227816658851982737)
                ·
                  refine ⟨6112563170862494138987053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8150084227816658851982737 6112563170862494138987053)
                  ·
                    refine ⟨2292211189073435302120145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6112563170862494138987053 2292211189073435302120145)
                    ·
                      refine ⟨1719158391805076476590109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292211189073435302120145 1719158391805076476590109)
                      ·
                        rfl

theorem cell23_3348049_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 2, 3, 2, 2, 3, 2].length) (baseStart_3348049 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348049 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348049 prefixEnd_3348049 := by exact prefixLift 3348049
  have htrace : WordTrace (prefixWord ++ tailWord_3348049) baseStart_3348049 baseEnd_3348049 := by
    simpa [prefixWord, tailWord_3348049, baseEnd_3348049] using wordTrace_append hprefix tailTrace_3348049
  have hstable : (prefixWord ++ tailWord_3348049).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348049).length < 2 ^ (prefixWord ++ tailWord_3348049).sum := by decide
  have hdescent : baseEnd_3348049 < baseStart_3348049 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348049) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348079 : List Nat := [1, 1, 2, 1, 3, 2, 1, 3, 5, 2, 2]
def baseStart_3348079 : Nat := 118140960795 + 3348079 * 2 ^ 59
def prefixEnd_3348079 : Nat := 4983230072969 + 3 ^ 40 * 3348079 * 2
def baseEnd_3348079 : Nat := 1719173796224711359214971

theorem tailTrace_3348079 : CollatzResearch.WordTrace tailWord_3348079 prefixEnd_3348079 1719173796224711359214971 := by
  unfold tailWord_3348079
  simp only [CollatzResearch.WordTrace]
  refine ⟨122114473237489064214479291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81409648824992709476319527 122114473237489064214479291)
  ·
    refine ⟨183171709856233596321718937, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122114473237489064214479291 183171709856233596321718937)
    ·
      refine ⟨137378782392175197241289203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183171709856233596321718937 137378782392175197241289203)
      ·
        refine ⟨206068173588262795861933805, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137378782392175197241289203 206068173588262795861933805)
        ·
          refine ⟨77275565095598548448225177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206068173588262795861933805 77275565095598548448225177)
          ·
            refine ⟨57956673821698911336168883, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77275565095598548448225177 57956673821698911336168883)
            ·
              refine ⟨86935010732548367004253325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57956673821698911336168883 86935010732548367004253325)
              ·
                refine ⟨32600629024705637626594997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86935010732548367004253325 32600629024705637626594997)
                ·
                  refine ⟨3056308971066153527493281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 32600629024705637626594997 3056308971066153527493281)
                  ·
                    refine ⟨2292231728299615145619961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056308971066153527493281 2292231728299615145619961)
                    ·
                      refine ⟨1719173796224711359214971, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292231728299615145619961 1719173796224711359214971)
                      ·
                        rfl

theorem cell23_3348079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 1, 3, 5, 2, 2].length) (baseStart_3348079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348079 prefixEnd_3348079 := by exact prefixLift 3348079
  have htrace : WordTrace (prefixWord ++ tailWord_3348079) baseStart_3348079 baseEnd_3348079 := by
    simpa [prefixWord, tailWord_3348079, baseEnd_3348079] using wordTrace_append hprefix tailTrace_3348079
  have hstable : (prefixWord ++ tailWord_3348079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348079).length < 2 ^ (prefixWord ++ tailWord_3348079).sum := by decide
  have hdescent : baseEnd_3348079 < baseStart_3348079 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348106 : List Nat := [3, 1, 2, 3, 2, 2, 2, 2, 2, 4]
def baseStart_3348106 : Nat := 118140960795 + 3348106 * 2 ^ 59
def prefixEnd_3348106 : Nat := 4983230072969 + 3 ^ 40 * 3348106 * 2
def baseEnd_3348106 : Nat := 573062553400794251192449

theorem tailTrace_3348106 : CollatzResearch.WordTrace tailWord_3348106 prefixEnd_3348106 573062553400794251192449 := by
  unfold tailWord_3348106
  simp only [CollatzResearch.WordTrace]
  refine ⟨30528864502097811956428043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81410305338927498550474781 30528864502097811956428043)
  ·
    refine ⟨45793296753146717934642065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30528864502097811956428043 45793296753146717934642065)
    ·
      refine ⟨34344972564860038450981549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45793296753146717934642065 34344972564860038450981549)
      ·
        refine ⟨12879364711822514419118081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34344972564860038450981549 12879364711822514419118081)
        ·
          refine ⟨9659523533866885814338561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12879364711822514419118081 9659523533866885814338561)
          ·
            refine ⟨7244642650400164360753921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9659523533866885814338561 7244642650400164360753921)
            ·
              refine ⟨5433481987800123270565441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7244642650400164360753921 5433481987800123270565441)
              ·
                refine ⟨4075111490850092452924081, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5433481987800123270565441 4075111490850092452924081)
                ·
                  refine ⟨3056333618137569339693061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075111490850092452924081 3056333618137569339693061)
                  ·
                    refine ⟨573062553400794251192449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3056333618137569339693061 573062553400794251192449)
                    ·
                      rfl

theorem cell23_3348106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_3348106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348106 prefixEnd_3348106 := by exact prefixLift 3348106
  have htrace : WordTrace (prefixWord ++ tailWord_3348106) baseStart_3348106 baseEnd_3348106 := by
    simpa [prefixWord, tailWord_3348106, baseEnd_3348106] using wordTrace_append hprefix tailTrace_3348106
  have hstable : (prefixWord ++ tailWord_3348106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348106).length < 2 ^ (prefixWord ++ tailWord_3348106).sum := by decide
  have hdescent : baseEnd_3348106 < baseStart_3348106 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348126 : List Nat := [4, 3, 1, 1, 1, 3, 2, 1, 1, 2, 4]
def baseStart_3348126 : Nat := 118140960795 + 3348126 * 2 ^ 59
def prefixEnd_3348126 : Nat := 4983230072969 + 3 ^ 40 * 3348126 * 2
def baseEnd_3348126 : Nat := 1719197929815472675327255

theorem tailTrace_3348126 : CollatzResearch.WordTrace tailWord_3348126 prefixEnd_3348126 1719197929815472675327255 := by
  unfold tailWord_3348126
  simp only [CollatzResearch.WordTrace]
  refine ⟨15264523433539848905180029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81410791645545860827626821 15264523433539848905180029)
  ·
    refine ⟨5724196287577443339442511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15264523433539848905180029 5724196287577443339442511)
    ·
      refine ⟨8586294431366165009163767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5724196287577443339442511 8586294431366165009163767)
      ·
        refine ⟨12879441647049247513745651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8586294431366165009163767 12879441647049247513745651)
        ·
          refine ⟨19319162470573871270618477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12879441647049247513745651 19319162470573871270618477)
          ·
            refine ⟨7244685926465201726481929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19319162470573871270618477 7244685926465201726481929)
            ·
              refine ⟨5433514444848901294861447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7244685926465201726481929 5433514444848901294861447)
              ·
                refine ⟨8150271667273351942292171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433514444848901294861447 8150271667273351942292171)
                ·
                  refine ⟨12225407500910027913438257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150271667273351942292171 12225407500910027913438257)
                  ·
                    refine ⟨9169055625682520935078693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12225407500910027913438257 9169055625682520935078693)
                    ·
                      refine ⟨1719197929815472675327255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9169055625682520935078693 1719197929815472675327255)
                      ·
                        rfl

theorem cell23_3348126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 3, 2, 1, 1, 2, 4].length) (baseStart_3348126 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348126 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348126 prefixEnd_3348126 := by exact prefixLift 3348126
  have htrace : WordTrace (prefixWord ++ tailWord_3348126) baseStart_3348126 baseEnd_3348126 := by
    simpa [prefixWord, tailWord_3348126, baseEnd_3348126] using wordTrace_append hprefix tailTrace_3348126
  have hstable : (prefixWord ++ tailWord_3348126).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348126).length < 2 ^ (prefixWord ++ tailWord_3348126).sum := by decide
  have hdescent : baseEnd_3348126 < baseStart_3348126 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348129 : List Nat := [1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 3]
def baseStart_3348129 : Nat := 118140960795 + 3348129 * 2 ^ 59
def prefixEnd_3348129 : Nat := 4983230072969 + 3 ^ 40 * 3348129 * 2
def baseEnd_3348129 : Nat := 1719199470257436163589741

theorem tailTrace_3348129 : CollatzResearch.WordTrace tailWord_3348129 prefixEnd_3348129 1719199470257436163589741 := by
  unfold tailWord_3348129
  simp only [CollatzResearch.WordTrace]
  refine ⟨122116296887307922753799441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81410864591538615169199627 122116296887307922753799441)
  ·
    refine ⟨91587222665480942065349581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122116296887307922753799441 91587222665480942065349581)
    ·
      refine ⟨34345208499555353274506093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91587222665480942065349581 34345208499555353274506093)
      ·
        refine ⟨12879453187333257477939785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34345208499555353274506093 12879453187333257477939785)
        ·
          refine ⟨9659589890499943108454839, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12879453187333257477939785 9659589890499943108454839)
          ·
            refine ⟨14489384835749914662682259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9659589890499943108454839 14489384835749914662682259)
            ·
              refine ⟨21734077253624871994023389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14489384835749914662682259 21734077253624871994023389)
              ·
                refine ⟨8150278970109326997758771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21734077253624871994023389 8150278970109326997758771)
                ·
                  refine ⟨12225418455163990496638157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150278970109326997758771 12225418455163990496638157)
                  ·
                    refine ⟨4584531920686496436239309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12225418455163990496638157 4584531920686496436239309)
                    ·
                      refine ⟨1719199470257436163589741, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584531920686496436239309 1719199470257436163589741)
                      ·
                        rfl

theorem cell23_3348129_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_3348129 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348129 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348129 prefixEnd_3348129 := by exact prefixLift 3348129
  have htrace : WordTrace (prefixWord ++ tailWord_3348129) baseStart_3348129 baseEnd_3348129 := by
    simpa [prefixWord, tailWord_3348129, baseEnd_3348129] using wordTrace_append hprefix tailTrace_3348129
  have hstable : (prefixWord ++ tailWord_3348129).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348129).length < 2 ^ (prefixWord ++ tailWord_3348129).sum := by decide
  have hdescent : baseEnd_3348129 < baseStart_3348129 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348129) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348130 : List Nat := [3, 3, 1, 4, 1, 1, 1, 2, 3, 2, 2]
def baseStart_3348130 : Nat := 118140960795 + 3348130 * 2 ^ 59
def prefixEnd_3348130 : Nat := 4983230072969 + 3 ^ 40 * 3348130 * 2
def baseEnd_3348130 : Nat := 1719199983738090659677237

theorem tailTrace_3348130 : CollatzResearch.WordTrace tailWord_3348130 prefixEnd_3348130 1719199983738090659677237 := by
  unfold tailWord_3348130
  simp only [CollatzResearch.WordTrace]
  refine ⟨30529083340076074981146461, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81410888906869533283057229 30529083340076074981146461)
  ·
    refine ⟨11448406252528528117929923, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30529083340076074981146461 11448406252528528117929923)
    ·
      refine ⟨17172609378792792176894885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448406252528528117929923 17172609378792792176894885)
      ·
        refine ⟨3219864258523648533167791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 17172609378792792176894885 3219864258523648533167791)
        ·
          refine ⟨4829796387785472799751687, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3219864258523648533167791 4829796387785472799751687)
          ·
            refine ⟨7244694581678209199627531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4829796387785472799751687 7244694581678209199627531)
            ·
              refine ⟨10867041872517313799441297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7244694581678209199627531 10867041872517313799441297)
              ·
                refine ⟨8150281404387985349580973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10867041872517313799441297 8150281404387985349580973)
                ·
                  refine ⟨3056355526645494506092865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8150281404387985349580973 3056355526645494506092865)
                  ·
                    refine ⟨2292266644984120879569649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056355526645494506092865 2292266644984120879569649)
                    ·
                      refine ⟨1719199983738090659677237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292266644984120879569649 1719199983738090659677237)
                      ·
                        rfl

theorem cell23_3348130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 4, 1, 1, 1, 2, 3, 2, 2].length) (baseStart_3348130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348130 prefixEnd_3348130 := by exact prefixLift 3348130
  have htrace : WordTrace (prefixWord ++ tailWord_3348130) baseStart_3348130 baseEnd_3348130 := by
    simpa [prefixWord, tailWord_3348130, baseEnd_3348130] using wordTrace_append hprefix tailTrace_3348130
  have hstable : (prefixWord ++ tailWord_3348130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348130).length < 2 ^ (prefixWord ++ tailWord_3348130).sum := by decide
  have hdescent : baseEnd_3348130 < baseStart_3348130 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348150 : List Nat := [5, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3]
def baseStart_3348150 : Nat := 118140960795 + 3348150 * 2 ^ 59
def prefixEnd_3348150 : Nat := 4983230072969 + 3 ^ 40 * 3348150 * 2
def baseEnd_3348150 : Nat := 1719210253351180581427145

theorem tailTrace_3348150 : CollatzResearch.WordTrace tailWord_3348150 prefixEnd_3348150 1719210253351180581427145 := by
  unfold tailWord_3348150
  simp only [CollatzResearch.WordTrace]
  refine ⟨7632316426264490208769619, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81411375213487895560209269 7632316426264490208769619)
  ·
    refine ⟨11448474639396735313154429, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7632316426264490208769619 11448474639396735313154429)
    ·
      refine ⟨4293177989773775742432911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11448474639396735313154429 4293177989773775742432911)
      ·
        refine ⟨6439766984660663613649367, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293177989773775742432911 6439766984660663613649367)
        ·
          refine ⟨9659650476990995420474051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439766984660663613649367 9659650476990995420474051)
          ·
            refine ⟨14489475715486493130711077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9659650476990995420474051 14489475715486493130711077)
            ·
              refine ⟨2716776696653717462008327, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14489475715486493130711077 2716776696653717462008327)
              ·
                refine ⟨4075165044980576193012491, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716776696653717462008327 4075165044980576193012491)
                ·
                  refine ⟨6112747567470864289518737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4075165044980576193012491 6112747567470864289518737)
                  ·
                    refine ⟨4584560675603148217139053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112747567470864289518737 4584560675603148217139053)
                    ·
                      refine ⟨1719210253351180581427145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584560675603148217139053 1719210253351180581427145)
                      ·
                        rfl

theorem cell23_3348150_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 1, 1, 4, 1, 1, 2, 3].length) (baseStart_3348150 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348150 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348150 prefixEnd_3348150 := by exact prefixLift 3348150
  have htrace : WordTrace (prefixWord ++ tailWord_3348150) baseStart_3348150 baseEnd_3348150 := by
    simpa [prefixWord, tailWord_3348150, baseEnd_3348150] using wordTrace_append hprefix tailTrace_3348150
  have hstable : (prefixWord ++ tailWord_3348150).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348150).length < 2 ^ (prefixWord ++ tailWord_3348150).sum := by decide
  have hdescent : baseEnd_3348150 < baseStart_3348150 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348150) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348180 : List Nat := [2, 4, 1, 3, 1, 2, 3, 1, 2, 1, 3]
def baseStart_3348180 : Nat := 118140960795 + 3348180 * 2 ^ 59
def prefixEnd_3348180 : Nat := 4983230072969 + 3 ^ 40 * 3348180 * 2
def baseEnd_3348180 : Nat := 1719225657770815464052007

theorem tailTrace_3348180 : CollatzResearch.WordTrace tailWord_3348180 prefixEnd_3348180 1719225657770815464052007 := by
  unfold tailWord_3348180
  simp only [CollatzResearch.WordTrace]
  refine ⟨61059078505061579231952997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81412104673415438975937329 61059078505061579231952997)
  ·
    refine ⟨11448577219699046105991187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61059078505061579231952997 11448577219699046105991187)
    ·
      refine ⟨17172865829548569158986781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11448577219699046105991187 17172865829548569158986781)
      ·
        refine ⟨6439824686080713434620043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17172865829548569158986781 6439824686080713434620043)
        ·
          refine ⟨9659737029121070151930065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6439824686080713434620043 9659737029121070151930065)
          ·
            refine ⟨7244802771840802613947549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9659737029121070151930065 7244802771840802613947549)
            ·
              refine ⟨2716801039440300980230331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7244802771840802613947549 2716801039440300980230331)
              ·
                refine ⟨4075201559160451470345497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716801039440300980230331 4075201559160451470345497)
                ·
                  refine ⟨3056401169370338602759123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075201559160451470345497 3056401169370338602759123)
                  ·
                    refine ⟨4584601754055507904138685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3056401169370338602759123 4584601754055507904138685)
                    ·
                      refine ⟨1719225657770815464052007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584601754055507904138685 1719225657770815464052007)
                      ·
                        rfl

theorem cell23_3348180_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 1, 2, 3, 1, 2, 1, 3].length) (baseStart_3348180 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348180 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348180 prefixEnd_3348180 := by exact prefixLift 3348180
  have htrace : WordTrace (prefixWord ++ tailWord_3348180) baseStart_3348180 baseEnd_3348180 := by
    simpa [prefixWord, tailWord_3348180, baseEnd_3348180] using wordTrace_append hprefix tailTrace_3348180
  have hstable : (prefixWord ++ tailWord_3348180).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348180).length < 2 ^ (prefixWord ++ tailWord_3348180).sum := by decide
  have hdescent : baseEnd_3348180 < baseStart_3348180 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348180) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348186 : List Nat := [3, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2]
def baseStart_3348186 : Nat := 118140960795 + 3348186 * 2 ^ 59
def prefixEnd_3348186 : Nat := 4983230072969 + 3 ^ 40 * 3348186 * 2
def baseEnd_3348186 : Nat := 1719228738654742440576979

theorem tailTrace_3348186 : CollatzResearch.WordTrace tailWord_3348186 prefixEnd_3348186 1719228738654742440576979 := by
  unfold tailWord_3348186
  simp only [CollatzResearch.WordTrace]
  refine ⟨30529593962025355372156103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81412250565400947659082941 30529593962025355372156103)
  ·
    refine ⟨45794390943038033058234155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30529593962025355372156103 45794390943038033058234155)
    ·
      refine ⟨68691586414557049587351233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45794390943038033058234155 68691586414557049587351233)
      ·
        refine ⟨51518689810917787190513425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68691586414557049587351233 51518689810917787190513425)
        ·
          refine ⟨38639017358188340392885069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51518689810917787190513425 38639017358188340392885069)
          ·
            refine ⟨14489631509320627647331901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38639017358188340392885069 14489631509320627647331901)
            ·
              refine ⟨5433611815995235367749463, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14489631509320627647331901 5433611815995235367749463)
              ·
                refine ⟨8150417723992853051624195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5433611815995235367749463 8150417723992853051624195)
                ·
                  refine ⟨12225626585989279577436293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150417723992853051624195 12225626585989279577436293)
                  ·
                    refine ⟨2292304984872989920769305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12225626585989279577436293 2292304984872989920769305)
                    ·
                      refine ⟨1719228738654742440576979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292304984872989920769305 1719228738654742440576979)
                      ·
                        rfl

theorem cell23_3348186_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 3, 3, 1, 1, 4, 2].length) (baseStart_3348186 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348186 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348186 prefixEnd_3348186 := by exact prefixLift 3348186
  have htrace : WordTrace (prefixWord ++ tailWord_3348186) baseStart_3348186 baseEnd_3348186 := by
    simpa [prefixWord, tailWord_3348186, baseEnd_3348186] using wordTrace_append hprefix tailTrace_3348186
  have hstable : (prefixWord ++ tailWord_3348186).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348186).length < 2 ^ (prefixWord ++ tailWord_3348186).sum := by decide
  have hdescent : baseEnd_3348186 < baseStart_3348186 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348186) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348192 : List Nat := [2, 1, 1, 3, 1, 2, 4, 2, 7]
def baseStart_3348192 : Nat := 118140960795 + 3348192 * 2 ^ 59
def prefixEnd_3348192 : Nat := 4983230072969 + 3 ^ 40 * 3348192 * 2
def baseEnd_3348192 : Nat := 191025757726518824122439

theorem tailTrace_3348192 : CollatzResearch.WordTrace tailWord_3348192 prefixEnd_3348192 191025757726518824122439 := by
  unfold tailWord_3348192
  simp only [CollatzResearch.WordTrace]
  refine ⟨61059297343039842256671415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81412396457386456342228553 61059297343039842256671415)
  ·
    refine ⟨91588946014559763385007123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61059297343039842256671415 91588946014559763385007123)
    ·
      refine ⟨137383419021839645077510685, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91588946014559763385007123 137383419021839645077510685)
      ·
        refine ⟨51518782133189866904066507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137383419021839645077510685 51518782133189866904066507)
        ·
          refine ⟨77278173199784800356099761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51518782133189866904066507 77278173199784800356099761)
          ·
            refine ⟨57958629899838600267074821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77278173199784800356099761 57958629899838600267074821)
            ·
              refine ⟨10867243106219737550076529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57958629899838600267074821 10867243106219737550076529)
              ·
                refine ⟨8150432329664803162557397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10867243106219737550076529 8150432329664803162557397)
                ·
                  refine ⟨191025757726518824122439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8150432329664803162557397 191025757726518824122439)
                  ·
                    rfl

theorem cell23_3348192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 2, 4, 2, 7].length) (baseStart_3348192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348192 prefixEnd_3348192 := by exact prefixLift 3348192
  have htrace : WordTrace (prefixWord ++ tailWord_3348192) baseStart_3348192 baseEnd_3348192 := by
    simpa [prefixWord, tailWord_3348192, baseEnd_3348192] using wordTrace_append hprefix tailTrace_3348192
  have hstable : (prefixWord ++ tailWord_3348192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348192).length < 2 ^ (prefixWord ++ tailWord_3348192).sum := by decide
  have hdescent : baseEnd_3348192 < baseStart_3348192 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348259 : List Nat := [1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 4]
def baseStart_3348259 : Nat := 118140960795 + 3348259 * 2 ^ 59
def prefixEnd_3348259 : Nat := 4983230072969 + 3 ^ 40 * 3348259 * 2
def baseEnd_3348259 : Nat := 1719266222742520654964143

theorem tailTrace_3348259 : CollatzResearch.WordTrace tailWord_3348259 prefixEnd_3348259 1719266222742520654964143 := by
  unfold tailWord_3348259
  simp only [CollatzResearch.WordTrace]
  refine ⟨122121038376836954956031831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81414025584557969970687887 122121038376836954956031831)
  ·
    refine ⟨183181557565255432434047747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122121038376836954956031831 183181557565255432434047747)
    ·
      refine ⟨274772336347883148651071621, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183181557565255432434047747 274772336347883148651071621)
      ·
        refine ⟨51519813065228090372075929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274772336347883148651071621 51519813065228090372075929)
        ·
          refine ⟨38639859798921067779056947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51519813065228090372075929 38639859798921067779056947)
          ·
            refine ⟨57959789698381601668585421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38639859798921067779056947 57959789698381601668585421)
            ·
              refine ⟨21734921136893100625719533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57959789698381601668585421 21734921136893100625719533)
              ·
                refine ⟨8150595426334912734644825, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21734921136893100625719533 8150595426334912734644825)
                ·
                  refine ⟨6112946569751184550983619, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8150595426334912734644825 6112946569751184550983619)
                  ·
                    refine ⟨9169419854626776826475429, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6112946569751184550983619 9169419854626776826475429)
                    ·
                      refine ⟨1719266222742520654964143, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9169419854626776826475429 1719266222742520654964143)
                      ·
                        rfl

theorem cell23_3348259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 3, 3, 2, 1, 4].length) (baseStart_3348259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348259 prefixEnd_3348259 := by exact prefixLift 3348259
  have htrace : WordTrace (prefixWord ++ tailWord_3348259) baseStart_3348259 baseEnd_3348259 := by
    simpa [prefixWord, tailWord_3348259, baseEnd_3348259] using wordTrace_append hprefix tailTrace_3348259
  have hstable : (prefixWord ++ tailWord_3348259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348259).length < 2 ^ (prefixWord ++ tailWord_3348259).sum := by decide
  have hdescent : baseEnd_3348259 < baseStart_3348259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348279 : List Nat := [1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 3]
def baseStart_3348279 : Nat := 118140960795 + 3348279 * 2 ^ 59
def prefixEnd_3348279 : Nat := 4983230072969 + 3 ^ 40 * 3348279 * 2
def baseEnd_3348279 : Nat := 1719276492355610576714051

theorem tailTrace_3348279 : CollatzResearch.WordTrace tailWord_3348279 prefixEnd_3348279 1719276492355610576714051 := by
  unfold tailWord_3348279
  simp only [CollatzResearch.WordTrace]
  refine ⟨122121767836764498371759891, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81414511891176332247839927 122121767836764498371759891)
  ·
    refine ⟨183182651755146747557639837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122121767836764498371759891 183182651755146747557639837)
    ·
      refine ⟨68693494408180030334114939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183182651755146747557639837 68693494408180030334114939)
      ·
        refine ⟨103040241612270045501172409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68693494408180030334114939 103040241612270045501172409)
        ·
          refine ⟨77280181209202534125879307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103040241612270045501172409 77280181209202534125879307)
          ·
            refine ⟨115920271813803801188818961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77280181209202534125879307 115920271813803801188818961)
            ·
              refine ⟨86940203860352850891614221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115920271813803801188818961 86940203860352850891614221)
              ·
                refine ⟨32602576447632319084355333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86940203860352850891614221 32602576447632319084355333)
                ·
                  refine ⟨6112983083931059828316625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32602576447632319084355333 6112983083931059828316625)
                  ·
                    refine ⟨4584737312948294871237469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6112983083931059828316625 4584737312948294871237469)
                    ·
                      refine ⟨1719276492355610576714051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584737312948294871237469 1719276492355610576714051)
                      ·
                        rfl

theorem cell23_3348279_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 2, 3, 4, 2, 3].length) (baseStart_3348279 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348279 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348279 prefixEnd_3348279 := by exact prefixLift 3348279
  have htrace : WordTrace (prefixWord ++ tailWord_3348279) baseStart_3348279 baseEnd_3348279 := by
    simpa [prefixWord, tailWord_3348279, baseEnd_3348279] using wordTrace_append hprefix tailTrace_3348279
  have hstable : (prefixWord ++ tailWord_3348279).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348279).length < 2 ^ (prefixWord ++ tailWord_3348279).sum := by decide
  have hdescent : baseEnd_3348279 < baseStart_3348279 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348279) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348336 : List Nat := [2, 1, 1, 1, 4, 1, 1, 3, 4, 3, 2]
def baseStart_3348336 : Nat := 118140960795 + 3348336 * 2 ^ 59
def prefixEnd_3348336 : Nat := 4983230072969 + 3 ^ 40 * 3348336 * 2
def baseEnd_3348336 : Nat := 1719305760752916853701289

theorem tailTrace_3348336 : CollatzResearch.WordTrace tailWord_3348336 prefixEnd_3348336 1719305760752916853701289 := by
  unfold tailWord_3348336
  simp only [CollatzResearch.WordTrace]
  refine ⟨61061923398778998553292431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81415897865038664737723241 61061923398778998553292431)
  ·
    refine ⟨91592885098168497829938647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61061923398778998553292431 91592885098168497829938647)
    ·
      refine ⟨137389327647252746744907971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91592885098168497829938647 137389327647252746744907971)
      ·
        refine ⟨206083991470879120117361957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137389327647252746744907971 206083991470879120117361957)
        ·
          refine ⟨38640748400789835022005367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206083991470879120117361957 38640748400789835022005367)
          ·
            refine ⟨57961122601184752533008051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38640748400789835022005367 57961122601184752533008051)
            ·
              refine ⟨86941683901777128799512077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57961122601184752533008051 86941683901777128799512077)
              ·
                refine ⟨32603131463166423299817029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86941683901777128799512077 32603131463166423299817029)
                ·
                  refine ⟨6113087149343704368715693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32603131463166423299817029 6113087149343704368715693)
                  ·
                    refine ⟨2292407681003889138268385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6113087149343704368715693 2292407681003889138268385)
                    ·
                      refine ⟨1719305760752916853701289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292407681003889138268385 1719305760752916853701289)
                      ·
                        rfl

theorem cell23_3348336_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 1, 3, 4, 3, 2].length) (baseStart_3348336 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348336 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348336 prefixEnd_3348336 := by exact prefixLift 3348336
  have htrace : WordTrace (prefixWord ++ tailWord_3348336) baseStart_3348336 baseEnd_3348336 := by
    simpa [prefixWord, tailWord_3348336, baseEnd_3348336] using wordTrace_append hprefix tailTrace_3348336
  have hstable : (prefixWord ++ tailWord_3348336).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348336).length < 2 ^ (prefixWord ++ tailWord_3348336).sum := by decide
  have hdescent : baseEnd_3348336 < baseStart_3348336 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348336) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348350 : List Nat := [4, 2, 3, 1, 1, 2, 3, 1, 6]
def baseStart_3348350 : Nat := 118140960795 + 3348350 * 2 ^ 59
def prefixEnd_3348350 : Nat := 4983230072969 + 3 ^ 40 * 3348350 * 2
def baseEnd_3348350 : Nat := 191034772164675533214025

theorem tailTrace_3348350 : CollatzResearch.WordTrace tailWord_3348350 prefixEnd_3348350 191034772164675533214025 := by
  unfold tailWord_3348350
  simp only [CollatzResearch.WordTrace]
  refine ⟨15265544677438409687199313, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81416238279671518331729669 15265544677438409687199313)
  ·
    refine ⟨11449158508078807265399485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15265544677438409687199313 11449158508078807265399485)
    ·
      refine ⟨4293434440529552724524807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11449158508078807265399485 4293434440529552724524807)
      ·
        refine ⟨6440151660794329086787211, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4293434440529552724524807 6440151660794329086787211)
        ·
          refine ⟨9660227491191493630180817, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6440151660794329086787211 9660227491191493630180817)
          ·
            refine ⟨7245170618393620222635613, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9660227491191493630180817 7245170618393620222635613)
            ·
              refine ⟨2716938981897607583488355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7245170618393620222635613 2716938981897607583488355)
              ·
                refine ⟨4075408472846411375232533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2716938981897607583488355 4075408472846411375232533)
                ·
                  refine ⟨191034772164675533214025, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4075408472846411375232533 191034772164675533214025)
                  ·
                    rfl

theorem cell23_3348350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 1, 2, 3, 1, 6].length) (baseStart_3348350 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348350 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348350 prefixEnd_3348350 := by exact prefixLift 3348350
  have htrace : WordTrace (prefixWord ++ tailWord_3348350) baseStart_3348350 baseEnd_3348350 := by
    simpa [prefixWord, tailWord_3348350, baseEnd_3348350] using wordTrace_append hprefix tailTrace_3348350
  have hstable : (prefixWord ++ tailWord_3348350).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348350).length < 2 ^ (prefixWord ++ tailWord_3348350).sum := by decide
  have hdescent : baseEnd_3348350 < baseStart_3348350 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348409 : List Nat := [1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 6]
def baseStart_3348409 : Nat := 118140960795 + 3348409 * 2 ^ 59
def prefixEnd_3348409 : Nat := 4983230072969 + 3 ^ 40 * 3348409 * 2
def baseEnd_3348409 : Nat := 1719343244840695068088453

theorem tailTrace_3348409 : CollatzResearch.WordTrace tailWord_3348409 prefixEnd_3348409 1719343244840695068088453 := by
  unfold tailWord_3348409
  simp only [CollatzResearch.WordTrace]
  refine ⟨122126509326293530573992281, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81417672884195687049328187 122126509326293530573992281)
  ·
    refine ⟨91594881994720147930494211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122126509326293530573992281 91594881994720147930494211)
    ·
      refine ⟨137392322992080221895741317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91594881994720147930494211 137392322992080221895741317)
      ·
        refine ⟨25761060561015041605451497, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137392322992080221895741317 25761060561015041605451497)
        ·
          refine ⟨19320795420761281204088623, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25761060561015041605451497 19320795420761281204088623)
          ·
            refine ⟨28981193131141921806132935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19320795420761281204088623 28981193131141921806132935)
            ·
              refine ⟨43471789696712882709199403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28981193131141921806132935 43471789696712882709199403)
              ·
                refine ⟨65207684545069324063799105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43471789696712882709199403 65207684545069324063799105)
                ·
                  refine ⟨48905763408801993047849329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65207684545069324063799105 48905763408801993047849329)
                  ·
                    refine ⟨36679322556601494785886997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 48905763408801993047849329 36679322556601494785886997)
                    ·
                      refine ⟨1719343244840695068088453, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36679322556601494785886997 1719343244840695068088453)
                      ·
                        rfl

theorem cell23_3348409_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 2, 1, 1, 1, 2, 2, 6].length) (baseStart_3348409 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348409 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348409 prefixEnd_3348409 := by exact prefixLift 3348409
  have htrace : WordTrace (prefixWord ++ tailWord_3348409) baseStart_3348409 baseEnd_3348409 := by
    simpa [prefixWord, tailWord_3348409, baseEnd_3348409] using wordTrace_append hprefix tailTrace_3348409
  have hstable : (prefixWord ++ tailWord_3348409).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348409).length < 2 ^ (prefixWord ++ tailWord_3348409).sum := by decide
  have hdescent : baseEnd_3348409 < baseStart_3348409 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348409) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348416 : List Nat := [2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3]
def baseStart_3348416 : Nat := 118140960795 + 3348416 * 2 ^ 59
def prefixEnd_3348416 : Nat := 4983230072969 + 3 ^ 40 * 3348416 * 2
def baseEnd_3348416 : Nat := 1719346839205276540700921

theorem tailTrace_3348416 : CollatzResearch.WordTrace tailWord_3348416 prefixEnd_3348416 1719346839205276540700921 := by
  unfold tailWord_3348416
  simp only [CollatzResearch.WordTrace]
  refine ⟨61063382318634085384748551, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81417843091512113846331401 61063382318634085384748551)
  ·
    refine ⟨91595073477951128077122827, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61063382318634085384748551 91595073477951128077122827)
    ·
      refine ⟨137392610216926692115684241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91595073477951128077122827 137392610216926692115684241)
      ·
        refine ⟨103044457662695019086763181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137392610216926692115684241 103044457662695019086763181)
        ·
          refine ⟨38641671623510632157536193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103044457662695019086763181 38641671623510632157536193)
          ·
            refine ⟨28981253717632974118152145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38641671623510632157536193 28981253717632974118152145)
            ·
              refine ⟨21735940288224730588614109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28981253717632974118152145 21735940288224730588614109)
              ·
                refine ⟨8150977608084273970730291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21735940288224730588614109 8150977608084273970730291)
                ·
                  refine ⟨12226466412126410956095437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8150977608084273970730291 12226466412126410956095437)
                  ·
                    refine ⟨4584924904547404108535789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12226466412126410956095437 4584924904547404108535789)
                    ·
                      refine ⟨1719346839205276540700921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4584924904547404108535789 1719346839205276540700921)
                      ·
                        rfl

theorem cell23_3348416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 3, 2, 2, 3, 1, 3, 3].length) (baseStart_3348416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348416 prefixEnd_3348416 := by exact prefixLift 3348416
  have htrace : WordTrace (prefixWord ++ tailWord_3348416) baseStart_3348416 baseEnd_3348416 := by
    simpa [prefixWord, tailWord_3348416, baseEnd_3348416] using wordTrace_append hprefix tailTrace_3348416
  have hstable : (prefixWord ++ tailWord_3348416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348416).length < 2 ^ (prefixWord ++ tailWord_3348416).sum := by decide
  have hdescent : baseEnd_3348416 < baseStart_3348416 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348444 : List Nat := [2, 2, 6, 1, 1, 1, 2, 2, 2, 4]
def baseStart_3348444 : Nat := 118140960795 + 3348444 * 2 ^ 59
def prefixEnd_3348444 : Nat := 4983230072969 + 3 ^ 40 * 3348444 * 2
def baseEnd_3348444 : Nat := 573120405554534143716931

theorem tailTrace_3348444 : CollatzResearch.WordTrace tailWord_3348444 prefixEnd_3348444 573120405554534143716931 := by
  unfold tailWord_3348444
  simp only [CollatzResearch.WordTrace]
  refine ⟨61063892940583365775758193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81418523920777821034344257 61063892940583365775758193)
  ·
    refine ⟨45797919705437524331818645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61063892940583365775758193 45797919705437524331818645)
    ·
      refine ⟨2146777486192383953053999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 45797919705437524331818645 2146777486192383953053999)
      ·
        refine ⟨3220166229288575929580999, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2146777486192383953053999 3220166229288575929580999)
        ·
          refine ⟨4830249343932863894371499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220166229288575929580999 4830249343932863894371499)
          ·
            refine ⟨7245374015899295841557249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830249343932863894371499 7245374015899295841557249)
            ·
              refine ⟨5434030511924471881167937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7245374015899295841557249 5434030511924471881167937)
              ·
                refine ⟨4075522883943353910875953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434030511924471881167937 4075522883943353910875953)
                ·
                  refine ⟨3056642162957515433156965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075522883943353910875953 3056642162957515433156965)
                  ·
                    refine ⟨573120405554534143716931, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3056642162957515433156965 573120405554534143716931)
                    ·
                      rfl

theorem cell23_3348444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 6, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_3348444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348444 prefixEnd_3348444 := by exact prefixLift 3348444
  have htrace : WordTrace (prefixWord ++ tailWord_3348444) baseStart_3348444 baseEnd_3348444 := by
    simpa [prefixWord, tailWord_3348444, baseEnd_3348444] using wordTrace_append hprefix tailTrace_3348444
  have hstable : (prefixWord ++ tailWord_3348444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348444).length < 2 ^ (prefixWord ++ tailWord_3348444).sum := by decide
  have hdescent : baseEnd_3348444 < baseStart_3348444 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348459 : List Nat := [1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5]
def baseStart_3348459 : Nat := 118140960795 + 3348459 * 2 ^ 59
def prefixEnd_3348459 : Nat := 4983230072969 + 3 ^ 40 * 3348459 * 2
def baseEnd_3348459 : Nat := 1719368918873419872463223

theorem tailTrace_3348459 : CollatzResearch.WordTrace tailWord_3348459 prefixEnd_3348459 1719368918873419872463223 := by
  unfold tailWord_3348459
  simp only [CollatzResearch.WordTrace]
  refine ⟨122128332976112389113312431, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81418888650741592742208287 122128332976112389113312431)
  ·
    refine ⟨183192499464168583669968647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122128332976112389113312431 183192499464168583669968647)
    ·
      refine ⟨274788749196252875504952971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183192499464168583669968647 274788749196252875504952971)
      ·
        refine ⟨412183123794379313257429457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274788749196252875504952971 412183123794379313257429457)
        ·
          refine ⟨309137342845784484943072093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412183123794379313257429457 309137342845784484943072093)
          ·
            refine ⟨115926503567169181853652035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309137342845784484943072093 115926503567169181853652035)
            ·
              refine ⟨173889755350753772780478053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115926503567169181853652035 173889755350753772780478053)
              ·
                refine ⟨32604329128266332396339635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 173889755350753772780478053 32604329128266332396339635)
                ·
                  refine ⟨48906493692399498594509453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32604329128266332396339635 48906493692399498594509453)
                  ·
                    refine ⟨18339935134649811972941045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 48906493692399498594509453 18339935134649811972941045)
                    ·
                      refine ⟨1719368918873419872463223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18339935134649811972941045 1719368918873419872463223)
                      ·
                        rfl

theorem cell23_3348459_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 1, 4, 1, 3, 5].length) (baseStart_3348459 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348459 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348459 prefixEnd_3348459 := by exact prefixLift 3348459
  have htrace : WordTrace (prefixWord ++ tailWord_3348459) baseStart_3348459 baseEnd_3348459 := by
    simpa [prefixWord, tailWord_3348459, baseEnd_3348459] using wordTrace_append hprefix tailTrace_3348459
  have hstable : (prefixWord ++ tailWord_3348459).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348459).length < 2 ^ (prefixWord ++ tailWord_3348459).sum := by decide
  have hdescent : baseEnd_3348459 < baseStart_3348459 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348459) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348473 : List Nat := [1, 2, 1, 3, 1, 4, 1, 3, 1, 4, 2]
def baseStart_3348473 : Nat := 118140960795 + 3348473 * 2 ^ 59
def prefixEnd_3348473 : Nat := 4983230072969 + 3 ^ 40 * 3348473 * 2
def baseEnd_3348473 : Nat := 1719376107602582817688159

theorem tailTrace_3348473 : CollatzResearch.WordTrace tailWord_3348473 prefixEnd_3348473 1719376107602582817688159 := by
  unfold tailWord_3348473
  simp only [CollatzResearch.WordTrace]
  refine ⟨122128843598061669504322073, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81419229065374446336214715 122128843598061669504322073)
  ·
    refine ⟨91596632698546252128241555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122128843598061669504322073 91596632698546252128241555)
    ·
      refine ⟨137394949047819378192362333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91596632698546252128241555 137394949047819378192362333)
      ·
        refine ⟨51523105892932266822135875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137394949047819378192362333 51523105892932266822135875)
        ·
          refine ⟨77284658839398400233203813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51523105892932266822135875 77284658839398400233203813)
          ·
            refine ⟨14490873532387200043725715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77284658839398400233203813 14490873532387200043725715)
            ·
              refine ⟨21736310298580800065588573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14490873532387200043725715 21736310298580800065588573)
              ·
                refine ⟨8151116361967800024595715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21736310298580800065588573 8151116361967800024595715)
                ·
                  refine ⟨12226674542951700036893573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151116361967800024595715 12226674542951700036893573)
                  ·
                    refine ⟨2292501476803443756917545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12226674542951700036893573 2292501476803443756917545)
                    ·
                      refine ⟨1719376107602582817688159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292501476803443756917545 1719376107602582817688159)
                      ·
                        rfl

theorem cell23_3348473_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 4, 1, 3, 1, 4, 2].length) (baseStart_3348473 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348473 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348473 prefixEnd_3348473 := by exact prefixLift 3348473
  have htrace : WordTrace (prefixWord ++ tailWord_3348473) baseStart_3348473 baseEnd_3348473 := by
    simpa [prefixWord, tailWord_3348473, baseEnd_3348473] using wordTrace_append hprefix tailTrace_3348473
  have hstable : (prefixWord ++ tailWord_3348473).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348473).length < 2 ^ (prefixWord ++ tailWord_3348473).sum := by decide
  have hdescent : baseEnd_3348473 < baseStart_3348473 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348473) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348476 : List Nat := [2, 2, 2, 1, 2, 2, 1, 2, 2, 4, 3]
def baseStart_3348476 : Nat := 118140960795 + 3348476 * 2 ^ 59
def prefixEnd_3348476 : Nat := 4983230072969 + 3 ^ 40 * 3348476 * 2
def baseEnd_3348476 : Nat := 1719377648044546305950645

theorem tailTrace_3348476 : CollatzResearch.WordTrace tailWord_3348476 prefixEnd_3348476 1719377648044546305950645 := by
  unfold tailWord_3348476
  simp only [CollatzResearch.WordTrace]
  refine ⟨61064476508525400508340641, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81419302011367200677787521 61064476508525400508340641)
  ·
    refine ⟨45798357381394050381255481, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61064476508525400508340641 45798357381394050381255481)
    ·
      refine ⟨34348768036045537785941611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45798357381394050381255481 34348768036045537785941611)
      ·
        refine ⟨51523152054068306678912417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34348768036045537785941611 51523152054068306678912417)
        ·
          refine ⟨38642364040551230009184313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51523152054068306678912417 38642364040551230009184313)
          ·
            refine ⟨28981773030413422506888235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38642364040551230009184313 28981773030413422506888235)
            ·
              refine ⟨43472659545620133760332353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28981773030413422506888235 43472659545620133760332353)
              ·
                refine ⟨32604494659215100320249265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43472659545620133760332353 32604494659215100320249265)
                ·
                  refine ⟨24453370994411325240186949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32604494659215100320249265 24453370994411325240186949)
                  ·
                    refine ⟨4585007061452123482535053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24453370994411325240186949 4585007061452123482535053)
                    ·
                      refine ⟨1719377648044546305950645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4585007061452123482535053 1719377648044546305950645)
                      ·
                        rfl

theorem cell23_3348476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 1, 2, 2, 4, 3].length) (baseStart_3348476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348476 prefixEnd_3348476 := by exact prefixLift 3348476
  have htrace : WordTrace (prefixWord ++ tailWord_3348476) baseStart_3348476 baseEnd_3348476 := by
    simpa [prefixWord, tailWord_3348476, baseEnd_3348476] using wordTrace_append hprefix tailTrace_3348476
  have hstable : (prefixWord ++ tailWord_3348476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348476).length < 2 ^ (prefixWord ++ tailWord_3348476).sum := by decide
  have hdescent : baseEnd_3348476 < baseStart_3348476 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348489 : List Nat := [1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 7]
def baseStart_3348489 : Nat := 118140960795 + 3348489 * 2 ^ 59
def prefixEnd_3348489 : Nat := 4983230072969 + 3 ^ 40 * 3348489 * 2
def baseEnd_3348489 : Nat := 1719384323293054755088085

theorem tailTrace_3348489 : CollatzResearch.WordTrace tailWord_3348489 prefixEnd_3348489 1719384323293054755088085 := by
  unfold tailWord_3348489
  simp only [CollatzResearch.WordTrace]
  refine ⟨122129427166003704236904521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81419618110669136157936347 122129427166003704236904521)
  ·
    refine ⟨91597070374502778177678391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122129427166003704236904521 91597070374502778177678391)
    ·
      refine ⟨137395605561754167266517587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91597070374502778177678391 137395605561754167266517587)
      ·
        refine ⟨206093408342631250899776381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137395605561754167266517587 206093408342631250899776381)
        ·
          refine ⟨77285028128486719087416143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206093408342631250899776381 77285028128486719087416143)
          ·
            refine ⟨115927542192730078631124215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77285028128486719087416143 115927542192730078631124215)
            ·
              refine ⟨173891313289095117946686323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115927542192730078631124215 173891313289095117946686323)
              ·
                refine ⟨260836969933642676920029485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173891313289095117946686323 260836969933642676920029485)
                ·
                  refine ⟨97813863725116003845011057, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 260836969933642676920029485 97813863725116003845011057)
                  ·
                    refine ⟨73360397793837002883758293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 97813863725116003845011057 73360397793837002883758293)
                    ·
                      refine ⟨1719384323293054755088085, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73360397793837002883758293 1719384323293054755088085)
                      ·
                        rfl

theorem cell23_3348489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 1, 1, 3, 2, 7].length) (baseStart_3348489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348489 prefixEnd_3348489 := by exact prefixLift 3348489
  have htrace : WordTrace (prefixWord ++ tailWord_3348489) baseStart_3348489 baseEnd_3348489 := by
    simpa [prefixWord, tailWord_3348489, baseEnd_3348489] using wordTrace_append hprefix tailTrace_3348489
  have hstable : (prefixWord ++ tailWord_3348489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348489).length < 2 ^ (prefixWord ++ tailWord_3348489).sum := by decide
  have hdescent : baseEnd_3348489 < baseStart_3348489 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348513 : List Nat := [1, 2, 3, 2, 4, 1, 2, 1, 7]
def baseStart_3348513 : Nat := 118140960795 + 3348513 * 2 ^ 59
def prefixEnd_3348513 : Nat := 4983230072969 + 3 ^ 40 * 3348513 * 2
def baseEnd_3348513 : Nat := 191044071869862517909775

theorem tailTrace_3348513 : CollatzResearch.WordTrace tailWord_3348513 prefixEnd_3348513 191044071869862517909775 := by
  unfold tailWord_3348513
  simp only [CollatzResearch.WordTrace]
  refine ⟨122130302517916756335778193, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81420201678611170890518795 122130302517916756335778193)
  ·
    refine ⟨91597726888437567251833645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122130302517916756335778193 91597726888437567251833645)
    ·
      refine ⟨34349147583164087719437617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91597726888437567251833645 34349147583164087719437617)
      ·
        refine ⟨25761860687373065789578213, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34349147583164087719437617 25761860687373065789578213)
        ·
          refine ⟨4830348878882449835545915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25761860687373065789578213 4830348878882449835545915)
          ·
            refine ⟨7245523318323674753318873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830348878882449835545915 7245523318323674753318873)
            ·
              refine ⟨5434142488742756064989155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7245523318323674753318873 5434142488742756064989155)
              ·
                refine ⟨8151213733114134097483733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434142488742756064989155 8151213733114134097483733)
                ·
                  refine ⟨191044071869862517909775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8151213733114134097483733 191044071869862517909775)
                  ·
                    rfl

theorem cell23_3348513_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 4, 1, 2, 1, 7].length) (baseStart_3348513 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348513 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348513 prefixEnd_3348513 := by exact prefixLift 3348513
  have htrace : WordTrace (prefixWord ++ tailWord_3348513) baseStart_3348513 baseEnd_3348513 := by
    simpa [prefixWord, tailWord_3348513, baseEnd_3348513] using wordTrace_append hprefix tailTrace_3348513
  have hstable : (prefixWord ++ tailWord_3348513).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348513).length < 2 ^ (prefixWord ++ tailWord_3348513).sum := by decide
  have hdescent : baseEnd_3348513 < baseStart_3348513 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348513) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348533 : List Nat := [1, 3, 3, 1, 1, 1, 2, 2, 2, 5, 2]
def baseStart_3348533 : Nat := 118140960795 + 3348533 * 2 ^ 59
def prefixEnd_3348533 : Nat := 4983230072969 + 3 ^ 40 * 3348533 * 2
def baseEnd_3348533 : Nat := 1719406916441852582937883

theorem tailTrace_3348533 : CollatzResearch.WordTrace tailWord_3348533 prefixEnd_3348533 1719406916441852582937883 := by
  unfold tailWord_3348533
  simp only [CollatzResearch.WordTrace]
  refine ⟨122131031977844299751506253, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81420687985229533167670835 122131031977844299751506253)
  ·
    refine ⟨45799136991691612406814845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122131031977844299751506253 45799136991691612406814845)
    ·
      refine ⟨17174676371884354652555567, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45799136991691612406814845 17174676371884354652555567)
      ·
        refine ⟨25762014557826531978833351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17174676371884354652555567 25762014557826531978833351)
        ·
          refine ⟨38643021836739797968250027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25762014557826531978833351 38643021836739797968250027)
          ·
            refine ⟨57964532755109696952375041, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38643021836739797968250027 57964532755109696952375041)
            ·
              refine ⟨43473399566332272714281281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57964532755109696952375041 43473399566332272714281281)
              ·
                refine ⟨32605049674749204535710961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43473399566332272714281281 32605049674749204535710961)
                ·
                  refine ⟨24453787256061903401783221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32605049674749204535710961 24453787256061903401783221)
                  ·
                    refine ⟨2292542555255803443917177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24453787256061903401783221 2292542555255803443917177)
                    ·
                      refine ⟨1719406916441852582937883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292542555255803443917177 1719406916441852582937883)
                      ·
                        rfl

theorem cell23_3348533_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 1, 2, 2, 2, 5, 2].length) (baseStart_3348533 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348533 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348533 prefixEnd_3348533 := by exact prefixLift 3348533
  have htrace : WordTrace (prefixWord ++ tailWord_3348533) baseStart_3348533 baseEnd_3348533 := by
    simpa [prefixWord, tailWord_3348533, baseEnd_3348533] using wordTrace_append hprefix tailTrace_3348533
  have hstable : (prefixWord ++ tailWord_3348533).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348533).length < 2 ^ (prefixWord ++ tailWord_3348533).sum := by decide
  have hdescent : baseEnd_3348533 < baseStart_3348533 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348533) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348583 : List Nat := [1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 3]
def baseStart_3348583 : Nat := 118140960795 + 3348583 * 2 ^ 59
def prefixEnd_3348583 : Nat := 4983230072969 + 3 ^ 40 * 3348583 * 2
def baseEnd_3348583 : Nat := 1719432590474577387312653

theorem tailTrace_3348583 : CollatzResearch.WordTrace tailWord_3348583 prefixEnd_3348583 1719432590474577387312653 := by
  unfold tailWord_3348583
  simp only [CollatzResearch.WordTrace]
  refine ⟨122132855627663158290826403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81421903751775438860550935 122132855627663158290826403)
  ·
    refine ⟨183199283441494737436239605, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122132855627663158290826403 183199283441494737436239605)
    ·
      refine ⟨17174932822640131634647463, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183199283441494737436239605 17174932822640131634647463)
      ·
        refine ⟨25762399233960197451971195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17174932822640131634647463 25762399233960197451971195)
        ·
          refine ⟨38643598850940296177956793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25762399233960197451971195 38643598850940296177956793)
          ·
            refine ⟨28982699138205222133467595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38643598850940296177956793 28982699138205222133467595)
            ·
              refine ⟨43474048707307833200201393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28982699138205222133467595 43474048707307833200201393)
              ·
                refine ⟨32605536530480874900151045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43474048707307833200201393 32605536530480874900151045)
                ·
                  refine ⟨6113538099465164043778321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32605536530480874900151045 6113538099465164043778321)
                  ·
                    refine ⟨4585153574598873032833741, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6113538099465164043778321 4585153574598873032833741)
                    ·
                      refine ⟨1719432590474577387312653, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4585153574598873032833741 1719432590474577387312653)
                      ·
                        rfl

theorem cell23_3348583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 1, 2, 4, 2, 3].length) (baseStart_3348583 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348583 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348583 prefixEnd_3348583 := by exact prefixLift 3348583
  have htrace : WordTrace (prefixWord ++ tailWord_3348583) baseStart_3348583 baseEnd_3348583 := by
    simpa [prefixWord, tailWord_3348583, baseEnd_3348583] using wordTrace_append hprefix tailTrace_3348583
  have hstable : (prefixWord ++ tailWord_3348583).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348583).length < 2 ^ (prefixWord ++ tailWord_3348583).sum := by decide
  have hdescent : baseEnd_3348583 < baseStart_3348583 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348656 : List Nat := [2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5]
def baseStart_3348656 : Nat := 118140960795 + 3348656 * 2 ^ 59
def prefixEnd_3348656 : Nat := 4983230072969 + 3 ^ 40 * 3348656 * 2
def baseEnd_3348656 : Nat := 1719470074562355601699817

theorem tailTrace_3348656 : CollatzResearch.WordTrace tailWord_3348656 prefixEnd_3348656 1719470074562355601699817 := by
  unfold tailWord_3348656
  simp only [CollatzResearch.WordTrace]
  refine ⟨61067759078199345879116911, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81423678770932461172155881 61067759078199345879116911)
  ·
    refine ⟨91601638617299018818675367, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61067759078199345879116911 91601638617299018818675367)
    ·
      refine ⟨137402457925948528228013051, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91601638617299018818675367 137402457925948528228013051)
      ·
        refine ⟨206103686888922792342019577, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137402457925948528228013051 206103686888922792342019577)
        ·
          refine ⟨154577765166692094256514683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206103686888922792342019577 154577765166692094256514683)
          ·
            refine ⟨231866647750038141384772025, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154577765166692094256514683 231866647750038141384772025)
            ·
              refine ⟨173899985812528606038579019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 231866647750038141384772025 173899985812528606038579019)
              ·
                refine ⟨260849978718792909057868529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173899985812528606038579019 260849978718792909057868529)
                ·
                  refine ⟨195637484039094681793401397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 260849978718792909057868529 195637484039094681793401397)
                  ·
                    refine ⟨18341014128665126418131381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 195637484039094681793401397 18341014128665126418131381)
                    ·
                      refine ⟨1719470074562355601699817, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18341014128665126418131381 1719470074562355601699817)
                      ·
                        rfl

theorem cell23_3348656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 2, 1, 2, 5, 5].length) (baseStart_3348656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348656 prefixEnd_3348656 := by exact prefixLift 3348656
  have htrace : WordTrace (prefixWord ++ tailWord_3348656) baseStart_3348656 baseEnd_3348656 := by
    simpa [prefixWord, tailWord_3348656, baseEnd_3348656] using wordTrace_append hprefix tailTrace_3348656
  have hstable : (prefixWord ++ tailWord_3348656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348656).length < 2 ^ (prefixWord ++ tailWord_3348656).sum := by decide
  have hdescent : baseEnd_3348656 < baseStart_3348656 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348657 : List Nat := [1, 2, 2, 5, 2, 1, 1, 1, 1, 5, 2]
def baseStart_3348657 : Nat := 118140960795 + 3348657 * 2 ^ 59
def prefixEnd_3348657 : Nat := 4983230072969 + 3 ^ 40 * 3348657 * 2
def baseEnd_3348657 : Nat := 1719470588043010097787313

theorem tailTrace_3348657 : CollatzResearch.WordTrace tailWord_3348657 prefixEnd_3348657 1719470588043010097787313 := by
  unfold tailWord_3348657
  simp only [CollatzResearch.WordTrace]
  refine ⟨122135554629395068929020225, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81423703086263379286013483 122135554629395068929020225)
  ·
    refine ⟨91601665972046301696765169, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122135554629395068929020225 91601665972046301696765169)
    ·
      refine ⟨68701249479034726272573877, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91601665972046301696765169 68701249479034726272573877)
      ·
        refine ⟨6440742138659505588053801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 68701249479034726272573877 6440742138659505588053801)
        ·
          refine ⟨4830556603994629191040351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6440742138659505588053801 4830556603994629191040351)
          ·
            refine ⟨7245834905991943786560527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4830556603994629191040351 7245834905991943786560527)
            ·
              refine ⟨10868752358987915679840791, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245834905991943786560527 10868752358987915679840791)
              ·
                refine ⟨16303128538481873519761187, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10868752358987915679840791 16303128538481873519761187)
                ·
                  refine ⟨24454692807722810279641781, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16303128538481873519761187 24454692807722810279641781)
                  ·
                    refine ⟨2292627450724013463716417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24454692807722810279641781 2292627450724013463716417)
                    ·
                      refine ⟨1719470588043010097787313, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292627450724013463716417 1719470588043010097787313)
                      ·
                        rfl

theorem cell23_3348657_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 2, 1, 1, 1, 1, 5, 2].length) (baseStart_3348657 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348657 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348657 prefixEnd_3348657 := by exact prefixLift 3348657
  have htrace : WordTrace (prefixWord ++ tailWord_3348657) baseStart_3348657 baseEnd_3348657 := by
    simpa [prefixWord, tailWord_3348657, baseEnd_3348657] using wordTrace_append hprefix tailTrace_3348657
  have hstable : (prefixWord ++ tailWord_3348657).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348657).length < 2 ^ (prefixWord ++ tailWord_3348657).sum := by decide
  have hdescent : baseEnd_3348657 < baseStart_3348657 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348657) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348663 : List Nat := [1, 1, 3, 1, 4, 2, 2, 2, 1, 6]
def baseStart_3348663 : Nat := 118140960795 + 3348663 * 2 ^ 59
def prefixEnd_3348663 : Nat := 4983230072969 + 3 ^ 40 * 3348663 * 2
def baseEnd_3348663 : Nat := 573157889642312358104095

theorem tailTrace_3348663 : CollatzResearch.WordTrace tailWord_3348663 prefixEnd_3348663 573157889642312358104095 := by
  unfold tailWord_3348663
  simp only [CollatzResearch.WordTrace]
  refine ⟨122135773467373331953738643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81423848978248887969159095 122135773467373331953738643)
  ·
    refine ⟨183203660201059997930607965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122135773467373331953738643 183203660201059997930607965)
    ·
      refine ⟨68701372575397499223977987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183203660201059997930607965 68701372575397499223977987)
      ·
        refine ⟨103052058863096248835966981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68701372575397499223977987 103052058863096248835966981)
        ·
          refine ⟨19322261036830546656743809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103052058863096248835966981 19322261036830546656743809)
          ·
            refine ⟨14491695777622909992557857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19322261036830546656743809 14491695777622909992557857)
            ·
              refine ⟨10868771833217182494418393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14491695777622909992557857 10868771833217182494418393)
              ·
                refine ⟨8151578874912886870813795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10868771833217182494418393 8151578874912886870813795)
                ·
                  refine ⟨12227368312369330306220693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151578874912886870813795 12227368312369330306220693)
                  ·
                    refine ⟨573157889642312358104095, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12227368312369330306220693 573157889642312358104095)
                    ·
                      rfl

theorem cell23_3348663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 4, 2, 2, 2, 1, 6].length) (baseStart_3348663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348663 prefixEnd_3348663 := by exact prefixLift 3348663
  have htrace : WordTrace (prefixWord ++ tailWord_3348663) baseStart_3348663 baseEnd_3348663 := by
    simpa [prefixWord, tailWord_3348663, baseEnd_3348663] using wordTrace_append hprefix tailTrace_3348663
  have hstable : (prefixWord ++ tailWord_3348663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348663).length < 2 ^ (prefixWord ++ tailWord_3348663).sum := by decide
  have hdescent : baseEnd_3348663 < baseStart_3348663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348687 : List Nat := [1, 1, 2, 1, 1, 3, 6, 1, 3, 2, 2]
def baseStart_3348687 : Nat := 118140960795 + 3348687 * 2 ^ 59
def prefixEnd_3348687 : Nat := 4983230072969 + 3 ^ 40 * 3348687 * 2
def baseEnd_3348687 : Nat := 1719485992462644980412175

theorem tailTrace_3348687 : CollatzResearch.WordTrace tailWord_3348687 prefixEnd_3348687 1719485992462644980412175 := by
  unfold tailWord_3348687
  simp only [CollatzResearch.WordTrace]
  refine ⟨122136648819286384052612315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81424432546190922701741543 122136648819286384052612315)
  ·
    refine ⟨183204973228929576078918473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122136648819286384052612315 183204973228929576078918473)
    ·
      refine ⟨137403729921697182059188855, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183204973228929576078918473 137403729921697182059188855)
      ·
        refine ⟨206105594882545773088783283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137403729921697182059188855 206105594882545773088783283)
        ·
          refine ⟨309158392323818659633174925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206105594882545773088783283 309158392323818659633174925)
          ·
            refine ⟨115934397121431997362440597, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309158392323818659633174925 115934397121431997362440597)
            ·
              refine ⟨5434424865067124876364403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 115934397121431997362440597 5434424865067124876364403)
              ·
                refine ⟨8151637297600687314546605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434424865067124876364403 8151637297600687314546605)
                ·
                  refine ⟨3056863986600257742954977, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8151637297600687314546605 3056863986600257742954977)
                  ·
                    refine ⟨2292647989950193307216233, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056863986600257742954977 2292647989950193307216233)
                    ·
                      refine ⟨1719485992462644980412175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292647989950193307216233 1719485992462644980412175)
                      ·
                        rfl

theorem cell23_3348687_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 3, 6, 1, 3, 2, 2].length) (baseStart_3348687 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348687 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348687 prefixEnd_3348687 := by exact prefixLift 3348687
  have htrace : WordTrace (prefixWord ++ tailWord_3348687) baseStart_3348687 baseEnd_3348687 := by
    simpa [prefixWord, tailWord_3348687, baseEnd_3348687] using wordTrace_append hprefix tailTrace_3348687
  have hstable : (prefixWord ++ tailWord_3348687).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348687).length < 2 ^ (prefixWord ++ tailWord_3348687).sum := by decide
  have hdescent : baseEnd_3348687 < baseStart_3348687 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348687) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348690 : List Nat := [3, 2, 2, 2, 1, 3, 1, 2, 1, 1, 5]
def baseStart_3348690 : Nat := 118140960795 + 3348690 * 2 ^ 59
def prefixEnd_3348690 : Nat := 4983230072969 + 3 ^ 40 * 3348690 * 2
def baseEnd_3348690 : Nat := 1719487532904608468674661

theorem tailTrace_3348690 : CollatzResearch.WordTrace tailWord_3348690 prefixEnd_3348690 1719487532904608468674661 := by
  unfold tailWord_3348690
  simp only [CollatzResearch.WordTrace]
  refine ⟨30534189559568878891242881, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81424505492183677043314349 30534189559568878891242881)
  ·
    refine ⟨22900642169676659168432161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30534189559568878891242881 22900642169676659168432161)
    ·
      refine ⟨17175481627257494376324121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22900642169676659168432161 17175481627257494376324121)
      ·
        refine ⟨12881611220443120782243091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17175481627257494376324121 12881611220443120782243091)
        ·
          refine ⟨19322416830664681173364637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12881611220443120782243091 19322416830664681173364637)
          ·
            refine ⟨7245906311499255440011739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19322416830664681173364637 7245906311499255440011739)
            ·
              refine ⟨10868859467248883160017609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7245906311499255440011739 10868859467248883160017609)
              ·
                refine ⟨8151644600436662370013207, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10868859467248883160017609 8151644600436662370013207)
                ·
                  refine ⟨12227466900654993555019811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8151644600436662370013207 12227466900654993555019811)
                  ·
                    refine ⟨18341200350982490332529717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12227466900654993555019811 18341200350982490332529717)
                    ·
                      refine ⟨1719487532904608468674661, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18341200350982490332529717 1719487532904608468674661)
                      ·
                        rfl

theorem cell23_3348690_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 3, 1, 2, 1, 1, 5].length) (baseStart_3348690 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348690 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348690 prefixEnd_3348690 := by exact prefixLift 3348690
  have htrace : WordTrace (prefixWord ++ tailWord_3348690) baseStart_3348690 baseEnd_3348690 := by
    simpa [prefixWord, tailWord_3348690, baseEnd_3348690] using wordTrace_append hprefix tailTrace_3348690
  have hstable : (prefixWord ++ tailWord_3348690).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348690).length < 2 ^ (prefixWord ++ tailWord_3348690).sum := by decide
  have hdescent : baseEnd_3348690 < baseStart_3348690 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348690) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348737 : List Nat := [1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 3]
def baseStart_3348737 : Nat := 118140960795 + 3348737 * 2 ^ 59
def prefixEnd_3348737 : Nat := 4983230072969 + 3 ^ 40 * 3348737 * 2
def baseEnd_3348737 : Nat := 1719511666495369784786945

theorem tailTrace_3348737 : CollatzResearch.WordTrace tailWord_3348737 prefixEnd_3348737 1719511666495369784786945 := by
  unfold tailWord_3348737
  simp only [CollatzResearch.WordTrace]
  refine ⟨122138472469105242591932465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81425648312736828394621643 122138472469105242591932465)
  ·
    refine ⟨91603854351828931943949349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122138472469105242591932465 91603854351828931943949349)
    ·
      refine ⟨17175722690967924739490503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91603854351828931943949349 17175722690967924739490503)
      ·
        refine ⟨25763584036451887109235755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17175722690967924739490503 25763584036451887109235755)
        ·
          refine ⟨38645376054677830663853633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25763584036451887109235755 38645376054677830663853633)
          ·
            refine ⟨28984032041008372997890225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38645376054677830663853633 28984032041008372997890225)
            ·
              refine ⟨21738024030756279748417669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28984032041008372997890225 21738024030756279748417669)
              ·
                refine ⟨4075879505766802452828313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21738024030756279748417669 4075879505766802452828313)
                ·
                  refine ⟨3056909629325101839621235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075879505766802452828313 3056909629325101839621235)
                  ·
                    refine ⟨4585364443987652759431853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3056909629325101839621235 4585364443987652759431853)
                    ·
                      refine ⟨1719511666495369784786945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4585364443987652759431853 1719511666495369784786945)
                      ·
                        rfl

theorem cell23_3348737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 2, 2, 4, 2, 1, 3].length) (baseStart_3348737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348737 prefixEnd_3348737 := by exact prefixLift 3348737
  have htrace : WordTrace (prefixWord ++ tailWord_3348737) baseStart_3348737 baseEnd_3348737 := by
    simpa [prefixWord, tailWord_3348737, baseEnd_3348737] using wordTrace_append hprefix tailTrace_3348737
  have hstable : (prefixWord ++ tailWord_3348737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348737).length < 2 ^ (prefixWord ++ tailWord_3348737).sum := by decide
  have hdescent : baseEnd_3348737 < baseStart_3348737 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348763 : List Nat := [1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5]
def baseStart_3348763 : Nat := 118140960795 + 3348763 * 2 ^ 59
def prefixEnd_3348763 : Nat := 4983230072969 + 3 ^ 40 * 3348763 * 2
def baseEnd_3348763 : Nat := 1719525016992386683061825

theorem tailTrace_3348763 : CollatzResearch.WordTrace tailWord_3348763 prefixEnd_3348763 1719525016992386683061825 := by
  unfold tailWord_3348763
  simp only [CollatzResearch.WordTrace]
  refine ⟨122139420767011049032378943, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81426280511340699354919295 122139420767011049032378943)
  ·
    refine ⟨183209131150516573548568415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122139420767011049032378943 183209131150516573548568415)
    ·
      refine ⟨274813696725774860322852623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183209131150516573548568415 274813696725774860322852623)
      ·
        refine ⟨412220545088662290484278935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274813696725774860322852623 412220545088662290484278935)
        ·
          refine ⟨618330817632993435726418403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412220545088662290484278935 618330817632993435726418403)
          ·
            refine ⟨927496226449490153589627605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 618330817632993435726418403 927496226449490153589627605)
            ·
              refine ⟨21738192807409925474756897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 927496226449490153589627605 21738192807409925474756897)
              ·
                refine ⟨16303644605557444106067673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21738192807409925474756897 16303644605557444106067673)
                ·
                  refine ⟨12227733454168083079550755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16303644605557444106067673 12227733454168083079550755)
                  ·
                    refine ⟨18341600181252124619326133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12227733454168083079550755 18341600181252124619326133)
                    ·
                      refine ⟨1719525016992386683061825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18341600181252124619326133 1719525016992386683061825)
                      ·
                        rfl

theorem cell23_3348763_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 1, 7, 2, 2, 1, 5].length) (baseStart_3348763 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348763 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348763 prefixEnd_3348763 := by exact prefixLift 3348763
  have htrace : WordTrace (prefixWord ++ tailWord_3348763) baseStart_3348763 baseEnd_3348763 := by
    simpa [prefixWord, tailWord_3348763, baseEnd_3348763] using wordTrace_append hprefix tailTrace_3348763
  have hstable : (prefixWord ++ tailWord_3348763).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348763).length < 2 ^ (prefixWord ++ tailWord_3348763).sum := by decide
  have hdescent : baseEnd_3348763 < baseStart_3348763 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348763) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348794 : List Nat := [3, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2]
def baseStart_3348794 : Nat := 118140960795 + 3348794 * 2 ^ 59
def prefixEnd_3348794 : Nat := 4983230072969 + 3 ^ 40 * 3348794 * 2
def baseEnd_3348794 : Nat := 1719540934892676061774183

theorem tailTrace_3348794 : CollatzResearch.WordTrace tailWord_3348794 prefixEnd_3348794 1719540934892676061774183 := by
  unfold tailWord_3348794
  simp only [CollatzResearch.WordTrace]
  refine ⟨30535137857474685331689359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81427034286599160884504957 30535137857474685331689359)
  ·
    refine ⟨45802706786212027997534039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30535137857474685331689359 45802706786212027997534039)
    ·
      refine ⟨68704060179318041996301059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45802706786212027997534039 68704060179318041996301059)
      ·
        refine ⟨103056090268977062994451589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68704060179318041996301059 103056090268977062994451589)
        ·
          refine ⟨19323016925433199311459673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103056090268977062994451589 19323016925433199311459673)
          ·
            refine ⟨14492262694074899483594755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19323016925433199311459673 14492262694074899483594755)
            ·
              refine ⟨21738394041112349225392133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492262694074899483594755 21738394041112349225392133)
              ·
                refine ⟨4075948882708565479761025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21738394041112349225392133 4075948882708565479761025)
                ·
                  refine ⟨3056961662031424109820769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4075948882708565479761025 3056961662031424109820769)
                  ·
                    refine ⟨2292721246523568082365577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3056961662031424109820769 2292721246523568082365577)
                    ·
                      refine ⟨1719540934892676061774183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292721246523568082365577 1719540934892676061774183)
                      ·
                        rfl

theorem cell23_3348794_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 2, 1, 4, 2, 2, 2].length) (baseStart_3348794 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348794 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348794 prefixEnd_3348794 := by exact prefixLift 3348794
  have htrace : WordTrace (prefixWord ++ tailWord_3348794) baseStart_3348794 baseEnd_3348794 := by
    simpa [prefixWord, tailWord_3348794, baseEnd_3348794] using wordTrace_append hprefix tailTrace_3348794
  have hstable : (prefixWord ++ tailWord_3348794).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348794).length < 2 ^ (prefixWord ++ tailWord_3348794).sum := by decide
  have hdescent : baseEnd_3348794 < baseStart_3348794 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348794) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348834 : List Nat := [3, 3, 2, 1, 1, 3, 2, 3, 5]
def baseStart_3348834 : Nat := 118140960795 + 3348834 * 2 ^ 59
def prefixEnd_3348834 : Nat := 4983230072969 + 3 ^ 40 * 3348834 * 2
def baseEnd_3348834 : Nat := 191062386013206211697111

theorem tailTrace_3348834 : CollatzResearch.WordTrace tailWord_3348834 prefixEnd_3348834 191062386013206211697111 := by
  unfold tailWord_3348834
  simp only [CollatzResearch.WordTrace]
  refine ⟨30535502587438457039553389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81428006899835885438809037 30535502587438457039553389)
  ·
    refine ⟨11450813470289421389832521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30535502587438457039553389 11450813470289421389832521)
    ·
      refine ⟨8588110102717066042374391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11450813470289421389832521 8588110102717066042374391)
      ·
        refine ⟨12882165154075599063561587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588110102717066042374391 12882165154075599063561587)
        ·
          refine ⟨19323247731113398595342381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12882165154075599063561587 19323247731113398595342381)
          ·
            refine ⟨7246217899167524473253393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19323247731113398595342381 7246217899167524473253393)
            ·
              refine ⟨5434663424375643354940045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7246217899167524473253393 5434663424375643354940045)
              ·
                refine ⟨2037998784140866258102517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5434663424375643354940045 2037998784140866258102517)
                ·
                  refine ⟨191062386013206211697111, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2037998784140866258102517 191062386013206211697111)
                  ·
                    rfl

theorem cell23_3348834_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 3, 2, 3, 5].length) (baseStart_3348834 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348834 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348834 prefixEnd_3348834 := by exact prefixLift 3348834
  have htrace : WordTrace (prefixWord ++ tailWord_3348834) baseStart_3348834 baseEnd_3348834 := by
    simpa [prefixWord, tailWord_3348834, baseEnd_3348834] using wordTrace_append hprefix tailTrace_3348834
  have hstable : (prefixWord ++ tailWord_3348834).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348834).length < 2 ^ (prefixWord ++ tailWord_3348834).sum := by decide
  have hdescent : baseEnd_3348834 < baseStart_3348834 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348834) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348883 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9]
def baseStart_3348883 : Nat := 118140960795 + 3348883 * 2 ^ 59
def prefixEnd_3348883 : Nat := 4983230072969 + 3 ^ 40 * 3348883 * 2
def baseEnd_3348883 : Nat := 1719586634670926213561273

theorem tailTrace_3348883 : CollatzResearch.WordTrace tailWord_3348883 prefixEnd_3348883 1719586634670926213561273 := by
  unfold tailWord_3348883
  simp only [CollatzResearch.WordTrace]
  refine ⟨122143797526576309526747303, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81429198351050873017831535 122143797526576309526747303)
  ·
    refine ⟨183215696289864464290120955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122143797526576309526747303 183215696289864464290120955)
    ·
      refine ⟨274823544434796696435181433, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183215696289864464290120955 274823544434796696435181433)
      ·
        refine ⟨206117658326097522326386075, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274823544434796696435181433 206117658326097522326386075)
        ·
          refine ⟨309176487489146283489579113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206117658326097522326386075 309176487489146283489579113)
          ·
            refine ⟨231882365616859712617184335, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309176487489146283489579113 231882365616859712617184335)
            ·
              refine ⟨347823548425289568925776503, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231882365616859712617184335 347823548425289568925776503)
              ·
                refine ⟨521735322637934353388664755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347823548425289568925776503 521735322637934353388664755)
                ·
                  refine ⟨782602983956901530082997133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521735322637934353388664755 782602983956901530082997133)
                  ·
                    refine ⟨293476118983838073781123925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 782602983956901530082997133 293476118983838073781123925)
                    ·
                      refine ⟨1719586634670926213561273, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 293476118983838073781123925 1719586634670926213561273)
                      ·
                        rfl

theorem cell23_3348883_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 1, 3, 9].length) (baseStart_3348883 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348883 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348883 prefixEnd_3348883 := by exact prefixLift 3348883
  have htrace : WordTrace (prefixWord ++ tailWord_3348883) baseStart_3348883 baseEnd_3348883 := by
    simpa [prefixWord, tailWord_3348883, baseEnd_3348883] using wordTrace_append hprefix tailTrace_3348883
  have hstable : (prefixWord ++ tailWord_3348883).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348883).length < 2 ^ (prefixWord ++ tailWord_3348883).sum := by decide
  have hdescent : baseEnd_3348883 < baseStart_3348883 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348883) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348890 : List Nat := [3, 1, 1, 4, 1, 2, 1, 2, 8]
def baseStart_3348890 : Nat := 118140960795 + 3348890 * 2 ^ 59
def prefixEnd_3348890 : Nat := 4983230072969 + 3 ^ 40 * 3348890 * 2
def baseEnd_3348890 : Nat := 191065581003945298463749

theorem tailTrace_3348890 : CollatzResearch.WordTrace tailWord_3348890 prefixEnd_3348890 191065581003945298463749 := by
  unfold tailWord_3348890
  simp only [CollatzResearch.WordTrace]
  refine ⟨30536013209387737430563031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81429368558367299814834749 30536013209387737430563031)
  ·
    refine ⟨45804019814081606145844547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30536013209387737430563031 45804019814081606145844547)
    ·
      refine ⟨68706029721122409218766821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45804019814081606145844547 68706029721122409218766821)
      ·
        refine ⟨12882380572710451728518779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68706029721122409218766821 12882380572710451728518779)
        ·
          refine ⟨19323570859065677592778169, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12882380572710451728518779 19323570859065677592778169)
          ·
            refine ⟨14492678144299258194583627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19323570859065677592778169 14492678144299258194583627)
            ·
              refine ⟨21739017216448887291875441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492678144299258194583627 21739017216448887291875441)
              ·
                refine ⟨16304262912336665468906581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21739017216448887291875441 16304262912336665468906581)
                ·
                  refine ⟨191065581003945298463749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16304262912336665468906581 191065581003945298463749)
                  ·
                    rfl

theorem cell23_3348890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 2, 1, 2, 8].length) (baseStart_3348890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348890 prefixEnd_3348890 := by exact prefixLift 3348890
  have htrace : WordTrace (prefixWord ++ tailWord_3348890) baseStart_3348890 baseEnd_3348890 := by
    simpa [prefixWord, tailWord_3348890, baseEnd_3348890] using wordTrace_append hprefix tailTrace_3348890
  have hstable : (prefixWord ++ tailWord_3348890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348890).length < 2 ^ (prefixWord ++ tailWord_3348890).sum := by decide
  have hdescent : baseEnd_3348890 < baseStart_3348890 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348904 : List Nat := [2, 1, 6, 1, 1, 1, 1, 1, 4, 2, 3]
def baseStart_3348904 : Nat := 118140960795 + 3348904 * 2 ^ 59
def prefixEnd_3348904 : Nat := 4983230072969 + 3 ^ 40 * 3348904 * 2
def baseEnd_3348904 : Nat := 1719597417764670631398677

theorem tailTrace_3348904 : CollatzResearch.WordTrace tailWord_3348904 prefixEnd_3348904 1719597417764670631398677 := by
  unfold tailWord_3348904
  simp only [CollatzResearch.WordTrace]
  refine ⟨61072281729750115056630883, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81429708973000153408841177 61072281729750115056630883)
  ·
    refine ⟨91608422594625172584946325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61072281729750115056630883 91608422594625172584946325)
    ·
      refine ⟨4294144809123054964919359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 91608422594625172584946325 4294144809123054964919359)
      ·
        refine ⟨6441217213684582447379039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294144809123054964919359 6441217213684582447379039)
        ·
          refine ⟨9661825820526873671068559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441217213684582447379039 9661825820526873671068559)
          ·
            refine ⟨14492738730790310506602839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661825820526873671068559 14492738730790310506602839)
            ·
              refine ⟨21739108096185465759904259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14492738730790310506602839 21739108096185465759904259)
              ·
                refine ⟨32608662144278198639856389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21739108096185465759904259 32608662144278198639856389)
                ·
                  refine ⟨6114124152052162244973073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32608662144278198639856389 6114124152052162244973073)
                  ·
                    refine ⟨4585593114039121683729805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6114124152052162244973073 4585593114039121683729805)
                    ·
                      refine ⟨1719597417764670631398677, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4585593114039121683729805 1719597417764670631398677)
                      ·
                        rfl

theorem cell23_3348904_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 1, 1, 4, 2, 3].length) (baseStart_3348904 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348904 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348904 prefixEnd_3348904 := by exact prefixLift 3348904
  have htrace : WordTrace (prefixWord ++ tailWord_3348904) baseStart_3348904 baseEnd_3348904 := by
    simpa [prefixWord, tailWord_3348904, baseEnd_3348904] using wordTrace_append hprefix tailTrace_3348904
  have hstable : (prefixWord ++ tailWord_3348904).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348904).length < 2 ^ (prefixWord ++ tailWord_3348904).sum := by decide
  have hdescent : baseEnd_3348904 < baseStart_3348904 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348904) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348920 : List Nat := [2, 1, 2, 1, 2, 2, 1, 4, 3, 5]
def baseStart_3348920 : Nat := 118140960795 + 3348920 * 2 ^ 59
def prefixEnd_3348920 : Nat := 4983230072969 + 3 ^ 40 * 3348920 * 2
def baseEnd_3348920 : Nat := 573201877818380856266201

theorem tailTrace_3348920 : CollatzResearch.WordTrace tailWord_3348920 prefixEnd_3348920 573201877818380856266201 := by
  unfold tailWord_3348920
  simp only [CollatzResearch.WordTrace]
  refine ⟨61072573513721132422922107, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81430098018294843230562809 61072573513721132422922107)
  ·
    refine ⟨91608860270581698634383161, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61072573513721132422922107 91608860270581698634383161)
    ·
      refine ⟨68706645202936273975787371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91608860270581698634383161 68706645202936273975787371)
      ·
        refine ⟨103059967804404410963681057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68706645202936273975787371 103059967804404410963681057)
        ·
          refine ⟨77294975853303308222760793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103059967804404410963681057 77294975853303308222760793)
          ·
            refine ⟨57971231889977481167070595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77294975853303308222760793 57971231889977481167070595)
            ·
              refine ⟨86956847834966221750605893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57971231889977481167070595 86956847834966221750605893)
              ·
                refine ⟨16304408969056166578238605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86956847834966221750605893 16304408969056166578238605)
                ·
                  refine ⟨6114153363396062466839477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16304408969056166578238605 6114153363396062466839477)
                  ·
                    refine ⟨573201877818380856266201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6114153363396062466839477 573201877818380856266201)
                    ·
                      rfl

theorem cell23_3348920_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 1, 4, 3, 5].length) (baseStart_3348920 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348920 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348920 prefixEnd_3348920 := by exact prefixLift 3348920
  have htrace : WordTrace (prefixWord ++ tailWord_3348920) baseStart_3348920 baseEnd_3348920 := by
    simpa [prefixWord, tailWord_3348920, baseEnd_3348920] using wordTrace_append hprefix tailTrace_3348920
  have hstable : (prefixWord ++ tailWord_3348920).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348920).length < 2 ^ (prefixWord ++ tailWord_3348920).sum := by decide
  have hdescent : baseEnd_3348920 < baseStart_3348920 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348920) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348924 : List Nat := [2, 2, 2, 4, 1, 1, 4, 1, 6]
def baseStart_3348924 : Nat := 118140960795 + 3348924 * 2 ^ 59
def prefixEnd_3348924 : Nat := 4983230072969 + 3 ^ 40 * 3348924 * 2
def baseEnd_3348924 : Nat := 191067520819751172572065

theorem tailTrace_3348924 : CollatzResearch.WordTrace tailWord_3348924 prefixEnd_3348924 191067520819751172572065 := by
  unfold tailWord_3348924
  simp only [CollatzResearch.WordTrace]
  refine ⟨61072646459713886764494913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81430195279618515685993217 61072646459713886764494913)
  ·
    refine ⟨45804484844785415073371185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61072646459713886764494913 45804484844785415073371185)
    ·
      refine ⟨34353363633589061305028389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45804484844785415073371185 34353363633589061305028389)
      ·
        refine ⟨6441255681297948994692823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34353363633589061305028389 6441255681297948994692823)
        ·
          refine ⟨9661883521946923492039235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441255681297948994692823 9661883521946923492039235)
          ·
            refine ⟨14492825282920385238058853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9661883521946923492039235 14492825282920385238058853)
            ·
              refine ⟨2717404740547572232136035, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14492825282920385238058853 2717404740547572232136035)
              ·
                refine ⟨4076107110821358348204053, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717404740547572232136035 4076107110821358348204053)
                ·
                  refine ⟨191067520819751172572065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4076107110821358348204053 191067520819751172572065)
                  ·
                    rfl

theorem cell23_3348924_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 1, 1, 4, 1, 6].length) (baseStart_3348924 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348924 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348924 prefixEnd_3348924 := by exact prefixLift 3348924
  have htrace : WordTrace (prefixWord ++ tailWord_3348924) baseStart_3348924 baseEnd_3348924 := by
    simpa [prefixWord, tailWord_3348924, baseEnd_3348924] using wordTrace_append hprefix tailTrace_3348924
  have hstable : (prefixWord ++ tailWord_3348924).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348924).length < 2 ^ (prefixWord ++ tailWord_3348924).sum := by decide
  have hdescent : baseEnd_3348924 < baseStart_3348924 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348924) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348937 : List Nat := [1, 2, 1, 1, 2, 1, 7, 2, 1, 5]
def baseStart_3348937 : Nat := 118140960795 + 3348937 * 2 ^ 59
def prefixEnd_3348937 : Nat := 4983230072969 + 3 ^ 40 * 3348937 * 2
def baseEnd_3348937 : Nat := 573204787542089667428675

theorem tailTrace_3348937 : CollatzResearch.WordTrace tailWord_3348937 prefixEnd_3348937 573204787542089667428675 := by
  unfold tailWord_3348937
  simp only [CollatzResearch.WordTrace]
  refine ⟨122145767068380676749213065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81430511378920451166142043 122145767068380676749213065)
  ·
    refine ⟨91609325301285507561909799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122145767068380676749213065 91609325301285507561909799)
    ·
      refine ⟨137413987951928261342864699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91609325301285507561909799 137413987951928261342864699)
      ·
        refine ⟨206120981927892392014297049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137413987951928261342864699 206120981927892392014297049)
        ·
          refine ⟨154590736445919294010722787, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206120981927892392014297049 154590736445919294010722787)
          ·
            refine ⟨231886104668878941016084181, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154590736445919294010722787 231886104668878941016084181)
            ·
              refine ⟨5434830578176850180064473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 231886104668878941016084181 5434830578176850180064473)
              ·
                refine ⟨4076122933632637635048355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5434830578176850180064473 4076122933632637635048355)
                ·
                  refine ⟨6114184400448956452572533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076122933632637635048355 6114184400448956452572533)
                  ·
                    refine ⟨573204787542089667428675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6114184400448956452572533 573204787542089667428675)
                    ·
                      rfl

theorem cell23_3348937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 1, 7, 2, 1, 5].length) (baseStart_3348937 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348937 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348937 prefixEnd_3348937 := by exact prefixLift 3348937
  have htrace : WordTrace (prefixWord ++ tailWord_3348937) baseStart_3348937 baseEnd_3348937 := by
    simpa [prefixWord, tailWord_3348937, baseEnd_3348937] using wordTrace_append hprefix tailTrace_3348937
  have hstable : (prefixWord ++ tailWord_3348937).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348937).length < 2 ^ (prefixWord ++ tailWord_3348937).sum := by decide
  have hdescent : baseEnd_3348937 < baseStart_3348937 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348954 : List Nat := [3, 1, 1, 2, 3, 1, 5, 1, 1, 5]
def baseStart_3348954 : Nat := 118140960795 + 3348954 * 2 ^ 59
def prefixEnd_3348954 : Nat := 4983230072969 + 3 ^ 40 * 3348954 * 2
def baseEnd_3348954 : Nat := 573207697265798478591149

theorem tailTrace_3348954 : CollatzResearch.WordTrace tailWord_3348954 prefixEnd_3348954 573207697265798478591149 := by
  unfold tailWord_3348954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30536596777329772163145479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81430924739546059101721277 30536596777329772163145479)
  ·
    refine ⟨45804895165994658244718219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30536596777329772163145479 45804895165994658244718219)
    ·
      refine ⟨68707342748991987367077329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45804895165994658244718219 68707342748991987367077329)
      ·
        refine ⟨51530507061743990525307997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68707342748991987367077329 51530507061743990525307997)
        ·
          refine ⟨19323940148153996446990499, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51530507061743990525307997 19323940148153996446990499)
          ·
            refine ⟨28985910222230994670485749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19323940148153996446990499 28985910222230994670485749)
            ·
              refine ⟨2717429083334155750358039, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 28985910222230994670485749 2717429083334155750358039)
              ·
                refine ⟨4076143625001233625537059, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717429083334155750358039 4076143625001233625537059)
                ·
                  refine ⟨6114215437501850438305589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076143625001233625537059 6114215437501850438305589)
                  ·
                    refine ⟨573207697265798478591149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6114215437501850438305589 573207697265798478591149)
                    ·
                      rfl

theorem cell23_3348954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 5, 1, 1, 5].length) (baseStart_3348954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348954 prefixEnd_3348954 := by exact prefixLift 3348954
  have htrace : WordTrace (prefixWord ++ tailWord_3348954) baseStart_3348954 baseEnd_3348954 := by
    simpa [prefixWord, tailWord_3348954, baseEnd_3348954] using wordTrace_append hprefix tailTrace_3348954
  have hstable : (prefixWord ++ tailWord_3348954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348954).length < 2 ^ (prefixWord ++ tailWord_3348954).sum := by decide
  have hdescent : baseEnd_3348954 < baseStart_3348954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348962 : List Nat := [3, 3, 3, 2, 1, 2, 2, 2, 1, 4]
def baseStart_3348962 : Nat := 118140960795 + 3348962 * 2 ^ 59
def prefixEnd_3348962 : Nat := 4983230072969 + 3 ^ 40 * 3348962 * 2
def baseEnd_3348962 : Nat := 573209066547543801491137

theorem tailTrace_3348962 : CollatzResearch.WordTrace tailWord_3348962 prefixEnd_3348962 573209066547543801491137 := by
  unfold tailWord_3348962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30536669723322526504718285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81431119262193404012582093 30536669723322526504718285)
  ·
    refine ⟨11451251146245947439269357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30536669723322526504718285 11451251146245947439269357)
    ·
      refine ⟨4294219179842230289726009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11451251146245947439269357 4294219179842230289726009)
      ·
        refine ⟨3220664384881672717294507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4294219179842230289726009 3220664384881672717294507)
        ·
          refine ⟨4830996577322509075941761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3220664384881672717294507 4830996577322509075941761)
          ·
            refine ⟨3623247432991881806956321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4830996577322509075941761 3623247432991881806956321)
            ·
              refine ⟨2717435574743911355217241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623247432991881806956321 2717435574743911355217241)
              ·
                refine ⟨2038076681057933516412931, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717435574743911355217241 2038076681057933516412931)
                ·
                  refine ⟨3057115021586900274619397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038076681057933516412931 3057115021586900274619397)
                  ·
                    refine ⟨573209066547543801491137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3057115021586900274619397 573209066547543801491137)
                    ·
                      rfl

theorem cell23_3348962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 3, 2, 1, 2, 2, 2, 1, 4].length) (baseStart_3348962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348962 prefixEnd_3348962 := by exact prefixLift 3348962
  have htrace : WordTrace (prefixWord ++ tailWord_3348962) baseStart_3348962 baseEnd_3348962 := by
    simpa [prefixWord, tailWord_3348962, baseEnd_3348962] using wordTrace_append hprefix tailTrace_3348962
  have hstable : (prefixWord ++ tailWord_3348962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348962).length < 2 ^ (prefixWord ++ tailWord_3348962).sum := by decide
  have hdescent : baseEnd_3348962 < baseStart_3348962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348968 : List Nat := [2, 1, 4, 1, 1, 3, 4, 2, 1, 1, 3]
def baseStart_3348968 : Nat := 118140960795 + 3348968 * 2 ^ 59
def prefixEnd_3348968 : Nat := 4983230072969 + 3 ^ 40 * 3348968 * 2
def baseEnd_3348968 : Nat := 1719630280526558380998383

theorem tailTrace_3348968 : CollatzResearch.WordTrace tailWord_3348968 prefixEnd_3348968 1719630280526558380998383 := by
  unfold tailWord_3348968
  simp only [CollatzResearch.WordTrace]
  refine ⟨61073448865634184521795779, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81431265154178912695727705 61073448865634184521795779)
  ·
    refine ⟨91610173298451276782693669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61073448865634184521795779 91610173298451276782693669)
    ·
      refine ⟨17176907493459614396755063, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91610173298451276782693669 17176907493459614396755063)
      ·
        refine ⟨25765361240189421595132595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17176907493459614396755063 25765361240189421595132595)
        ·
          refine ⟨38648041860284132392698893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25765361240189421595132595 38648041860284132392698893)
          ·
            refine ⟨14493015697606549647262085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38648041860284132392698893 14493015697606549647262085)
            ·
              refine ⟨2717440443301228058861641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14493015697606549647262085 2717440443301228058861641)
              ·
                refine ⟨2038080332475921044146231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717440443301228058861641 2038080332475921044146231)
                ·
                  refine ⟨3057120498713881566219347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038080332475921044146231 3057120498713881566219347)
                  ·
                    refine ⟨4585680748070822349329021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3057120498713881566219347 4585680748070822349329021)
                    ·
                      refine ⟨1719630280526558380998383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4585680748070822349329021 1719630280526558380998383)
                      ·
                        rfl

theorem cell23_3348968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 4, 2, 1, 1, 3].length) (baseStart_3348968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348968 prefixEnd_3348968 := by exact prefixLift 3348968
  have htrace : WordTrace (prefixWord ++ tailWord_3348968) baseStart_3348968 baseEnd_3348968 := by
    simpa [prefixWord, tailWord_3348968, baseEnd_3348968] using wordTrace_append hprefix tailTrace_3348968
  have hstable : (prefixWord ++ tailWord_3348968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348968).length < 2 ^ (prefixWord ++ tailWord_3348968).sum := by decide
  have hdescent : baseEnd_3348968 < baseStart_3348968 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3348977 : List Nat := [1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 3]
def baseStart_3348977 : Nat := 118140960795 + 3348977 * 2 ^ 59
def prefixEnd_3348977 : Nat := 4983230072969 + 3 ^ 40 * 3348977 * 2
def baseEnd_3348977 : Nat := 1719634901852448845785841

theorem tailTrace_3348977 : CollatzResearch.WordTrace tailWord_3348977 prefixEnd_3348977 1719634901852448845785841 := by
  unfold tailWord_3348977
  simp only [CollatzResearch.WordTrace]
  refine ⟨122147225988235763580669185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81431483992157175720446123 122147225988235763580669185)
  ·
    refine ⟨91610419491176822685501889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122147225988235763580669185 91610419491176822685501889)
    ·
      refine ⟨68707814618382617014126417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91610419491176822685501889 68707814618382617014126417)
      ·
        refine ⟨51530860963786962760594813, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68707814618382617014126417 51530860963786962760594813)
        ·
          refine ⟨19324072861420111035223055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51530860963786962760594813 19324072861420111035223055)
          ·
            refine ⟨28986109292130166552834583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19324072861420111035223055 28986109292130166552834583)
            ·
              refine ⟨43479163938195249829251875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28986109292130166552834583 43479163938195249829251875)
              ·
                refine ⟨65218745907292874743877813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43479163938195249829251875 65218745907292874743877813)
                ·
                  refine ⟨6114257428808707007238545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 65218745907292874743877813 6114257428808707007238545)
                  ·
                    refine ⟨4585693071606530255428909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6114257428808707007238545 4585693071606530255428909)
                    ·
                      refine ⟨1719634901852448845785841, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4585693071606530255428909 1719634901852448845785841)
                      ·
                        rfl

theorem cell23_3348977_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 3, 1, 1, 1, 5, 2, 3].length) (baseStart_3348977 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3348977 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3348977 prefixEnd_3348977 := by exact prefixLift 3348977
  have htrace : WordTrace (prefixWord ++ tailWord_3348977) baseStart_3348977 baseEnd_3348977 := by
    simpa [prefixWord, tailWord_3348977, baseEnd_3348977] using wordTrace_append hprefix tailTrace_3348977
  have hstable : (prefixWord ++ tailWord_3348977).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3348977).length < 2 ^ (prefixWord ++ tailWord_3348977).sum := by decide
  have hdescent : baseEnd_3348977 < baseStart_3348977 := by decide
  rcases family_descends (prefixWord ++ tailWord_3348977) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349005 : List Nat := [1, 7, 1, 1, 1, 3, 2, 1, 1, 5]
def baseStart_3349005 : Nat := 118140960795 + 3349005 * 2 ^ 59
def prefixEnd_3349005 : Nat := 4983230072969 + 3 ^ 40 * 3349005 * 2
def baseEnd_3349005 : Nat := 573216426436924912078571

theorem tailTrace_3349005 : CollatzResearch.WordTrace tailWord_3349005 prefixEnd_3349005 573216426436924912078571 := by
  unfold tailWord_3349005
  simp only [CollatzResearch.WordTrace]
  refine ⟨122148247232134324362688469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81432164821422882908458979 122148247232134324362688469)
  ·
    refine ⟨2862849544503148227250511, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 122148247232134324362688469 2862849544503148227250511)
    ·
      refine ⟨4294274316754722340875767, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2862849544503148227250511 4294274316754722340875767)
      ·
        refine ⟨6441411475132083511313651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4294274316754722340875767 6441411475132083511313651)
        ·
          refine ⟨9662117212698125266970477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441411475132083511313651 9662117212698125266970477)
          ·
            refine ⟨3623293954761796975113929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9662117212698125266970477 3623293954761796975113929)
            ·
              refine ⟨2717470466071347731335447, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623293954761796975113929 2717470466071347731335447)
              ·
                refine ⟨4076205699107021597003171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717470466071347731335447 4076205699107021597003171)
                ·
                  refine ⟨6114308548660532395504757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076205699107021597003171 6114308548660532395504757)
                  ·
                    refine ⟨573216426436924912078571, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6114308548660532395504757 573216426436924912078571)
                    ·
                      rfl

theorem cell23_3349005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 2, 1, 1, 5].length) (baseStart_3349005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349005 prefixEnd_3349005 := by exact prefixLift 3349005
  have htrace : WordTrace (prefixWord ++ tailWord_3349005) baseStart_3349005 baseEnd_3349005 := by
    simpa [prefixWord, tailWord_3349005, baseEnd_3349005] using wordTrace_append hprefix tailTrace_3349005
  have hstable : (prefixWord ++ tailWord_3349005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349005).length < 2 ^ (prefixWord ++ tailWord_3349005).sum := by decide
  have hdescent : baseEnd_3349005 < baseStart_3349005 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349038 : List Nat := [4, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4]
def baseStart_3349038 : Nat := 118140960795 + 3349038 * 2 ^ 59
def prefixEnd_3349038 : Nat := 4983230072969 + 3 ^ 40 * 3349038 * 2
def baseEnd_3349038 : Nat := 1719666224172373107123061

theorem tailTrace_3349038 : CollatzResearch.WordTrace tailWord_3349038 prefixEnd_3349038 1719666224172373107123061 := by
  unfold tailWord_3349038
  simp only [CollatzResearch.WordTrace]
  refine ⟨15268681355126846374829971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81432967227343180665759845 15268681355126846374829971)
  ·
    refine ⟨22903022032690269562244957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15268681355126846374829971 22903022032690269562244957)
    ·
      refine ⟨8588633262258851085841859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22903022032690269562244957 8588633262258851085841859)
      ·
        refine ⟨12882949893388276628762789, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588633262258851085841859 12882949893388276628762789)
        ·
          refine ⟨2415553105010301867893023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12882949893388276628762789 2415553105010301867893023)
          ·
            refine ⟨3623329657515452801839535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415553105010301867893023 3623329657515452801839535)
            ·
              refine ⟨5434994486273179202759303, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623329657515452801839535 5434994486273179202759303)
              ·
                refine ⟨8152491729409768804138955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5434994486273179202759303 8152491729409768804138955)
                ·
                  refine ⟨12228737594114653206208433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8152491729409768804138955 12228737594114653206208433)
                  ·
                    refine ⟨9171553195585989904656325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12228737594114653206208433 9171553195585989904656325)
                    ·
                      refine ⟨1719666224172373107123061, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9171553195585989904656325 1719666224172373107123061)
                      ·
                        rfl

theorem cell23_3349038_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 4, 1, 1, 1, 1, 2, 4].length) (baseStart_3349038 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349038 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349038 prefixEnd_3349038 := by exact prefixLift 3349038
  have htrace : WordTrace (prefixWord ++ tailWord_3349038) baseStart_3349038 baseEnd_3349038 := by
    simpa [prefixWord, tailWord_3349038, baseEnd_3349038] using wordTrace_append hprefix tailTrace_3349038
  have hstable : (prefixWord ++ tailWord_3349038).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349038).length < 2 ^ (prefixWord ++ tailWord_3349038).sum := by decide
  have hdescent : baseEnd_3349038 < baseStart_3349038 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349038) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349064 : List Nat := [2, 1, 3, 1, 1, 1, 1, 6, 1, 4, 2]
def baseStart_3349064 : Nat := 118140960795 + 3349064 * 2 ^ 59
def prefixEnd_3349064 : Nat := 4983230072969 + 3 ^ 40 * 3349064 * 2
def baseEnd_3349064 : Nat := 1719679574669390005397941

theorem tailTrace_3349064 : CollatzResearch.WordTrace tailWord_3349064 prefixEnd_3349064 1719679574669390005397941 := by
  unfold tailWord_3349064
  simp only [CollatzResearch.WordTrace]
  refine ⟨61075199569460288719543123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81433599425947051626057497 61075199569460288719543123)
  ·
    refine ⟨91612799354190433079314685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61075199569460288719543123 91612799354190433079314685)
    ·
      refine ⟨34354799757821412404743007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91612799354190433079314685 34354799757821412404743007)
      ·
        refine ⟨51532199636732118607114511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34354799757821412404743007 51532199636732118607114511)
        ·
          refine ⟨77298299455098177910671767, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51532199636732118607114511 77298299455098177910671767)
          ·
            refine ⟨115947449182647266866007651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77298299455098177910671767 115947449182647266866007651)
            ·
              refine ⟨173921173773970900299011477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115947449182647266866007651 173921173773970900299011477)
              ·
                refine ⟨8152555020654885951516163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 173921173773970900299011477 8152555020654885951516163)
                ·
                  refine ⟨12228832530982328927274245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8152555020654885951516163 12228832530982328927274245)
                  ·
                    refine ⟨2292906099559186673863921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12228832530982328927274245 2292906099559186673863921)
                    ·
                      refine ⟨1719679574669390005397941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292906099559186673863921 1719679574669390005397941)
                      ·
                        rfl

theorem cell23_3349064_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 1, 1, 6, 1, 4, 2].length) (baseStart_3349064 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349064 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349064 prefixEnd_3349064 := by exact prefixLift 3349064
  have htrace : WordTrace (prefixWord ++ tailWord_3349064) baseStart_3349064 baseEnd_3349064 := by
    simpa [prefixWord, tailWord_3349064, baseEnd_3349064] using wordTrace_append hprefix tailTrace_3349064
  have hstable : (prefixWord ++ tailWord_3349064).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349064).length < 2 ^ (prefixWord ++ tailWord_3349064).sum := by decide
  have hdescent : baseEnd_3349064 < baseStart_3349064 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349064) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349077 : List Nat := [1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 4]
def baseStart_3349077 : Nat := 118140960795 + 3349077 * 2 ^ 59
def prefixEnd_3349077 : Nat := 4983230072969 + 3 ^ 40 * 3349077 * 2
def baseEnd_3349077 : Nat := 1719686249917898454535381

theorem tailTrace_3349077 : CollatzResearch.WordTrace tailWord_3349077 prefixEnd_3349077 1719686249917898454535381 := by
  unfold tailWord_3349077
  simp only [CollatzResearch.WordTrace]
  refine ⟨122150873287873480659309485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81433915525248987106206323 122150873287873480659309485)
  ·
    refine ⟨45806577482952555247241057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122150873287873480659309485 45806577482952555247241057)
    ·
      refine ⟨34354933112214416435430793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45806577482952555247241057 34354933112214416435430793)
      ·
        refine ⟨25766199834160812326573095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34354933112214416435430793 25766199834160812326573095)
        ·
          refine ⟨38649299751241218489859643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25766199834160812326573095 38649299751241218489859643)
          ·
            refine ⟨57973949626861827734789465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38649299751241218489859643 57973949626861827734789465)
            ·
              refine ⟨43480462220146370801092099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57973949626861827734789465 43480462220146370801092099)
              ·
                refine ⟨65220693330219556201638149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43480462220146370801092099 65220693330219556201638149)
                ·
                  refine ⟨12228879999416166787807153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65220693330219556201638149 12228879999416166787807153)
                  ·
                    refine ⟨9171659999562125090855365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12228879999416166787807153 9171659999562125090855365)
                    ·
                      refine ⟨1719686249917898454535381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9171659999562125090855365 1719686249917898454535381)
                      ·
                        rfl

theorem cell23_3349077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_3349077 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349077 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349077 prefixEnd_3349077 := by exact prefixLift 3349077
  have htrace : WordTrace (prefixWord ++ tailWord_3349077) baseStart_3349077 baseEnd_3349077 := by
    simpa [prefixWord, tailWord_3349077, baseEnd_3349077] using wordTrace_append hprefix tailTrace_3349077
  have hstable : (prefixWord ++ tailWord_3349077).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349077).length < 2 ^ (prefixWord ++ tailWord_3349077).sum := by decide
  have hdescent : baseEnd_3349077 < baseStart_3349077 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349097 : List Nat := [1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 3]
def baseStart_3349097 : Nat := 118140960795 + 3349097 * 2 ^ 59
def prefixEnd_3349097 : Nat := 4983230072969 + 3 ^ 40 * 3349097 * 2
def baseEnd_3349097 : Nat := 1719696519530988376285289

theorem tailTrace_3349097 : CollatzResearch.WordTrace tailWord_3349097 prefixEnd_3349097 1719696519530988376285289 := by
  unfold tailWord_3349097
  simp only [CollatzResearch.WordTrace]
  refine ⟨122151602747801024075037545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81434401831867349383358363 122151602747801024075037545)
  ·
    refine ⟨91613702060850768056278159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122151602747801024075037545 91613702060850768056278159)
    ·
      refine ⟨137420553091276152084417239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91613702060850768056278159 137420553091276152084417239)
      ·
        refine ⟨206130829636914228126625859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137420553091276152084417239 206130829636914228126625859)
        ·
          refine ⟨309196244455371342189938789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206130829636914228126625859 309196244455371342189938789)
          ·
            refine ⟨57974295835382126660613523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309196244455371342189938789 57974295835382126660613523)
            ·
              refine ⟨86961443753073189990920285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57974295835382126660613523 86961443753073189990920285)
              ·
                refine ⟨32610541407402446246595107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86961443753073189990920285 32610541407402446246595107)
                ·
                  refine ⟨48915812111103669369892661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32610541407402446246595107 48915812111103669369892661)
                  ·
                    refine ⟨4585857385415969003427437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48915812111103669369892661 4585857385415969003427437)
                    ·
                      refine ⟨1719696519530988376285289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4585857385415969003427437 1719696519530988376285289)
                      ·
                        rfl

theorem cell23_3349097_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 1, 3, 1, 5, 3].length) (baseStart_3349097 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349097 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349097 prefixEnd_3349097 := by exact prefixLift 3349097
  have htrace : WordTrace (prefixWord ++ tailWord_3349097) baseStart_3349097 baseEnd_3349097 := by
    simpa [prefixWord, tailWord_3349097, baseEnd_3349097] using wordTrace_append hprefix tailTrace_3349097
  have hstable : (prefixWord ++ tailWord_3349097).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349097).length < 2 ^ (prefixWord ++ tailWord_3349097).sum := by decide
  have hdescent : baseEnd_3349097 < baseStart_3349097 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349097) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349098 : List Nat := [3, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2]
def baseStart_3349098 : Nat := 118140960795 + 3349098 * 2 ^ 59
def prefixEnd_3349098 : Nat := 4983230072969 + 3 ^ 40 * 3349098 * 2
def baseEnd_3349098 : Nat := 1719697033011642872372785

theorem tailTrace_3349098 : CollatzResearch.WordTrace tailWord_3349098 prefixEnd_3349098 1719697033011642872372785 := by
  unfold tailWord_3349098
  simp only [CollatzResearch.WordTrace]
  refine ⟨30537909805199350311455987, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81434426147198267497215965 30537909805199350311455987)
  ·
    refine ⟨45806864707799025467183981, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30537909805199350311455987 45806864707799025467183981)
    ·
      refine ⟨17177574265424634550193993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45806864707799025467183981 17177574265424634550193993)
      ·
        refine ⟨12883180699068475912645495, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17177574265424634550193993 12883180699068475912645495)
        ·
          refine ⟨19324771048602713868968243, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12883180699068475912645495 19324771048602713868968243)
          ·
            refine ⟨28987156572904070803452365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19324771048602713868968243 28987156572904070803452365)
            ·
              refine ⟨10870183714839026551294637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28987156572904070803452365 10870183714839026551294637)
              ·
                refine ⟨4076318893064634956735489, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10870183714839026551294637 4076318893064634956735489)
                ·
                  refine ⟨3057239169798476217551617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4076318893064634956735489 3057239169798476217551617)
                  ·
                    refine ⟨2292929377348857163163713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3057239169798476217551617 2292929377348857163163713)
                    ·
                      refine ⟨1719697033011642872372785, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2292929377348857163163713 1719697033011642872372785)
                      ·
                        rfl

theorem cell23_3349098_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 1, 3, 3, 2, 2, 2].length) (baseStart_3349098 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349098 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349098 prefixEnd_3349098 := by exact prefixLift 3349098
  have htrace : WordTrace (prefixWord ++ tailWord_3349098) baseStart_3349098 baseEnd_3349098 := by
    simpa [prefixWord, tailWord_3349098, baseEnd_3349098] using wordTrace_append hprefix tailTrace_3349098
  have hstable : (prefixWord ++ tailWord_3349098).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349098).length < 2 ^ (prefixWord ++ tailWord_3349098).sum := by decide
  have hdescent : baseEnd_3349098 < baseStart_3349098 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349098) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349127 : List Nat := [1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 5]
def baseStart_3349127 : Nat := 118140960795 + 3349127 * 2 ^ 59
def prefixEnd_3349127 : Nat := 4983230072969 + 3 ^ 40 * 3349127 * 2
def baseEnd_3349127 : Nat := 1719711923950623258910151

theorem tailTrace_3349127 : CollatzResearch.WordTrace tailWord_3349127 prefixEnd_3349127 1719711923950623258910151 := by
  unfold tailWord_3349127
  simp only [CollatzResearch.WordTrace]
  refine ⟨122152696937692339198629635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81435131291794892799086423 122152696937692339198629635)
  ·
    refine ⟨183229045406538508797944453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122152696937692339198629635 183229045406538508797944453)
    ·
      refine ⟨34355446013725970399614585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183229045406538508797944453 34355446013725970399614585)
      ·
        refine ⟨25766584510294477799710939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34355446013725970399614585 25766584510294477799710939)
        ·
          refine ⟨38649876765441716699566409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25766584510294477799710939 38649876765441716699566409)
          ·
            refine ⟨28987407574081287524674807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38649876765441716699566409 28987407574081287524674807)
            ·
              refine ⟨43481111361121931287012211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28987407574081287524674807 43481111361121931287012211)
              ·
                refine ⟨65221667041682896930518317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43481111361121931287012211 65221667041682896930518317)
                ·
                  refine ⟨24458125140631086348944369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65221667041682896930518317 24458125140631086348944369)
                  ·
                    refine ⟨18343593855473314761708277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24458125140631086348944369 18343593855473314761708277)
                    ·
                      refine ⟨1719711923950623258910151, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18343593855473314761708277 1719711923950623258910151)
                      ·
                        rfl

theorem cell23_3349127_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 1, 1, 3, 2, 5].length) (baseStart_3349127 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349127 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349127 prefixEnd_3349127 := by exact prefixLift 3349127
  have htrace : WordTrace (prefixWord ++ tailWord_3349127) baseStart_3349127 baseEnd_3349127 := by
    simpa [prefixWord, tailWord_3349127, baseEnd_3349127] using wordTrace_append hprefix tailTrace_3349127
  have hstable : (prefixWord ++ tailWord_3349127).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349127).length < 2 ^ (prefixWord ++ tailWord_3349127).sum := by decide
  have hdescent : baseEnd_3349127 < baseStart_3349127 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349127) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349134 : List Nat := [4, 1, 1, 3, 1, 1, 1, 4, 2, 5]
def baseStart_3349134 : Nat := 118140960795 + 3349134 * 2 ^ 59
def prefixEnd_3349134 : Nat := 4983230072969 + 3 ^ 40 * 3349134 * 2
def baseEnd_3349134 : Nat := 573238506105068243840873

theorem tailTrace_3349134 : CollatzResearch.WordTrace tailWord_3349134 prefixEnd_3349134 573238506105068243840873 := by
  unfold tailWord_3349134
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269119031083372424266807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81435301499111319596089637 15269119031083372424266807)
  ·
    refine ⟨22903678546625058636400211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15269119031083372424266807 22903678546625058636400211)
    ·
      refine ⟨34355517819937587954600317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22903678546625058636400211 34355517819937587954600317)
      ·
        refine ⟨12883319182476595482975119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34355517819937587954600317 12883319182476595482975119)
        ·
          refine ⟨19324978773714893224462679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12883319182476595482975119 19324978773714893224462679)
          ·
            refine ⟨28987468160572339836694019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19324978773714893224462679 28987468160572339836694019)
            ·
              refine ⟨43481202240858509755041029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28987468160572339836694019 43481202240858509755041029)
              ·
                refine ⟨8152725420160970579070193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43481202240858509755041029 8152725420160970579070193)
                ·
                  refine ⟨6114544065120727934302645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8152725420160970579070193 6114544065120727934302645)
                  ·
                    refine ⟨573238506105068243840873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6114544065120727934302645 573238506105068243840873)
                    ·
                      rfl

theorem cell23_3349134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 1, 1, 4, 2, 5].length) (baseStart_3349134 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349134 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349134 prefixEnd_3349134 := by exact prefixLift 3349134
  have htrace : WordTrace (prefixWord ++ tailWord_3349134) baseStart_3349134 baseEnd_3349134 := by
    simpa [prefixWord, tailWord_3349134, baseEnd_3349134] using wordTrace_append hprefix tailTrace_3349134
  have hstable : (prefixWord ++ tailWord_3349134).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349134).length < 2 ^ (prefixWord ++ tailWord_3349134).sum := by decide
  have hdescent : baseEnd_3349134 < baseStart_3349134 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349138 : List Nat := [3, 2, 3, 1, 2, 1, 4, 2, 5]
def baseStart_3349138 : Nat := 118140960795 + 3349138 * 2 ^ 59
def prefixEnd_3349138 : Nat := 4983230072969 + 3 ^ 40 * 3349138 * 2
def baseEnd_3349138 : Nat := 191079730248646968430289

theorem tailTrace_3349138 : CollatzResearch.WordTrace tailWord_3349138 prefixEnd_3349138 191079730248646968430289 := by
  unfold tailWord_3349138
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538274535163122019320017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81435398760434992051520045 30538274535163122019320017)
  ·
    refine ⟨22903705901372341514490013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30538274535163122019320017 22903705901372341514490013)
    ·
      refine ⟨8588889713014628067933755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22903705901372341514490013 8588889713014628067933755)
      ·
        refine ⟨12883334569521942101900633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8588889713014628067933755 12883334569521942101900633)
        ·
          refine ⟨9662500927141456576425475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12883334569521942101900633 9662500927141456576425475)
          ·
            refine ⟨14493751390712184864638213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9662500927141456576425475 14493751390712184864638213)
            ·
              refine ⟨2717578385758534662119665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14493751390712184864638213 2717578385758534662119665)
              ·
                refine ⟨2038183789318900996589749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2717578385758534662119665 2038183789318900996589749)
                ·
                  refine ⟨191079730248646968430289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038183789318900996589749 191079730248646968430289)
                  ·
                    rfl

theorem cell23_3349138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 2, 1, 4, 2, 5].length) (baseStart_3349138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349138 prefixEnd_3349138 := by exact prefixLift 3349138
  have htrace : WordTrace (prefixWord ++ tailWord_3349138) baseStart_3349138 baseEnd_3349138 := by
    simpa [prefixWord, tailWord_3349138, baseEnd_3349138] using wordTrace_append hprefix tailTrace_3349138
  have hstable : (prefixWord ++ tailWord_3349138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349138).length < 2 ^ (prefixWord ++ tailWord_3349138).sum := by decide
  have hdescent : baseEnd_3349138 < baseStart_3349138 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349171 : List Nat := [1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 4]
def baseStart_3349171 : Nat := 118140960795 + 3349171 * 2 ^ 59
def prefixEnd_3349171 : Nat := 4983230072969 + 3 ^ 40 * 3349171 * 2
def baseEnd_3349171 : Nat := 1719734517099421086759949

theorem tailTrace_3349171 : CollatzResearch.WordTrace tailWord_3349171 prefixEnd_3349171 1719734517099421086759949 := by
  unfold tailWord_3349171
  simp only [CollatzResearch.WordTrace]
  refine ⟨122154301749532934713231367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81436201166355289808820911 122154301749532934713231367)
  ·
    refine ⟨183231452624299402069847051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122154301749532934713231367 183231452624299402069847051)
    ·
      refine ⟨274847178936449103104770577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183231452624299402069847051 274847178936449103104770577)
      ·
        refine ⟨206135384202336827328577933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274847178936449103104770577 206135384202336827328577933)
        ·
          refine ⟨77300769075876310248216725, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 206135384202336827328577933 77300769075876310248216725)
          ·
            refine ⟨3623473550431702042885159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 77300769075876310248216725 3623473550431702042885159)
            ·
              refine ⟨5435210325647553064327739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623473550431702042885159 5435210325647553064327739)
              ·
                refine ⟨8152815488471329596491609, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435210325647553064327739 8152815488471329596491609)
                ·
                  refine ⟨6114611616353497197368707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8152815488471329596491609 6114611616353497197368707)
                  ·
                    refine ⟨9171917424530245796053061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6114611616353497197368707 9171917424530245796053061)
                    ·
                      refine ⟨1719734517099421086759949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9171917424530245796053061 1719734517099421086759949)
                      ·
                        rfl

theorem cell23_3349171_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 6, 1, 1, 2, 1, 4].length) (baseStart_3349171 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349171 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349171 prefixEnd_3349171 := by exact prefixLift 3349171
  have htrace : WordTrace (prefixWord ++ tailWord_3349171) baseStart_3349171 baseEnd_3349171 := by
    simpa [prefixWord, tailWord_3349171, baseEnd_3349171] using wordTrace_append hprefix tailTrace_3349171
  have hstable : (prefixWord ++ tailWord_3349171).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349171).length < 2 ^ (prefixWord ++ tailWord_3349171).sum := by decide
  have hdescent : baseEnd_3349171 < baseStart_3349171 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349171) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349177 : List Nat := [1, 2, 1, 4, 1, 1, 1, 4, 8]
def baseStart_3349177 : Nat := 118140960795 + 3349177 * 2 ^ 59
def prefixEnd_3349177 : Nat := 4983230072969 + 3 ^ 40 * 3349177 * 2
def baseEnd_3349177 : Nat := 191081955331483118142769

theorem tailTrace_3349177 : CollatzResearch.WordTrace tailWord_3349177 prefixEnd_3349177 191081955331483118142769 := by
  unfold tailWord_3349177
  simp only [CollatzResearch.WordTrace]
  refine ⟨122154520587511197737949785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81436347058340798491966523 122154520587511197737949785)
  ·
    refine ⟨91615890440633398303462339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122154520587511197737949785 91615890440633398303462339)
    ·
      refine ⟨137423835660950097455193509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91615890440633398303462339 137423835660950097455193509)
      ·
        refine ⟨25766969186428143272848783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137423835660950097455193509 25766969186428143272848783)
        ·
          refine ⟨38650453779642214909273175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25766969186428143272848783 38650453779642214909273175)
          ·
            refine ⟨57975680669463322363909763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38650453779642214909273175 57975680669463322363909763)
            ·
              refine ⟨86963521004194983545864645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57975680669463322363909763 86963521004194983545864645)
              ·
                refine ⟨16305660188286559414849621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86963521004194983545864645 16305660188286559414849621)
                ·
                  refine ⟨191081955331483118142769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16305660188286559414849621 191081955331483118142769)
                  ·
                    rfl

theorem cell23_3349177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 1, 4, 8].length) (baseStart_3349177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349177 prefixEnd_3349177 := by exact prefixLift 3349177
  have htrace : WordTrace (prefixWord ++ tailWord_3349177) baseStart_3349177 baseEnd_3349177 := by
    simpa [prefixWord, tailWord_3349177, baseEnd_3349177] using wordTrace_append hprefix tailTrace_3349177
  have hstable : (prefixWord ++ tailWord_3349177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349177).length < 2 ^ (prefixWord ++ tailWord_3349177).sum := by decide
  have hdescent : baseEnd_3349177 < baseStart_3349177 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349194 : List Nat := [3, 1, 2, 1, 4, 2, 1, 1, 8]
def baseStart_3349194 : Nat := 118140960795 + 3349194 * 2 ^ 59
def prefixEnd_3349194 : Nat := 4983230072969 + 3 ^ 40 * 3349194 * 2
def baseEnd_3349194 : Nat := 191082925239386055196927

theorem tailTrace_3349194 : CollatzResearch.WordTrace tailWord_3349194 prefixEnd_3349194 191082925239386055196927 := by
  unfold tailWord_3349194
  simp only [CollatzResearch.WordTrace]
  refine ⟨30538785157112402410329659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81436760418966406427545757 30538785157112402410329659)
  ·
    refine ⟨45808177735668603615494489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30538785157112402410329659 45808177735668603615494489)
    ·
      refine ⟨34356133301751452711620867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45808177735668603615494489 34356133301751452711620867)
      ·
        refine ⟨51534199952627179067431301, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34356133301751452711620867 51534199952627179067431301)
        ·
          refine ⟨9662662491117596075143369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51534199952627179067431301 9662662491117596075143369)
          ·
            refine ⟨7246996868338197056357527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9662662491117596075143369 7246996868338197056357527)
            ·
              refine ⟨10870495302507295584536291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7246996868338197056357527 10870495302507295584536291)
              ·
                refine ⟨16305742953760943376804437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870495302507295584536291 16305742953760943376804437)
                ·
                  refine ⟨191082925239386055196927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16305742953760943376804437 191082925239386055196927)
                  ·
                    rfl

theorem cell23_3349194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 4, 2, 1, 1, 8].length) (baseStart_3349194 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349194 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349194 prefixEnd_3349194 := by exact prefixLift 3349194
  have htrace : WordTrace (prefixWord ++ tailWord_3349194) baseStart_3349194 baseEnd_3349194 := by
    simpa [prefixWord, tailWord_3349194, baseEnd_3349194] using wordTrace_append hprefix tailTrace_3349194
  have hstable : (prefixWord ++ tailWord_3349194).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349194).length < 2 ^ (prefixWord ++ tailWord_3349194).sum := by decide
  have hdescent : baseEnd_3349194 < baseStart_3349194 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349198 : List Nat := [4, 1, 1, 1, 3, 2, 2, 4, 1, 4]
def baseStart_3349198 : Nat := 118140960795 + 3349198 * 2 ^ 59
def prefixEnd_3349198 : Nat := 4983230072969 + 3 ^ 40 * 3349198 * 2
def baseEnd_3349198 : Nat := 573249460359030827040775

theorem tailTrace_3349198 : CollatzResearch.WordTrace tailWord_3349198 prefixEnd_3349198 573249460359030827040775 := by
  unfold tailWord_3349198
  simp only [CollatzResearch.WordTrace]
  refine ⟨15269410815054389790558031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81436857680290078882976165 15269410815054389790558031)
  ·
    refine ⟨22904116222581584685837047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15269410815054389790558031 22904116222581584685837047)
    ·
      refine ⟨34356174333872377028755571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22904116222581584685837047 34356174333872377028755571)
      ·
        refine ⟨51534261500808565543133357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34356174333872377028755571 51534261500808565543133357)
        ·
          refine ⟨19325348062803212078675009, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51534261500808565543133357 19325348062803212078675009)
          ·
            refine ⟨14494011047102409059006257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19325348062803212078675009 14494011047102409059006257)
            ·
              refine ⟨10870508285326806794254693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14494011047102409059006257 10870508285326806794254693)
              ·
                refine ⟨2038220303498776273922755, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10870508285326806794254693 2038220303498776273922755)
                ·
                  refine ⟨3057330455248164410884133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038220303498776273922755 3057330455248164410884133)
                  ·
                    refine ⟨573249460359030827040775, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3057330455248164410884133 573249460359030827040775)
                    ·
                      rfl

theorem cell23_3349198_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 2, 4, 1, 4].length) (baseStart_3349198 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349198 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349198 prefixEnd_3349198 := by exact prefixLift 3349198
  have htrace : WordTrace (prefixWord ++ tailWord_3349198) baseStart_3349198 baseEnd_3349198 := by
    simpa [prefixWord, tailWord_3349198, baseEnd_3349198] using wordTrace_append hprefix tailTrace_3349198
  have hstable : (prefixWord ++ tailWord_3349198).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349198).length < 2 ^ (prefixWord ++ tailWord_3349198).sum := by decide
  have hdescent : baseEnd_3349198 < baseStart_3349198 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349198) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349231 : List Nat := [1, 1, 2, 1, 5, 2, 2, 1, 1, 5, 2]
def baseStart_3349231 : Nat := 118140960795 + 3349231 * 2 ^ 59
def prefixEnd_3349231 : Nat := 4983230072969 + 3 ^ 40 * 3349231 * 2
def baseEnd_3349231 : Nat := 1719765325938690852009673

theorem tailTrace_3349231 : CollatzResearch.WordTrace tailWord_3349231 prefixEnd_3349231 1719765325938690852009673 := by
  unfold tailWord_3349231
  simp only [CollatzResearch.WordTrace]
  refine ⟨122156490129315564960415547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81437660086210376640277031 122156490129315564960415547)
  ·
    refine ⟨183234735193973347440623321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122156490129315564960415547 183234735193973347440623321)
    ·
      refine ⟨137426051395480010580467491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183234735193973347440623321 137426051395480010580467491)
      ·
        refine ⟨206139077093220015870701237, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137426051395480010580467491 206139077093220015870701237)
        ·
          refine ⟨19325538477489376487878241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206139077093220015870701237 19325538477489376487878241)
          ·
            refine ⟨14494153858117032365908681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19325538477489376487878241 14494153858117032365908681)
            ·
              refine ⟨10870615393587774274431511, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14494153858117032365908681 10870615393587774274431511)
              ·
                refine ⟨16305923090381661411647267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870615393587774274431511 16305923090381661411647267)
                ·
                  refine ⟨24458884635572492117470901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16305923090381661411647267 24458884635572492117470901)
                  ·
                    refine ⟨2293020434584921136012897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24458884635572492117470901 2293020434584921136012897)
                    ·
                      refine ⟨1719765325938690852009673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293020434584921136012897 1719765325938690852009673)
                      ·
                        rfl

theorem cell23_3349231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 2, 2, 1, 1, 5, 2].length) (baseStart_3349231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349231 prefixEnd_3349231 := by exact prefixLift 3349231
  have htrace : WordTrace (prefixWord ++ tailWord_3349231) baseStart_3349231 baseEnd_3349231 := by
    simpa [prefixWord, tailWord_3349231, baseEnd_3349231] using wordTrace_append hprefix tailTrace_3349231
  have hstable : (prefixWord ++ tailWord_3349231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349231).length < 2 ^ (prefixWord ++ tailWord_3349231).sum := by decide
  have hdescent : baseEnd_3349231 < baseStart_3349231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349255 : List Nat := [1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 3]
def baseStart_3349255 : Nat := 118140960795 + 3349255 * 2 ^ 59
def prefixEnd_3349255 : Nat := 4983230072969 + 3 ^ 40 * 3349255 * 2
def baseEnd_3349255 : Nat := 1719777649474398758109563

theorem tailTrace_3349255 : CollatzResearch.WordTrace tailWord_3349255 prefixEnd_3349255 1719777649474398758109563 := by
  unfold tailWord_3349255
  simp only [CollatzResearch.WordTrace]
  refine ⟨122157365481228617059289219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81438243654152411372859479 122157365481228617059289219)
  ·
    refine ⟨183236048221842925588933829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122157365481228617059289219 183236048221842925588933829)
    ·
      refine ⟨34356759041595548547925093, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183236048221842925588933829 34356759041595548547925093)
      ·
        refine ⟨6441892320299165352735955, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34356759041595548547925093 6441892320299165352735955)
        ·
          refine ⟨9662838480448748029103933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6441892320299165352735955 9662838480448748029103933)
          ·
            refine ⟨3623564430168280510913975, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9662838480448748029103933 3623564430168280510913975)
            ·
              refine ⟨5435346645252420766370963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623564430168280510913975 5435346645252420766370963)
              ·
                refine ⟨8153019967878631149556445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435346645252420766370963 8153019967878631149556445)
                ·
                  refine ⟨3057382487954486681083667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8153019967878631149556445 3057382487954486681083667)
                  ·
                    refine ⟨4586073731931730021625501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3057382487954486681083667 4586073731931730021625501)
                    ·
                      refine ⟨1719777649474398758109563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586073731931730021625501 1719777649474398758109563)
                      ·
                        rfl

theorem cell23_3349255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 3, 1, 1, 3, 1, 3].length) (baseStart_3349255 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349255 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349255 prefixEnd_3349255 := by exact prefixLift 3349255
  have htrace : WordTrace (prefixWord ++ tailWord_3349255) baseStart_3349255 baseEnd_3349255 := by
    simpa [prefixWord, tailWord_3349255, baseEnd_3349255] using wordTrace_append hprefix tailTrace_3349255
  have hstable : (prefixWord ++ tailWord_3349255).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349255).length < 2 ^ (prefixWord ++ tailWord_3349255).sum := by decide
  have hdescent : baseEnd_3349255 < baseStart_3349255 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349274 : List Nat := [3, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6]
def baseStart_3349274 : Nat := 118140960795 + 3349274 * 2 ^ 59
def prefixEnd_3349274 : Nat := 4983230072969 + 3 ^ 40 * 3349274 * 2
def baseEnd_3349274 : Nat := 1719787405606834183771975

theorem tailTrace_3349274 : CollatzResearch.WordTrace tailWord_3349274 prefixEnd_3349274 1719787405606834183771975 := by
  unfold tailWord_3349274
  simp only [CollatzResearch.WordTrace]
  refine ⟨30539514617039945826057719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81438705645439855536153917 30539514617039945826057719)
  ·
    refine ⟨45809271925559918739086579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30539514617039945826057719 45809271925559918739086579)
    ·
      refine ⟨68713907888339878108629869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45809271925559918739086579 68713907888339878108629869)
      ·
        refine ⟨25767715458127454290736201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68713907888339878108629869 25767715458127454290736201)
        ·
          refine ⟨19325786593595590718052151, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25767715458127454290736201 19325786593595590718052151)
          ·
            refine ⟨28988679890393386077078227, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19325786593595590718052151 28988679890393386077078227)
            ·
              refine ⟨43483019835590079115617341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28988679890393386077078227 43483019835590079115617341)
              ·
                refine ⟨16306132438346279668356503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43483019835590079115617341 16306132438346279668356503)
                ·
                  refine ⟨24459198657519419502534755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16306132438346279668356503 24459198657519419502534755)
                  ·
                    refine ⟨36688797986279129253802133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24459198657519419502534755 36688797986279129253802133)
                    ·
                      refine ⟨1719787405606834183771975, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36688797986279129253802133 1719787405606834183771975)
                      ·
                        rfl

theorem cell23_3349274_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 1, 3, 1, 1, 6].length) (baseStart_3349274 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349274 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349274 prefixEnd_3349274 := by exact prefixLift 3349274
  have htrace : WordTrace (prefixWord ++ tailWord_3349274) baseStart_3349274 baseEnd_3349274 := by
    simpa [prefixWord, tailWord_3349274, baseEnd_3349274] using wordTrace_append hprefix tailTrace_3349274
  have hstable : (prefixWord ++ tailWord_3349274).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349274).length < 2 ^ (prefixWord ++ tailWord_3349274).sum := by decide
  have hdescent : baseEnd_3349274 < baseStart_3349274 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349274) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349281 : List Nat := [1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 3]
def baseStart_3349281 : Nat := 118140960795 + 3349281 * 2 ^ 59
def prefixEnd_3349281 : Nat := 4983230072969 + 3 ^ 40 * 3349281 * 2
def baseEnd_3349281 : Nat := 1719790999971415656384443

theorem tailTrace_3349281 : CollatzResearch.WordTrace tailWord_3349281 prefixEnd_3349281 1719790999971415656384443 := by
  unfold tailWord_3349281
  simp only [CollatzResearch.WordTrace]
  refine ⟨122158313779134423499735697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81438875852756282333157131 122158313779134423499735697)
  ·
    refine ⟨91618735334350817624801773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122158313779134423499735697 91618735334350817624801773)
    ·
      refine ⟨34357025750381556609300665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91618735334350817624801773 34357025750381556609300665)
      ·
        refine ⟨25767769312786167456975499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34357025750381556609300665 25767769312786167456975499)
        ·
          refine ⟨38651653969179251185463249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25767769312786167456975499 38651653969179251185463249)
          ·
            refine ⟨28988740476884438389097437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38651653969179251185463249 28988740476884438389097437)
            ·
              refine ⟨10870777678831664395911539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28988740476884438389097437 10870777678831664395911539)
              ·
                refine ⟨16306166518247496593867309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870777678831664395911539 16306166518247496593867309)
                ·
                  refine ⟨6114812444342811222700241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16306166518247496593867309 6114812444342811222700241)
                  ·
                    refine ⟨4586109333257108417025181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6114812444342811222700241 4586109333257108417025181)
                    ·
                      refine ⟨1719790999971415656384443, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586109333257108417025181 1719790999971415656384443)
                      ·
                        rfl

theorem cell23_3349281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_3349281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349281 prefixEnd_3349281 := by exact prefixLift 3349281
  have htrace : WordTrace (prefixWord ++ tailWord_3349281) baseStart_3349281 baseEnd_3349281 := by
    simpa [prefixWord, tailWord_3349281, baseEnd_3349281] using wordTrace_append hprefix tailTrace_3349281
  have hstable : (prefixWord ++ tailWord_3349281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349281).length < 2 ^ (prefixWord ++ tailWord_3349281).sum := by decide
  have hdescent : baseEnd_3349281 < baseStart_3349281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349325 : List Nat := [1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 4]
def baseStart_3349325 : Nat := 118140960795 + 3349325 * 2 ^ 59
def prefixEnd_3349325 : Nat := 4983230072969 + 3 ^ 40 * 3349325 * 2
def baseEnd_3349325 : Nat := 1719813593120213484234241

theorem tailTrace_3349325 : CollatzResearch.WordTrace tailWord_3349325 prefixEnd_3349325 1719813593120213484234241 := by
  unfold tailWord_3349325
  simp only [CollatzResearch.WordTrace]
  refine ⟨122159918590975019014337429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81439945727316679342891619 122159918590975019014337429)
  ·
    refine ⟨5726246183951954016297067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122159918590975019014337429 5726246183951954016297067)
    ·
      refine ⟨8589369275927931024445601, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5726246183951954016297067 8589369275927931024445601)
      ·
        refine ⟨6442026956945948268334201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8589369275927931024445601 6442026956945948268334201)
        ·
          refine ⟨4831520217709461201250651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442026956945948268334201 4831520217709461201250651)
          ·
            refine ⟨7247280326564191801875977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831520217709461201250651 7247280326564191801875977)
            ·
              refine ⟨5435460244923143851406983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7247280326564191801875977 5435460244923143851406983)
              ·
                refine ⟨8153190367384715777110475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435460244923143851406983 8153190367384715777110475)
                ·
                  refine ⟨12229785551077073665665713, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153190367384715777110475 12229785551077073665665713)
                  ·
                    refine ⟨9172339163307805249249285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12229785551077073665665713 9172339163307805249249285)
                    ·
                      refine ⟨1719813593120213484234241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9172339163307805249249285 1719813593120213484234241)
                      ·
                        rfl

theorem cell23_3349325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 2, 1, 2, 1, 1, 2, 4].length) (baseStart_3349325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349325 prefixEnd_3349325 := by exact prefixLift 3349325
  have htrace : WordTrace (prefixWord ++ tailWord_3349325) baseStart_3349325 baseEnd_3349325 := by
    simpa [prefixWord, tailWord_3349325, baseEnd_3349325] using wordTrace_append hprefix tailTrace_3349325
  have hstable : (prefixWord ++ tailWord_3349325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349325).length < 2 ^ (prefixWord ++ tailWord_3349325).sum := by decide
  have hdescent : baseEnd_3349325 < baseStart_3349325 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349328 : List Nat := [2, 1, 1, 1, 1, 4, 4, 3, 2, 1, 3]
def baseStart_3349328 : Nat := 118140960795 + 3349328 * 2 ^ 59
def prefixEnd_3349328 : Nat := 4983230072969 + 3 ^ 40 * 3349328 * 2
def baseEnd_3349328 : Nat := 1719815133562176972496727

theorem tailTrace_3349328 : CollatzResearch.WordTrace tailWord_3349328 prefixEnd_3349328 1719815133562176972496727 := by
  unfold tailWord_3349328
  simp only [CollatzResearch.WordTrace]
  refine ⟨61080014004982075263348319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81440018673309433684464425 61080014004982075263348319)
  ·
    refine ⟨91620021007473112895022479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61080014004982075263348319 91620021007473112895022479)
    ·
      refine ⟨137430031511209669342533719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91620021007473112895022479 137430031511209669342533719)
      ·
        refine ⟨206145047266814504013800579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137430031511209669342533719 206145047266814504013800579)
        ·
          refine ⟨309217570900221756020700869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206145047266814504013800579 309217570900221756020700869)
          ·
            refine ⟨57978294543791579253881413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 309217570900221756020700869 57978294543791579253881413)
            ·
              refine ⟨10870930226960921110102765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57978294543791579253881413 10870930226960921110102765)
              ·
                refine ⟨4076598835110345416288537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10870930226960921110102765 4076598835110345416288537)
                ·
                  refine ⟨3057449126332759062216403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4076598835110345416288537 3057449126332759062216403)
                  ·
                    refine ⟨4586173689499138593324605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3057449126332759062216403 4586173689499138593324605)
                    ·
                      refine ⟨1719815133562176972496727, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586173689499138593324605 1719815133562176972496727)
                      ·
                        rfl

theorem cell23_3349328_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 4, 3, 2, 1, 3].length) (baseStart_3349328 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349328 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349328 prefixEnd_3349328 := by exact prefixLift 3349328
  have htrace : WordTrace (prefixWord ++ tailWord_3349328) baseStart_3349328 baseEnd_3349328 := by
    simpa [prefixWord, tailWord_3349328, baseEnd_3349328] using wordTrace_append hprefix tailTrace_3349328
  have hstable : (prefixWord ++ tailWord_3349328).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349328).length < 2 ^ (prefixWord ++ tailWord_3349328).sum := by decide
  have hdescent : baseEnd_3349328 < baseStart_3349328 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349328) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349338 : List Nat := [3, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2]
def baseStart_3349338 : Nat := 118140960795 + 3349338 * 2 ^ 59
def prefixEnd_3349338 : Nat := 4983230072969 + 3 ^ 40 * 3349338 * 2
def baseEnd_3349338 : Nat := 1719820268368721933371681

theorem tailTrace_3349338 : CollatzResearch.WordTrace tailWord_3349338 prefixEnd_3349338 1719820268368721933371681 := by
  unfold tailWord_3349338
  simp only [CollatzResearch.WordTrace]
  refine ⟨30540098184981980558640167, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81440261826618614823040445 30540098184981980558640167)
  ·
    refine ⟨45810147277472970837960251, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30540098184981980558640167 45810147277472970837960251)
    ·
      refine ⟨68715220916209456256940377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45810147277472970837960251 68715220916209456256940377)
      ·
        refine ⟨51536415687157092192705283, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68715220916209456256940377 51536415687157092192705283)
        ·
          refine ⟨77304623530735638289057925, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51536415687157092192705283 77304623530735638289057925)
          ·
            refine ⟨14494616912012932179198361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77304623530735638289057925 14494616912012932179198361)
            ·
              refine ⟨10870962684009699134398771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14494616912012932179198361 10870962684009699134398771)
              ·
                refine ⟨16306444026014548701598157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10870962684009699134398771 16306444026014548701598157)
                ·
                  refine ⟨6114916509755455763099309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16306444026014548701598157 6114916509755455763099309)
                  ·
                    refine ⟨2293093691158295911162241, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6114916509755455763099309 2293093691158295911162241)
                    ·
                      refine ⟨1719820268368721933371681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293093691158295911162241 1719820268368721933371681)
                      ·
                        rfl

theorem cell23_3349338_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 4, 2, 1, 3, 3, 2].length) (baseStart_3349338 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349338 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349338 prefixEnd_3349338 := by exact prefixLift 3349338
  have htrace : WordTrace (prefixWord ++ tailWord_3349338) baseStart_3349338 baseEnd_3349338 := by
    simpa [prefixWord, tailWord_3349338, baseEnd_3349338] using wordTrace_append hprefix tailTrace_3349338
  have hstable : (prefixWord ++ tailWord_3349338).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349338).length < 2 ^ (prefixWord ++ tailWord_3349338).sum := by decide
  have hdescent : baseEnd_3349338 < baseStart_3349338 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349338) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349344 : List Nat := [2, 1, 1, 3, 3, 1, 1, 2, 1, 8]
def baseStart_3349344 : Nat := 118140960795 + 3349344 * 2 ^ 59
def prefixEnd_3349344 : Nat := 4983230072969 + 3 ^ 40 * 3349344 * 2
def baseEnd_3349344 : Nat := 573274449750882969965551

theorem tailTrace_3349344 : CollatzResearch.WordTrace tailWord_3349344 prefixEnd_3349344 573274449750882969965551 := by
  unfold tailWord_3349344
  simp only [CollatzResearch.WordTrace]
  refine ⟨61080305788953092629639543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81440407718604123506186057 61080305788953092629639543)
  ·
    refine ⟨91620458683429638944459315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61080305788953092629639543 91620458683429638944459315)
    ·
      refine ⟨137430688025144458416688973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91620458683429638944459315 137430688025144458416688973)
      ·
        refine ⟨51536508009429171906258365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137430688025144458416688973 51536508009429171906258365)
        ·
          refine ⟨19326190503535939464846887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51536508009429171906258365 19326190503535939464846887)
          ·
            refine ⟨28989285755303909197270331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19326190503535939464846887 28989285755303909197270331)
            ·
              refine ⟨43483928632955863795905497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28989285755303909197270331 43483928632955863795905497)
              ·
                refine ⟨32612946474716897846929123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43483928632955863795905497 32612946474716897846929123)
                ·
                  refine ⟨48919419712075346770393685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32612946474716897846929123 48919419712075346770393685)
                  ·
                    refine ⟨573274449750882969965551, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 48919419712075346770393685 573274449750882969965551)
                    ·
                      rfl

theorem cell23_3349344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 1, 1, 2, 1, 8].length) (baseStart_3349344 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349344 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349344 prefixEnd_3349344 := by exact prefixLift 3349344
  have htrace : WordTrace (prefixWord ++ tailWord_3349344) baseStart_3349344 baseEnd_3349344 := by
    simpa [prefixWord, tailWord_3349344, baseEnd_3349344] using wordTrace_append hprefix tailTrace_3349344
  have hstable : (prefixWord ++ tailWord_3349344).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349344).length < 2 ^ (prefixWord ++ tailWord_3349344).sum := by decide
  have hdescent : baseEnd_3349344 < baseStart_3349344 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349355 : List Nat := [1, 1, 1, 1, 2, 2, 8, 1, 1, 3, 2]
def baseStart_3349355 : Nat := 118140960795 + 3349355 * 2 ^ 59
def prefixEnd_3349355 : Nat := 4983230072969 + 3 ^ 40 * 3349355 * 2
def baseEnd_3349355 : Nat := 1719828997539848366859103

theorem tailTrace_3349355 : CollatzResearch.WordTrace tailWord_3349355 prefixEnd_3349355 1719828997539848366859103 := by
  unfold tailWord_3349355
  simp only [CollatzResearch.WordTrace]
  refine ⟨122161012780866334137929519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81440675187244222758619679 122161012780866334137929519)
  ·
    refine ⟨183241519171299501206894279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122161012780866334137929519 183241519171299501206894279)
    ·
      refine ⟨274862278756949251810341419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183241519171299501206894279 274862278756949251810341419)
      ·
        refine ⟨412293418135423877715512129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274862278756949251810341419 412293418135423877715512129)
        ·
          refine ⟨309220063601567908286634097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 412293418135423877715512129 309220063601567908286634097)
          ·
            refine ⟨231915047701175931214975573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309220063601567908286634097 231915047701175931214975573)
            ·
              refine ⟨2717754465248155443925495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 231915047701175931214975573 2717754465248155443925495)
              ·
                refine ⟨4076631697872233165888243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717754465248155443925495 4076631697872233165888243)
                ·
                  refine ⟨6114947546808349748832365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076631697872233165888243 6114947546808349748832365)
                  ·
                    refine ⟨2293105330053131155812137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6114947546808349748832365 2293105330053131155812137)
                    ·
                      refine ⟨1719828997539848366859103, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293105330053131155812137 1719828997539848366859103)
                      ·
                        rfl

theorem cell23_3349355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 8, 1, 1, 3, 2].length) (baseStart_3349355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349355 prefixEnd_3349355 := by exact prefixLift 3349355
  have htrace : WordTrace (prefixWord ++ tailWord_3349355) baseStart_3349355 baseEnd_3349355 := by
    simpa [prefixWord, tailWord_3349355, baseEnd_3349355] using wordTrace_append hprefix tailTrace_3349355
  have hstable : (prefixWord ++ tailWord_3349355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349355).length < 2 ^ (prefixWord ++ tailWord_3349355).sum := by decide
  have hdescent : baseEnd_3349355 < baseStart_3349355 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349381 : List Nat := [1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 4]
def baseStart_3349381 : Nat := 118140960795 + 3349381 * 2 ^ 59
def prefixEnd_3349381 : Nat := 4983230072969 + 3 ^ 40 * 3349381 * 2
def baseEnd_3349381 : Nat := 1719842348036865265133983

theorem tailTrace_3349381 : CollatzResearch.WordTrace tailWord_3349381 prefixEnd_3349381 1719842348036865265133983 := by
  unfold tailWord_3349381
  simp only [CollatzResearch.WordTrace]
  refine ⟨122161961078772140578375997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81441307385848093718917331 122161961078772140578375997)
  ·
    refine ⟨45810735404539552716890999, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122161961078772140578375997 45810735404539552716890999)
    ·
      refine ⟨68716103106809329075336499, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45810735404539552716890999 68716103106809329075336499)
      ·
        refine ⟨103074154660213993613004749, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68716103106809329075336499 103074154660213993613004749)
        ·
          refine ⟨38652807997580247604876781, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103074154660213993613004749 38652807997580247604876781)
          ·
            refine ⟨14494802999092592851828793, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38652807997580247604876781 14494802999092592851828793)
            ·
              refine ⟨10871102249319444638871595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14494802999092592851828793 10871102249319444638871595)
              ·
                refine ⟨16306653373979166958307393, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10871102249319444638871595 16306653373979166958307393)
                ·
                  refine ⟨12229990030484375218730545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16306653373979166958307393 12229990030484375218730545)
                  ·
                    refine ⟨9172492522863281414047909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12229990030484375218730545 9172492522863281414047909)
                    ·
                      refine ⟨1719842348036865265133983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9172492522863281414047909 1719842348036865265133983)
                      ·
                        rfl

theorem cell23_3349381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 2, 1, 2, 2, 4].length) (baseStart_3349381 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349381 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349381 prefixEnd_3349381 := by exact prefixLift 3349381
  have htrace : WordTrace (prefixWord ++ tailWord_3349381) baseStart_3349381 baseEnd_3349381 := by
    simpa [prefixWord, tailWord_3349381, baseEnd_3349381] using wordTrace_append hprefix tailTrace_3349381
  have hstable : (prefixWord ++ tailWord_3349381).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349381).length < 2 ^ (prefixWord ++ tailWord_3349381).sum := by decide
  have hdescent : baseEnd_3349381 < baseStart_3349381 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349385 : List Nat := [1, 2, 1, 1, 5, 4, 1, 1, 1, 4, 2]
def baseStart_3349385 : Nat := 118140960795 + 3349385 * 2 ^ 59
def prefixEnd_3349385 : Nat := 4983230072969 + 3 ^ 40 * 3349385 * 2
def baseEnd_3349385 : Nat := 1719844401959483249483965

theorem tailTrace_3349385 : CollatzResearch.WordTrace tailWord_3349385 prefixEnd_3349385 1719844401959483249483965 := by
  unfold tailWord_3349385
  simp only [CollatzResearch.WordTrace]
  refine ⟨122162106970757649261521609, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81441404647171766174347739 122162106970757649261521609)
  ·
    refine ⟨91621580228068236946141207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122162106970757649261521609 91621580228068236946141207)
    ·
      refine ⟨137432370342102355419211811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91621580228068236946141207 137432370342102355419211811)
      ·
        refine ⟨206148555513153533128817717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137432370342102355419211811 206148555513153533128817717)
        ·
          refine ⟨19326427079358143730826661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206148555513153533128817717 19326427079358143730826661)
          ·
            refine ⟨3623705077379651949529999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19326427079358143730826661 3623705077379651949529999)
            ·
              refine ⟨5435557616069477924294999, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623705077379651949529999 5435557616069477924294999)
              ·
                refine ⟨8153336424104216886442499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435557616069477924294999 8153336424104216886442499)
                ·
                  refine ⟨12230004636156325329663749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153336424104216886442499 12230004636156325329663749)
                  ·
                    refine ⟨2293125869279310999311953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12230004636156325329663749 2293125869279310999311953)
                    ·
                      refine ⟨1719844401959483249483965, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293125869279310999311953 1719844401959483249483965)
                      ·
                        rfl

theorem cell23_3349385_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 4, 1, 1, 1, 4, 2].length) (baseStart_3349385 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349385 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349385 prefixEnd_3349385 := by exact prefixLift 3349385
  have htrace : WordTrace (prefixWord ++ tailWord_3349385) baseStart_3349385 baseEnd_3349385 := by
    simpa [prefixWord, tailWord_3349385, baseEnd_3349385] using wordTrace_append hprefix tailTrace_3349385
  have hstable : (prefixWord ++ tailWord_3349385).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349385).length < 2 ^ (prefixWord ++ tailWord_3349385).sum := by decide
  have hdescent : baseEnd_3349385 < baseStart_3349385 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349385) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349408 : List Nat := [2, 1, 1, 4, 1, 1, 5, 3, 5]
def baseStart_3349408 : Nat := 118140960795 + 3349408 * 2 ^ 59
def prefixEnd_3349408 : Nat := 4983230072969 + 3 ^ 40 * 3349408 * 2
def baseEnd_3349408 : Nat := 191095134668281851055151

theorem tailTrace_3349408 : CollatzResearch.WordTrace tailWord_3349408 prefixEnd_3349408 191095134668281851055151 := by
  unfold tailWord_3349408
  simp only [CollatzResearch.WordTrace]
  refine ⟨61081472924837162094804439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81441963899782882793072585 61081472924837162094804439)
  ·
    refine ⟨91622209387255743142206659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61081472924837162094804439 91622209387255743142206659)
    ·
      refine ⟨137433314080883614713309989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91622209387255743142206659 137433314080883614713309989)
      ·
        refine ⟨25768746390165677758745623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137433314080883614713309989 25768746390165677758745623)
        ·
          refine ⟨38653119585248516638118435, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25768746390165677758745623 38653119585248516638118435)
          ·
            refine ⟨57979679377872774957177653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38653119585248516638118435 57979679377872774957177653)
            ·
              refine ⟨5435594941675572652235405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57979679377872774957177653 5435594941675572652235405)
              ·
                refine ⟨2038348103128339744588277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5435594941675572652235405 2038348103128339744588277)
                ·
                  refine ⟨191095134668281851055151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038348103128339744588277 191095134668281851055151)
                  ·
                    rfl

theorem cell23_3349408_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 5, 3, 5].length) (baseStart_3349408 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349408 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349408 prefixEnd_3349408 := by exact prefixLift 3349408
  have htrace : WordTrace (prefixWord ++ tailWord_3349408) baseStart_3349408 baseEnd_3349408 := by
    simpa [prefixWord, tailWord_3349408, baseEnd_3349408] using wordTrace_append hprefix tailTrace_3349408
  have hstable : (prefixWord ++ tailWord_3349408).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349408).length < 2 ^ (prefixWord ++ tailWord_3349408).sum := by decide
  have hdescent : baseEnd_3349408 < baseStart_3349408 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349408) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349424 : List Nat := [2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8]
def baseStart_3349424 : Nat := 118140960795 + 3349424 * 2 ^ 59
def prefixEnd_3349424 : Nat := 4983230072969 + 3 ^ 40 * 3349424 * 2
def baseEnd_3349424 : Nat := 1719864427705008596896285

theorem tailTrace_3349424 : CollatzResearch.WordTrace tailWord_3349424 prefixEnd_3349424 1719864427705008596896285 := by
  unfold tailWord_3349424
  simp only [CollatzResearch.WordTrace]
  refine ⟨61081764708808179461095663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81442352945077572614794217 61081764708808179461095663)
  ·
    refine ⟨91622647063212269191643495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61081764708808179461095663 91622647063212269191643495)
    ·
      refine ⟨137433970594818403787465243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91622647063212269191643495 137433970594818403787465243)
      ·
        refine ⟨206150955892227605681197865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137433970594818403787465243 206150955892227605681197865)
        ·
          refine ⟨154613216919170704260898399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206150955892227605681197865 154613216919170704260898399)
          ·
            refine ⟨231919825378756056391347599, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154613216919170704260898399 231919825378756056391347599)
            ·
              refine ⟨347879738068134084587021399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 231919825378756056391347599 347879738068134084587021399)
              ·
                refine ⟨521819607102201126880532099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 347879738068134084587021399 521819607102201126880532099)
                ·
                  refine ⟨782729410653301690320798149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 521819607102201126880532099 782729410653301690320798149)
                  ·
                    refine ⟨146761764497494066935149653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 782729410653301690320798149 146761764497494066935149653)
                    ·
                      refine ⟨1719864427705008596896285, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 146761764497494066935149653 1719864427705008596896285)
                      ·
                        rfl

theorem cell23_3349424_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 8].length) (baseStart_3349424 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349424 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349424 prefixEnd_3349424 := by exact prefixLift 3349424
  have htrace : WordTrace (prefixWord ++ tailWord_3349424) baseStart_3349424 baseEnd_3349424 := by
    simpa [prefixWord, tailWord_3349424, baseEnd_3349424] using wordTrace_append hprefix tailTrace_3349424
  have hstable : (prefixWord ++ tailWord_3349424).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349424).length < 2 ^ (prefixWord ++ tailWord_3349424).sum := by decide
  have hdescent : baseEnd_3349424 < baseStart_3349424 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349424) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349425 : List Nat := [1, 2, 2, 4, 4, 1, 1, 1, 7]
def baseStart_3349425 : Nat := 118140960795 + 3349425 * 2 ^ 59
def prefixEnd_3349425 : Nat := 4983230072969 + 3 ^ 40 * 3349425 * 2
def baseEnd_3349425 : Nat := 191096104576184788109309

theorem tailTrace_3349425 : CollatzResearch.WordTrace tailWord_3349425 prefixEnd_3349425 191096104576184788109309 := by
  unfold tailWord_3349425
  simp only [CollatzResearch.WordTrace]
  refine ⟨122163565890612736092977729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81442377260408490728651819 122163565890612736092977729)
  ·
    refine ⟨91622674417959552069733297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122163565890612736092977729 91622674417959552069733297)
    ·
      refine ⟨68717005813469664052299973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91622674417959552069733297 68717005813469664052299973)
      ·
        refine ⟨12884438590025562009806245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68717005813469664052299973 12884438590025562009806245)
        ·
          refine ⟨2415832235629792876838671, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12884438590025562009806245 2415832235629792876838671)
          ·
            refine ⟨3623748353444689315258007, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415832235629792876838671 3623748353444689315258007)
            ·
              refine ⟨5435622530167033972887011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623748353444689315258007 5435622530167033972887011)
              ·
                refine ⟨8153433795250550959330517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5435622530167033972887011 8153433795250550959330517)
                ·
                  refine ⟨191096104576184788109309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8153433795250550959330517 191096104576184788109309)
                  ·
                    rfl

theorem cell23_3349425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 4, 1, 1, 1, 7].length) (baseStart_3349425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349425 prefixEnd_3349425 := by exact prefixLift 3349425
  have htrace : WordTrace (prefixWord ++ tailWord_3349425) baseStart_3349425 baseEnd_3349425 := by
    simpa [prefixWord, tailWord_3349425, baseEnd_3349425] using wordTrace_append hprefix tailTrace_3349425
  have hstable : (prefixWord ++ tailWord_3349425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349425).length < 2 ^ (prefixWord ++ tailWord_3349425).sum := by decide
  have hdescent : baseEnd_3349425 < baseStart_3349425 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349430 : List Nat := [5, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3]
def baseStart_3349430 : Nat := 118140960795 + 3349430 * 2 ^ 59
def prefixEnd_3349430 : Nat := 4983230072969 + 3 ^ 40 * 3349430 * 2
def baseEnd_3349430 : Nat := 1719867508588935573421259

theorem tailTrace_3349430 : CollatzResearch.WordTrace tailWord_3349430 prefixEnd_3349430 1719867508588935573421259 := by
  unfold tailWord_3349430
  simp only [CollatzResearch.WordTrace]
  refine ⟨7635234265974663871681859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81442498837063081297939829 7635234265974663871681859)
  ·
    refine ⟨11452851398961995807522789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7635234265974663871681859 11452851398961995807522789)
    ·
      refine ⟨2147409637305374213910523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 11452851398961995807522789 2147409637305374213910523)
      ·
        refine ⟨3221114455958061320865785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147409637305374213910523 3221114455958061320865785)
        ·
          refine ⟨2415835841968545990649339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221114455958061320865785 2415835841968545990649339)
          ·
            refine ⟨3623753762952818985974009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415835841968545990649339 3623753762952818985974009)
            ·
              refine ⟨2717815322214614239480507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3623753762952818985974009 2717815322214614239480507)
              ·
                refine ⟨4076722983321921359220761, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2717815322214614239480507 4076722983321921359220761)
                ·
                  refine ⟨3057542237491441019415571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4076722983321921359220761 3057542237491441019415571)
                  ·
                    refine ⟨4586313356237161529123357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3057542237491441019415571 4586313356237161529123357)
                    ·
                      refine ⟨1719867508588935573421259, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586313356237161529123357 1719867508588935573421259)
                      ·
                        rfl

theorem cell23_3349430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 2, 1, 2, 1, 2, 1, 3].length) (baseStart_3349430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349430 prefixEnd_3349430 := by exact prefixLift 3349430
  have htrace : WordTrace (prefixWord ++ tailWord_3349430) baseStart_3349430 baseEnd_3349430 := by
    simpa [prefixWord, tailWord_3349430, baseEnd_3349430] using wordTrace_append hprefix tailTrace_3349430
  have hstable : (prefixWord ++ tailWord_3349430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349430).length < 2 ^ (prefixWord ++ tailWord_3349430).sum := by decide
  have hdescent : baseEnd_3349430 < baseStart_3349430 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349491 : List Nat := [1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 3]
def baseStart_3349491 : Nat := 118140960795 + 3349491 * 2 ^ 59
def prefixEnd_3349491 : Nat := 4983230072969 + 3 ^ 40 * 3349491 * 2
def baseEnd_3349491 : Nat := 1719898830908859834758477

theorem tailTrace_3349491 : CollatzResearch.WordTrace tailWord_3349491 prefixEnd_3349491 1719898830908859834758477 := by
  unfold tailWord_3349491
  simp only [CollatzResearch.WordTrace]
  refine ⟨122165973108373629364880327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81443982072249086243253551 122165973108373629364880327)
  ·
    refine ⟨183248959662560444047320491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122165973108373629364880327 183248959662560444047320491)
    ·
      refine ⟨274873439493840666070980737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183248959662560444047320491 274873439493840666070980737)
      ·
        refine ⟨206155079620380499553235553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274873439493840666070980737 206155079620380499553235553)
        ·
          refine ⟨154616309715285374664926665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206155079620380499553235553 154616309715285374664926665)
          ·
            refine ⟨115962232286464030998694999, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154616309715285374664926665 115962232286464030998694999)
            ·
              refine ⟨173943348429696046498042499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115962232286464030998694999 173943348429696046498042499)
              ·
                refine ⟨260915022644544069747063749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 173943348429696046498042499 260915022644544069747063749)
                ·
                  refine ⟨48921566745852013077574453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 260915022644544069747063749 48921566745852013077574453)
                  ·
                    refine ⟨4586396882423626226022605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48921566745852013077574453 4586396882423626226022605)
                    ·
                      refine ⟨1719898830908859834758477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586396882423626226022605 1719898830908859834758477)
                      ·
                        rfl

theorem cell23_3349491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 1, 1, 4, 5, 3].length) (baseStart_3349491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349491 prefixEnd_3349491 := by exact prefixLift 3349491
  have htrace : WordTrace (prefixWord ++ tailWord_3349491) baseStart_3349491 baseEnd_3349491 := by
    simpa [prefixWord, tailWord_3349491, baseEnd_3349491] using wordTrace_append hprefix tailTrace_3349491
  have hstable : (prefixWord ++ tailWord_3349491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349491).length < 2 ^ (prefixWord ++ tailWord_3349491).sum := by decide
  have hdescent : baseEnd_3349491 < baseStart_3349491 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349502 : List Nat := [4, 2, 2, 2, 2, 1, 1, 2, 3, 4]
def baseStart_3349502 : Nat := 118140960795 + 3349502 * 2 ^ 59
def prefixEnd_3349502 : Nat := 4983230072969 + 3 ^ 40 * 3349502 * 2
def baseEnd_3349502 : Nat := 573301493065353097240309

theorem tailTrace_3349502 : CollatzResearch.WordTrace tailWord_3349502 prefixEnd_3349502 573301493065353097240309 := by
  unfold tailWord_3349502
  simp only [CollatzResearch.WordTrace]
  refine ⟨15270796788916722280441345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81444249540889185495687173 15270796788916722280441345)
  ·
    refine ⟨11453097591687541710331009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15270796788916722280441345 11453097591687541710331009)
    ·
      refine ⟨8589823193765656282748257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11453097591687541710331009 8589823193765656282748257)
      ·
        refine ⟨6442367395324242212061193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8589823193765656282748257 6442367395324242212061193)
        ·
          refine ⟨4831775546493181659045895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6442367395324242212061193 4831775546493181659045895)
          ·
            refine ⟨7247663319739772488568843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4831775546493181659045895 7247663319739772488568843)
            ·
              refine ⟨10871494979609658732853265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7247663319739772488568843 10871494979609658732853265)
              ·
                refine ⟨8153621234707244049639949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10871494979609658732853265 8153621234707244049639949)
                ·
                  refine ⟨3057607963015216518614981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8153621234707244049639949 3057607963015216518614981)
                  ·
                    refine ⟨573301493065353097240309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3057607963015216518614981 573301493065353097240309)
                    ·
                      rfl

theorem cell23_3349502_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 2, 2, 1, 1, 2, 3, 4].length) (baseStart_3349502 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349502 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349502 prefixEnd_3349502 := by exact prefixLift 3349502
  have htrace : WordTrace (prefixWord ++ tailWord_3349502) baseStart_3349502 baseEnd_3349502 := by
    simpa [prefixWord, tailWord_3349502, baseEnd_3349502] using wordTrace_append hprefix tailTrace_3349502
  have hstable : (prefixWord ++ tailWord_3349502).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349502).length < 2 ^ (prefixWord ++ tailWord_3349502).sum := by decide
  have hdescent : baseEnd_3349502 < baseStart_3349502 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349502) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349532 : List Nat := [2, 2, 3, 1, 5, 1, 1, 2, 6]
def baseStart_3349532 : Nat := 118140960795 + 3349532 * 2 ^ 59
def prefixEnd_3349532 : Nat := 4983230072969 + 3 ^ 40 * 3349532 * 2
def baseEnd_3349532 : Nat := 191102209290632686038421

theorem tailTrace_3349532 : CollatzResearch.WordTrace tailWord_3349532 prefixEnd_3349532 191102209290632686038421 := by
  unfold tailWord_3349532
  simp only [CollatzResearch.WordTrace]
  refine ⟨61083734250612546683561425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81444979000816728911415233 61083734250612546683561425)
  ·
    refine ⟨45812800687959410012671069, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61083734250612546683561425 45812800687959410012671069)
    ·
      refine ⟨17179800257984778754751651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45812800687959410012671069 17179800257984778754751651)
      ·
        refine ⟨25769700386977168132127477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17179800257984778754751651 25769700386977168132127477)
        ·
          refine ⟨2415909411279109512386951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25769700386977168132127477 2415909411279109512386951)
          ·
            refine ⟨3623864116918664268580427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2415909411279109512386951 3623864116918664268580427)
            ·
              refine ⟨5435796175377996402870641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3623864116918664268580427 5435796175377996402870641)
              ·
                refine ⟨4076847131533497302152981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5435796175377996402870641 4076847131533497302152981)
                ·
                  refine ⟨191102209290632686038421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4076847131533497302152981 191102209290632686038421)
                  ·
                    rfl

theorem cell23_3349532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 5, 1, 1, 2, 6].length) (baseStart_3349532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349532 prefixEnd_3349532 := by exact prefixLift 3349532
  have htrace : WordTrace (prefixWord ++ tailWord_3349532) baseStart_3349532 baseEnd_3349532 := by
    simpa [prefixWord, tailWord_3349532, baseEnd_3349532] using wordTrace_append hprefix tailTrace_3349532
  have hstable : (prefixWord ++ tailWord_3349532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349532).length < 2 ^ (prefixWord ++ tailWord_3349532).sum := by decide
  have hdescent : baseEnd_3349532 < baseStart_3349532 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349565 : List Nat := [1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 4]
def baseStart_3349565 : Nat := 118140960795 + 3349565 * 2 ^ 59
def prefixEnd_3349565 : Nat := 4983230072969 + 3 ^ 40 * 3349565 * 2
def baseEnd_3349565 : Nat := 1719936828477292545233137

theorem tailTrace_3349565 : CollatzResearch.WordTrace tailWord_3349565 prefixEnd_3349565 1719936828477292545233137 := by
  unfold tailWord_3349565
  simp only [CollatzResearch.WordTrace]
  refine ⟨122168672110105540003074149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81445781406737026668716099 122168672110105540003074149)
  ·
    refine ⟨22906626020644788750576403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122168672110105540003074149 22906626020644788750576403)
    ·
      refine ⟨34359939030967183125864605, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22906626020644788750576403 34359939030967183125864605)
      ·
        refine ⟨12884977136612693672199227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34359939030967183125864605 12884977136612693672199227)
        ·
          refine ⟨19327465704919040508298841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12884977136612693672199227 19327465704919040508298841)
          ·
            refine ⟨14495599278689280381224131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19327465704919040508298841 14495599278689280381224131)
            ·
              refine ⟨21743398918033920571836197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14495599278689280381224131 21743398918033920571836197)
              ·
                refine ⟨4076887297131360107219287, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21743398918033920571836197 4076887297131360107219287)
                ·
                  refine ⟨6115330945697040160828931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076887297131360107219287 6115330945697040160828931)
                  ·
                    refine ⟨9172996418545560241243397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6115330945697040160828931 9172996418545560241243397)
                    ·
                      refine ⟨1719936828477292545233137, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9172996418545560241243397 1719936828477292545233137)
                      ·
                        rfl

theorem cell23_3349565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 3, 1, 2, 1, 4, 1, 1, 4].length) (baseStart_3349565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349565 prefixEnd_3349565 := by exact prefixLift 3349565
  have htrace : WordTrace (prefixWord ++ tailWord_3349565) baseStart_3349565 baseEnd_3349565 := by
    simpa [prefixWord, tailWord_3349565, baseEnd_3349565] using wordTrace_append hprefix tailTrace_3349565
  have hstable : (prefixWord ++ tailWord_3349565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349565).length < 2 ^ (prefixWord ++ tailWord_3349565).sum := by decide
  have hdescent : baseEnd_3349565 < baseStart_3349565 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349571 : List Nat := [1, 1, 1, 3, 1, 2, 5, 9]
def baseStart_3349571 : Nat := 118140960795 + 3349571 * 2 ^ 59
def prefixEnd_3349571 : Nat := 4983230072969 + 3 ^ 40 * 3349571 * 2
def baseEnd_3349571 : Nat := 63701478124489611916967

theorem tailTrace_3349571 : CollatzResearch.WordTrace tailWord_3349571 prefixEnd_3349571 63701478124489611916967 := by
  unfold tailWord_3349571
  simp only [CollatzResearch.WordTrace]
  refine ⟨122168890948083803027792567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81445927298722535351861711 122168890948083803027792567)
  ·
    refine ⟨183253336422125704541688851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122168890948083803027792567 183253336422125704541688851)
    ·
      refine ⟨274880004633188556812533277, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183253336422125704541688851 274880004633188556812533277)
      ·
        refine ⟨103080001737445708804699979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274880004633188556812533277 103080001737445708804699979)
        ·
          refine ⟨154620002606168563207049969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103080001737445708804699979 154620002606168563207049969)
          ·
            refine ⟨115965001954626422405287477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154620002606168563207049969 115965001954626422405287477)
            ·
              refine ⟨10871718933246227100495701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115965001954626422405287477 10871718933246227100495701)
              ·
                refine ⟨63701478124489611916967, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 10871718933246227100495701 63701478124489611916967)
                ·
                  rfl

theorem cell23_3349571_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 5, 9].length) (baseStart_3349571 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349571 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349571 prefixEnd_3349571 := by exact prefixLift 3349571
  have htrace : WordTrace (prefixWord ++ tailWord_3349571) baseStart_3349571 baseEnd_3349571 := by
    simpa [prefixWord, tailWord_3349571, baseEnd_3349571] using wordTrace_append hprefix tailTrace_3349571
  have hstable : (prefixWord ++ tailWord_3349571).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349571).length < 2 ^ (prefixWord ++ tailWord_3349571).sum := by decide
  have hdescent : baseEnd_3349571 < baseStart_3349571 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349571) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349578 : List Nat := [3, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4]
def baseStart_3349578 : Nat := 118140960795 + 3349578 * 2 ^ 59
def prefixEnd_3349578 : Nat := 4983230072969 + 3 ^ 40 * 3349578 * 2
def baseEnd_3349578 : Nat := 1719943503725800994370577

theorem tailTrace_3349578 : CollatzResearch.WordTrace tailWord_3349578 prefixEnd_3349578 1719943503725800994370577 := by
  unfold tailWord_3349578
  simp only [CollatzResearch.WordTrace]
  refine ⟨30542286564764610805824347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81446097506038962148864925 30542286564764610805824347)
  ·
    refine ⟨45813429847146916208736521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30542286564764610805824347 45813429847146916208736521)
    ·
      refine ⟨34360072385360187156552391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45813429847146916208736521 34360072385360187156552391)
      ·
        refine ⟨51540108578040280734828587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34360072385360187156552391 51540108578040280734828587)
        ·
          refine ⟨77310162867060421102242881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51540108578040280734828587 77310162867060421102242881)
          ·
            refine ⟨57982622150295315826682161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77310162867060421102242881 57982622150295315826682161)
            ·
              refine ⟨43486966612721486870011621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57982622150295315826682161 43486966612721486870011621)
              ·
                refine ⟨8153806239885278788127179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43486966612721486870011621 8153806239885278788127179)
                ·
                  refine ⟨12230709359827918182190769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8153806239885278788127179 12230709359827918182190769)
                  ·
                    refine ⟨9173032019870938636643077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12230709359827918182190769 9173032019870938636643077)
                    ·
                      refine ⟨1719943503725800994370577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9173032019870938636643077 1719943503725800994370577)
                      ·
                        rfl

theorem cell23_3349578_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 2, 2, 4, 1, 2, 4].length) (baseStart_3349578 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349578 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349578 prefixEnd_3349578 := by exact prefixLift 3349578
  have htrace : WordTrace (prefixWord ++ tailWord_3349578) baseStart_3349578 baseEnd_3349578 := by
    simpa [prefixWord, tailWord_3349578, baseEnd_3349578] using wordTrace_append hprefix tailTrace_3349578
  have hstable : (prefixWord ++ tailWord_3349578).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349578).length < 2 ^ (prefixWord ++ tailWord_3349578).sum := by decide
  have hdescent : baseEnd_3349578 < baseStart_3349578 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349578) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349585 : List Nat := [1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 3]
def baseStart_3349585 : Nat := 118140960795 + 3349585 * 2 ^ 59
def prefixEnd_3349585 : Nat := 4983230072969 + 3 ^ 40 * 3349585 * 2
def baseEnd_3349585 : Nat := 1719947098090382466983045

theorem tailTrace_3349585 : CollatzResearch.WordTrace tailWord_3349585 prefixEnd_3349585 1719947098090382466983045 := by
  unfold tailWord_3349585
  simp only [CollatzResearch.WordTrace]
  refine ⟨122169401570033083418802209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81446267713355388945868139 122169401570033083418802209)
  ·
    refine ⟨91627051177524812564101657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122169401570033083418802209 91627051177524812564101657)
    ·
      refine ⟨68720288383143609423076243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91627051177524812564101657 68720288383143609423076243)
      ·
        refine ⟨103080432574715414134614365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68720288383143609423076243 103080432574715414134614365)
        ·
          refine ⟨38655162215518280300480387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103080432574715414134614365 38655162215518280300480387)
          ·
            refine ⟨57982743323277420450720581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38655162215518280300480387 57982743323277420450720581)
            ·
              refine ⟨10871764373114516334510109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 57982743323277420450720581 10871764373114516334510109)
              ·
                refine ⟨4076911639917943625441291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10871764373114516334510109 4076911639917943625441291)
                ·
                  refine ⟨6115367459876915438161937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4076911639917943625441291 6115367459876915438161937)
                  ·
                    refine ⟨4586525594907686578621453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6115367459876915438161937 4586525594907686578621453)
                    ·
                      refine ⟨1719947098090382466983045, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586525594907686578621453 1719947098090382466983045)
                      ·
                        rfl

theorem cell23_3349585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 1, 4, 3, 1, 2, 3].length) (baseStart_3349585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349585 prefixEnd_3349585 := by exact prefixLift 3349585
  have htrace : WordTrace (prefixWord ++ tailWord_3349585) baseStart_3349585 baseEnd_3349585 := by
    simpa [prefixWord, tailWord_3349585, baseEnd_3349585] using wordTrace_append hprefix tailTrace_3349585
  have hstable : (prefixWord ++ tailWord_3349585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349585).length < 2 ^ (prefixWord ++ tailWord_3349585).sum := by decide
  have hdescent : baseEnd_3349585 < baseStart_3349585 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349695 : List Nat := [1, 1, 2, 2, 2, 2, 3, 5, 5]
def baseStart_3349695 : Nat := 118140960795 + 3349695 * 2 ^ 59
def prefixEnd_3349695 : Nat := 4983230072969 + 3 ^ 40 * 3349695 * 2
def baseEnd_3349695 : Nat := 191111508995819670734171

theorem tailTrace_3349695 : CollatzResearch.WordTrace tailWord_3349695 prefixEnd_3349695 191111508995819670734171 := by
  unfold tailWord_3349695
  simp only [CollatzResearch.WordTrace]
  refine ⟨122173413599634572205306539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81448942399756381470204359 122173413599634572205306539)
  ·
    refine ⟨183260120399451858307959809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122173413599634572205306539 183260120399451858307959809)
    ·
      refine ⟨137445090299588893730969857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183260120399451858307959809 137445090299588893730969857)
      ·
        refine ⟨103083817724691670298227393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137445090299588893730969857 103083817724691670298227393)
        ·
          refine ⟨77312863293518752723670545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103083817724691670298227393 77312863293518752723670545)
          ·
            refine ⟨57984647470139064542752909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77312863293518752723670545 57984647470139064542752909)
            ·
              refine ⟨21744242801302149203532341, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57984647470139064542752909 21744242801302149203532341)
              ·
                refine ⟨2038522762622076487831157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21744242801302149203532341 2038522762622076487831157)
                ·
                  refine ⟨191111508995819670734171, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038522762622076487831157 191111508995819670734171)
                  ·
                    rfl

theorem cell23_3349695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 3, 5, 5].length) (baseStart_3349695 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349695 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349695 prefixEnd_3349695 := by exact prefixLift 3349695
  have htrace : WordTrace (prefixWord ++ tailWord_3349695) baseStart_3349695 baseEnd_3349695 := by
    simpa [prefixWord, tailWord_3349695, baseEnd_3349695] using wordTrace_append hprefix tailTrace_3349695
  have hstable : (prefixWord ++ tailWord_3349695).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349695).length < 2 ^ (prefixWord ++ tailWord_3349695).sum := by decide
  have hdescent : baseEnd_3349695 < baseStart_3349695 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349706 : List Nat := [3, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2]
def baseStart_3349706 : Nat := 118140960795 + 3349706 * 2 ^ 59
def prefixEnd_3349706 : Nat := 4983230072969 + 3 ^ 40 * 3349706 * 2
def baseEnd_3349706 : Nat := 1720009229249576493569989

theorem tailTrace_3349706 : CollatzResearch.WordTrace tailWord_3349706 prefixEnd_3349706 1720009229249576493569989 := by
  unfold tailWord_3349706
  simp only [CollatzResearch.WordTrace]
  refine ⟨30543453700648680270989243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81449209868396480722637981 30543453700648680270989243)
  ·
    refine ⟨45815180550973020406483865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30543453700648680270989243 45815180550973020406483865)
    ·
      refine ⟨34361385413229765304862899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45815180550973020406483865 34361385413229765304862899)
      ·
        refine ⟨51542078119844647957294349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34361385413229765304862899 51542078119844647957294349)
        ·
          refine ⟨19328279294941742983985381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51542078119844647957294349 19328279294941742983985381)
          ·
            refine ⟨3624052367801576809497259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19328279294941742983985381 3624052367801576809497259)
            ·
              refine ⟨5436078551702365214245889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624052367801576809497259 5436078551702365214245889)
              ·
                refine ⟨4077058913776773910684417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5436078551702365214245889 4077058913776773910684417)
                ·
                  refine ⟨3057794185332580433013313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4077058913776773910684417 3057794185332580433013313)
                  ·
                    refine ⟨2293345638999435324759985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3057794185332580433013313 2293345638999435324759985)
                    ·
                      refine ⟨1720009229249576493569989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293345638999435324759985 1720009229249576493569989)
                      ·
                        rfl

theorem cell23_3349706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 3, 4, 1, 2, 2, 2, 2].length) (baseStart_3349706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349706 prefixEnd_3349706 := by exact prefixLift 3349706
  have htrace : WordTrace (prefixWord ++ tailWord_3349706) baseStart_3349706 baseEnd_3349706 := by
    simpa [prefixWord, tailWord_3349706, baseEnd_3349706] using wordTrace_append hprefix tailTrace_3349706
  have hstable : (prefixWord ++ tailWord_3349706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349706).length < 2 ^ (prefixWord ++ tailWord_3349706).sum := by decide
  have hdescent : baseEnd_3349706 < baseStart_3349706 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349745 : List Nat := [1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 4]
def baseStart_3349745 : Nat := 118140960795 + 3349745 * 2 ^ 59
def prefixEnd_3349745 : Nat := 4983230072969 + 3 ^ 40 * 3349745 * 2
def baseEnd_3349745 : Nat := 1720029254995101840982309

theorem tailTrace_3349745 : CollatzResearch.WordTrace tailWord_3349745 prefixEnd_3349745 1720029254995101840982309 := by
  unfold tailWord_3349745
  simp only [CollatzResearch.WordTrace]
  refine ⟨122175237249453430744626689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81450158166302287163084459 122175237249453430744626689)
  ·
    refine ⟨91631427937090073058470017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122175237249453430744626689 91631427937090073058470017)
    ·
      refine ⟨68723570952817554793852513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91631427937090073058470017 68723570952817554793852513)
      ·
        refine ⟨51542678214613166095389385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68723570952817554793852513 51542678214613166095389385)
        ·
          refine ⟨38657008660959874571542039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51542678214613166095389385 38657008660959874571542039)
          ·
            refine ⟨57985512991439811857313059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38657008660959874571542039 57985512991439811857313059)
            ·
              refine ⟨86978269487159717785969589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57985512991439811857313059 86978269487159717785969589)
              ·
                refine ⟨8154212764421223542434649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86978269487159717785969589 8154212764421223542434649)
                ·
                  refine ⟨6115659573315917656825987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8154212764421223542434649 6115659573315917656825987)
                  ·
                    refine ⟨9173489359973876485238981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6115659573315917656825987 9173489359973876485238981)
                    ·
                      refine ⟨1720029254995101840982309, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9173489359973876485238981 1720029254995101840982309)
                      ·
                        rfl

theorem cell23_3349745_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 1, 1, 5, 2, 1, 4].length) (baseStart_3349745 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349745 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349745 prefixEnd_3349745 := by exact prefixLift 3349745
  have htrace : WordTrace (prefixWord ++ tailWord_3349745) baseStart_3349745 baseEnd_3349745 := by
    simpa [prefixWord, tailWord_3349745, baseEnd_3349745] using wordTrace_append hprefix tailTrace_3349745
  have hstable : (prefixWord ++ tailWord_3349745).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349745).length < 2 ^ (prefixWord ++ tailWord_3349745).sum := by decide
  have hdescent : baseEnd_3349745 < baseStart_3349745 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349745) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349746 : List Nat := [3, 2, 1, 3, 4, 1, 1, 3, 5]
def baseStart_3349746 : Nat := 118140960795 + 3349746 * 2 ^ 59
def prefixEnd_3349746 : Nat := 4983230072969 + 3 ^ 40 * 3349746 * 2
def baseEnd_3349746 : Nat := 191114418719528481896645

theorem tailTrace_3349746 : CollatzResearch.WordTrace tailWord_3349746 prefixEnd_3349746 191114418719528481896645 := by
  unfold tailWord_3349746
  simp only [CollatzResearch.WordTrace]
  refine ⟨30543818430612451978853273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81450182481633205276942061 30543818430612451978853273)
  ·
    refine ⟨22907863822959338984139955, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30543818430612451978853273 22907863822959338984139955)
    ·
      refine ⟨34361795734439008476209933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22907863822959338984139955 34361795734439008476209933)
      ·
        refine ⟨12885673400414628178578725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34361795734439008476209933 12885673400414628178578725)
        ·
          refine ⟨2416063762577742783483511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 12885673400414628178578725 2416063762577742783483511)
          ·
            refine ⟨3624095643866614175225267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416063762577742783483511 3624095643866614175225267)
            ·
              refine ⟨5436143465799921262837901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624095643866614175225267 5436143465799921262837901)
              ·
                refine ⟨2038553799674970473564213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5436143465799921262837901 2038553799674970473564213)
                ·
                  refine ⟨191114418719528481896645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2038553799674970473564213 191114418719528481896645)
                  ·
                    rfl

theorem cell23_3349746_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 4, 1, 1, 3, 5].length) (baseStart_3349746 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349746 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349746 prefixEnd_3349746 := by exact prefixLift 3349746
  have htrace : WordTrace (prefixWord ++ tailWord_3349746) baseStart_3349746 baseEnd_3349746 := by
    simpa [prefixWord, tailWord_3349746, baseEnd_3349746] using wordTrace_append hprefix tailTrace_3349746
  have hstable : (prefixWord ++ tailWord_3349746).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349746).length < 2 ^ (prefixWord ++ tailWord_3349746).sum := by decide
  have hdescent : baseEnd_3349746 < baseStart_3349746 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349746) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349772 : List Nat := [2, 2, 1, 2, 2, 3, 3, 1, 3, 4]
def baseStart_3349772 : Nat := 118140960795 + 3349772 * 2 ^ 59
def prefixEnd_3349772 : Nat := 4983230072969 + 3 ^ 40 * 3349772 * 2
def baseEnd_3349772 : Nat := 573347706324257745114895

theorem tailTrace_3349772 : CollatzResearch.WordTrace tailWord_3349772 prefixEnd_3349772 573347706324257745114895 := by
  unfold tailWord_3349772
  simp only [CollatzResearch.WordTrace]
  refine ⟨61088111010177807177929785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81450814680237076237239713 61088111010177807177929785)
  ·
    refine ⟨45816083257633355383447339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61088111010177807177929785 45816083257633355383447339)
    ·
      refine ⟨68724124886450033075171009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45816083257633355383447339 68724124886450033075171009)
      ·
        refine ⟨51543093664837524806378257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68724124886450033075171009 51543093664837524806378257)
        ·
          refine ⟨38657320248628143604783693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51543093664837524806378257 38657320248628143604783693)
          ·
            refine ⟨14496495093235553851793885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38657320248628143604783693 14496495093235553851793885)
            ·
              refine ⟨5436185659963332694422707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14496495093235553851793885 5436185659963332694422707)
              ·
                refine ⟨8154278489944999041634061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436185659963332694422707 8154278489944999041634061)
                ·
                  refine ⟨3057854433729374640612773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8154278489944999041634061 3057854433729374640612773)
                  ·
                    refine ⟨573347706324257745114895, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3057854433729374640612773 573347706324257745114895)
                    ·
                      rfl

theorem cell23_3349772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 3, 3, 1, 3, 4].length) (baseStart_3349772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349772 prefixEnd_3349772 := by exact prefixLift 3349772
  have htrace : WordTrace (prefixWord ++ tailWord_3349772) baseStart_3349772 baseEnd_3349772 := by
    simpa [prefixWord, tailWord_3349772, baseEnd_3349772] using wordTrace_append hprefix tailTrace_3349772
  have hstable : (prefixWord ++ tailWord_3349772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349772).length < 2 ^ (prefixWord ++ tailWord_3349772).sum := by decide
  have hdescent : baseEnd_3349772 < baseStart_3349772 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349856 : List Nat := [2, 1, 1, 3, 4, 3, 1, 1, 2, 3, 2]
def baseStart_3349856 : Nat := 118140960795 + 3349856 * 2 ^ 59
def prefixEnd_3349856 : Nat := 4983230072969 + 3 ^ 40 * 3349856 * 2
def baseEnd_3349856 : Nat := 1720086251347750906694299

theorem tailTrace_3349856 : CollatzResearch.WordTrace tailWord_3349856 prefixEnd_3349856 1720086251347750906694299 := by
  unfold tailWord_3349856
  simp only [CollatzResearch.WordTrace]
  refine ⟨61089642876025648350958711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81452857168034197801278281 61089642876025648350958711)
  ·
    refine ⟨91634464314038472526438067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61089642876025648350958711 91634464314038472526438067)
    ·
      refine ⟨137451696471057708789657101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91634464314038472526438067 137451696471057708789657101)
      ·
        refine ⟨51544386176646640796121413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137451696471057708789657101 51544386176646640796121413)
        ·
          refine ⟨9664572408121245149272765, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 51544386176646640796121413 9664572408121245149272765)
          ·
            refine ⟨3624214653045466930977287, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 9664572408121245149272765 3624214653045466930977287)
            ·
              refine ⟨5436321979568200396465931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624214653045466930977287 5436321979568200396465931)
              ·
                refine ⟨8154482969352300594698897, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436321979568200396465931 8154482969352300594698897)
                ·
                  refine ⟨6115862227014225446024173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8154482969352300594698897 6115862227014225446024173)
                  ·
                    refine ⟨2293448335130334542259065, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6115862227014225446024173 2293448335130334542259065)
                    ·
                      refine ⟨1720086251347750906694299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293448335130334542259065 1720086251347750906694299)
                      ·
                        rfl

theorem cell23_3349856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 3, 1, 1, 2, 3, 2].length) (baseStart_3349856 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349856 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349856 prefixEnd_3349856 := by exact prefixLift 3349856
  have htrace : WordTrace (prefixWord ++ tailWord_3349856) baseStart_3349856 baseEnd_3349856 := by
    simpa [prefixWord, tailWord_3349856, baseEnd_3349856] using wordTrace_append hprefix tailTrace_3349856
  have hstable : (prefixWord ++ tailWord_3349856).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349856).length < 2 ^ (prefixWord ++ tailWord_3349856).sum := by decide
  have hdescent : baseEnd_3349856 < baseStart_3349856 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349863 : List Nat := [1, 1, 5, 1, 4, 1, 2, 3, 1, 1, 3]
def baseStart_3349863 : Nat := 118140960795 + 3349863 * 2 ^ 59
def prefixEnd_3349863 : Nat := 4983230072969 + 3 ^ 40 * 3349863 * 2
def baseEnd_3349863 : Nat := 1720089845712332379306767

theorem tailTrace_3349863 : CollatzResearch.WordTrace tailWord_3349863 prefixEnd_3349863 1720089845712332379306767 := by
  unfold tailWord_3349863
  simp only [CollatzResearch.WordTrace]
  refine ⟨122179541063025936897422243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81453027375350624598281495 122179541063025936897422243)
  ·
    refine ⟨183269311594538905346133365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122179541063025936897422243 183269311594538905346133365)
    ·
      refine ⟨17181497961988022376200003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183269311594538905346133365 17181497961988022376200003)
      ·
        refine ⟨25772246942982033564300005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17181497961988022376200003 25772246942982033564300005)
        ·
          refine ⟨4832296301809131293306251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 25772246942982033564300005 4832296301809131293306251)
          ·
            refine ⟨7248444452713696939959377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832296301809131293306251 7248444452713696939959377)
            ·
              refine ⟨5436333339535272704969533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7248444452713696939959377 5436333339535272704969533)
              ·
                refine ⟨2038625002325727264363575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5436333339535272704969533 2038625002325727264363575)
                ·
                  refine ⟨3057937503488590896545363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038625002325727264363575 3057937503488590896545363)
                  ·
                    refine ⟨4586906255232886344818045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3057937503488590896545363 4586906255232886344818045)
                    ·
                      refine ⟨1720089845712332379306767, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586906255232886344818045 1720089845712332379306767)
                      ·
                        rfl

theorem cell23_3349863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 2, 3, 1, 1, 3].length) (baseStart_3349863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349863 prefixEnd_3349863 := by exact prefixLift 3349863
  have htrace : WordTrace (prefixWord ++ tailWord_3349863) baseStart_3349863 baseEnd_3349863 := by
    simpa [prefixWord, tailWord_3349863, baseEnd_3349863] using wordTrace_append hprefix tailTrace_3349863
  have hstable : (prefixWord ++ tailWord_3349863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349863).length < 2 ^ (prefixWord ++ tailWord_3349863).sum := by decide
  have hdescent : baseEnd_3349863 < baseStart_3349863 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349865 : List Nat := [1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 4]
def baseStart_3349865 : Nat := 118140960795 + 3349865 * 2 ^ 59
def prefixEnd_3349865 : Nat := 4983230072969 + 3 ^ 40 * 3349865 * 2
def baseEnd_3349865 : Nat := 1720090872673641371481757

theorem tailTrace_3349865 : CollatzResearch.WordTrace tailWord_3349865 prefixEnd_3349865 1720090872673641371481757 := by
  unfold tailWord_3349865
  simp only [CollatzResearch.WordTrace]
  refine ⟨122179614009018691238995049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81453076006012460825996699 122179614009018691238995049)
  ·
    refine ⟨91634710506764018429246287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122179614009018691238995049 91634710506764018429246287)
    ·
      refine ⟨137452065760146027643869431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91634710506764018429246287 137452065760146027643869431)
      ·
        refine ⟨206178098640219041465804147, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137452065760146027643869431 206178098640219041465804147)
        ·
          refine ⟨309267147960328562198706221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206178098640219041465804147 309267147960328562198706221)
          ·
            refine ⟨115975180485123210824514833, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 309267147960328562198706221 115975180485123210824514833)
            ·
              refine ⟨86981385363842408118386125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 115975180485123210824514833 86981385363842408118386125)
              ·
                refine ⟨32618019511440903044394797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 86981385363842408118386125 32618019511440903044394797)
                ·
                  refine ⟨12231757316790338641648049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32618019511440903044394797 12231757316790338641648049)
                  ·
                    refine ⟨9173817987592753981236037, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12231757316790338641648049 9173817987592753981236037)
                    ·
                      refine ⟨1720090872673641371481757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9173817987592753981236037 1720090872673641371481757)
                      ·
                        rfl

theorem cell23_3349865_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 2, 3, 3, 2, 4].length) (baseStart_3349865 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349865 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349865 prefixEnd_3349865 := by exact prefixLift 3349865
  have htrace : WordTrace (prefixWord ++ tailWord_3349865) baseStart_3349865 baseEnd_3349865 := by
    simpa [prefixWord, tailWord_3349865, baseEnd_3349865] using wordTrace_append hprefix tailTrace_3349865
  have hstable : (prefixWord ++ tailWord_3349865).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349865).length < 2 ^ (prefixWord ++ tailWord_3349865).sum := by decide
  have hdescent : baseEnd_3349865 < baseStart_3349865 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349865) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349869 : List Nat := [1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 4]
def baseStart_3349869 : Nat := 118140960795 + 3349869 * 2 ^ 59
def prefixEnd_3349869 : Nat := 4983230072969 + 3 ^ 40 * 3349869 * 2
def baseEnd_3349869 : Nat := 1720092926596259355831739

theorem tailTrace_3349869 : CollatzResearch.WordTrace tailWord_3349869 prefixEnd_3349869 1720092926596259355831739 := by
  unfold tailWord_3349869
  simp only [CollatzResearch.WordTrace]
  refine ⟨122179759901004199922140661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81453173267336133281427107 122179759901004199922140661)
  ·
    refine ⟨11454352490719143742700687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122179759901004199922140661 11454352490719143742700687)
    ·
      refine ⟨17181528736078715614051031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11454352490719143742700687 17181528736078715614051031)
      ·
        refine ⟨25772293104118073421076547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17181528736078715614051031 25772293104118073421076547)
        ·
          refine ⟨38658439656177110131614821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25772293104118073421076547 38658439656177110131614821)
          ·
            refine ⟨7248457435533208149677779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38658439656177110131614821 7248457435533208149677779)
            ·
              refine ⟨10872686153299812224516669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248457435533208149677779 10872686153299812224516669)
              ·
                refine ⟨4077257307487429584193751, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10872686153299812224516669 4077257307487429584193751)
                ·
                  refine ⟨6115885961231144376290627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077257307487429584193751 6115885961231144376290627)
                  ·
                    refine ⟨9173828941846716564435941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6115885961231144376290627 9173828941846716564435941)
                    ·
                      refine ⟨1720092926596259355831739, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9173828941846716564435941 1720092926596259355831739)
                      ·
                        rfl

theorem cell23_3349869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 4, 1, 3, 1, 1, 4].length) (baseStart_3349869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349869 prefixEnd_3349869 := by exact prefixLift 3349869
  have htrace : WordTrace (prefixWord ++ tailWord_3349869) baseStart_3349869 baseEnd_3349869 := by
    simpa [prefixWord, tailWord_3349869, baseEnd_3349869] using wordTrace_append hprefix tailTrace_3349869
  have hstable : (prefixWord ++ tailWord_3349869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349869).length < 2 ^ (prefixWord ++ tailWord_3349869).sum := by decide
  have hdescent : baseEnd_3349869 < baseStart_3349869 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349889 : List Nat := [1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 5]
def baseStart_3349889 : Nat := 118140960795 + 3349889 * 2 ^ 59
def prefixEnd_3349889 : Nat := 4983230072969 + 3 ^ 40 * 3349889 * 2
def baseEnd_3349889 : Nat := 1720103196209349277581647

theorem tailTrace_3349889 : CollatzResearch.WordTrace tailWord_3349889 prefixEnd_3349889 1720103196209349277581647 := by
  unfold tailWord_3349889
  simp only [CollatzResearch.WordTrace]
  refine ⟨122180489360931743337868721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81453659573954495558579147 122180489360931743337868721)
  ·
    refine ⟨91635367020698807503401541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122180489360931743337868721 91635367020698807503401541)
    ·
      refine ⟨17181631316381026406887789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91635367020698807503401541 17181631316381026406887789)
      ·
        refine ⟨6443111743642884902582921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17181631316381026406887789 6443111743642884902582921)
        ·
          refine ⟨4832333807732163676937191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6443111743642884902582921 4832333807732163676937191)
          ·
            refine ⟨7248500711598245515405787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4832333807732163676937191 7248500711598245515405787)
            ·
              refine ⟨10872751067397368273108681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7248500711598245515405787 10872751067397368273108681)
              ·
                refine ⟨8154563300548026204831511, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10872751067397368273108681 8154563300548026204831511)
                ·
                  refine ⟨12231844950822039307247267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8154563300548026204831511 12231844950822039307247267)
                  ·
                    refine ⟨18347767426233058960870901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12231844950822039307247267 18347767426233058960870901)
                    ·
                      refine ⟨1720103196209349277581647, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18347767426233058960870901 1720103196209349277581647)
                      ·
                        rfl

theorem cell23_3349889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 1, 1, 2, 1, 1, 5].length) (baseStart_3349889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349889 prefixEnd_3349889 := by exact prefixLift 3349889
  have htrace : WordTrace (prefixWord ++ tailWord_3349889) baseStart_3349889 baseEnd_3349889 := by
    simpa [prefixWord, tailWord_3349889, baseEnd_3349889] using wordTrace_append hprefix tailTrace_3349889
  have hstable : (prefixWord ++ tailWord_3349889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349889).length < 2 ^ (prefixWord ++ tailWord_3349889).sum := by decide
  have hdescent : baseEnd_3349889 < baseStart_3349889 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349896 : List Nat := [2, 1, 3, 3, 1, 3, 3, 1, 2, 4]
def baseStart_3349896 : Nat := 118140960795 + 3349896 * 2 ^ 59
def prefixEnd_3349896 : Nat := 4983230072969 + 3 ^ 40 * 3349896 * 2
def baseEnd_3349896 : Nat := 573368930191310250064705

theorem tailTrace_3349896 : CollatzResearch.WordTrace tailWord_3349896 prefixEnd_3349896 573368930191310250064705 := by
  unfold tailWord_3349896
  simp only [CollatzResearch.WordTrace]
  refine ⟨61090372335953191766686771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81453829781270922355582361 61090372335953191766686771)
  ·
    refine ⟨91635558503929787650030157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61090372335953191766686771 91635558503929787650030157)
    ·
      refine ⟨34363334438973670368761309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91635558503929787650030157 34363334438973670368761309)
      ·
        refine ⟨12886250414615126388285491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 34363334438973670368761309 12886250414615126388285491)
        ·
          refine ⟨19329375621922689582428237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12886250414615126388285491 19329375621922689582428237)
          ·
            refine ⟨7248515858221008593410589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19329375621922689582428237 7248515858221008593410589)
            ·
              refine ⟨2718193446832878222528971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7248515858221008593410589 2718193446832878222528971)
              ·
                refine ⟨4077290170249317333793457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718193446832878222528971 4077290170249317333793457)
                ·
                  refine ⟨3057967627686988000345093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4077290170249317333793457 3057967627686988000345093)
                  ·
                    refine ⟨573368930191310250064705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3057967627686988000345093 573368930191310250064705)
                    ·
                      rfl

theorem cell23_3349896_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 3, 3, 1, 2, 4].length) (baseStart_3349896 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349896 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349896 prefixEnd_3349896 := by exact prefixLift 3349896
  have htrace : WordTrace (prefixWord ++ tailWord_3349896) baseStart_3349896 baseEnd_3349896 := by
    simpa [prefixWord, tailWord_3349896, baseEnd_3349896] using wordTrace_append hprefix tailTrace_3349896
  have hstable : (prefixWord ++ tailWord_3349896).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349896).length < 2 ^ (prefixWord ++ tailWord_3349896).sum := by decide
  have hdescent : baseEnd_3349896 < baseStart_3349896 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349896) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349919 : List Nat := [1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 3]
def baseStart_3349919 : Nat := 118140960795 + 3349919 * 2 ^ 59
def prefixEnd_3349919 : Nat := 4983230072969 + 3 ^ 40 * 3349919 * 2
def baseEnd_3349919 : Nat := 1720118600628984160206509

theorem tailTrace_3349919 : CollatzResearch.WordTrace tailWord_3349919 prefixEnd_3349919 1720118600628984160206509 := by
  unfold tailWord_3349919
  simp only [CollatzResearch.WordTrace]
  refine ⟨122181583550823058461460811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81454389033882038974307207 122181583550823058461460811)
  ·
    refine ⟨183272375326234587692191217, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122181583550823058461460811 183272375326234587692191217)
    ·
      refine ⟨137454281494675940769143413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183272375326234587692191217 137454281494675940769143413)
      ·
        refine ⟨12886338890125869447107195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 137454281494675940769143413 12886338890125869447107195)
        ·
          refine ⟨19329508335188804170660793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12886338890125869447107195 19329508335188804170660793)
          ·
            refine ⟨14497131251391603127995595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19329508335188804170660793 14497131251391603127995595)
            ·
              refine ⟨21745696877087404691993393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14497131251391603127995595 21745696877087404691993393)
              ·
                refine ⟨16309272657815553518995045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21745696877087404691993393 16309272657815553518995045)
                ·
                  refine ⟨3057988623340416284811571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16309272657815553518995045 3057988623340416284811571)
                  ·
                    refine ⟨4586982935010624427217357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3057988623340416284811571 4586982935010624427217357)
                    ·
                      refine ⟨1720118600628984160206509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4586982935010624427217357 1720118600628984160206509)
                      ·
                        rfl

theorem cell23_3349919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 1, 2, 1, 2, 4, 1, 3].length) (baseStart_3349919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349919 prefixEnd_3349919 := by exact prefixLift 3349919
  have htrace : WordTrace (prefixWord ++ tailWord_3349919) baseStart_3349919 baseEnd_3349919 := by
    simpa [prefixWord, tailWord_3349919, baseEnd_3349919] using wordTrace_append hprefix tailTrace_3349919
  have hstable : (prefixWord ++ tailWord_3349919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349919).length < 2 ^ (prefixWord ++ tailWord_3349919).sum := by decide
  have hdescent : baseEnd_3349919 < baseStart_3349919 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349935 : List Nat := [1, 1, 2, 1, 2, 2, 1, 3, 4, 6]
def baseStart_3349935 : Nat := 118140960795 + 3349935 * 2 ^ 59
def prefixEnd_3349935 : Nat := 4983230072969 + 3 ^ 40 * 3349935 * 2
def baseEnd_3349935 : Nat := 573375605439818699202145

theorem tailTrace_3349935 : CollatzResearch.WordTrace tailWord_3349935 prefixEnd_3349935 573375605439818699202145 := by
  unfold tailWord_3349935
  simp only [CollatzResearch.WordTrace]
  refine ⟨122182167118765093194043259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81454778079176728796028839 122182167118765093194043259)
  ·
    refine ⟨183273250678147639791064889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122182167118765093194043259 183273250678147639791064889)
    ·
      refine ⟨137454938008610729843298667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183273250678147639791064889 137454938008610729843298667)
      ·
        refine ⟨206182407012916094764948001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137454938008610729843298667 206182407012916094764948001)
        ·
          refine ⟨154636805259687071073711001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206182407012916094764948001 154636805259687071073711001)
          ·
            refine ⟨115977603944765303305283251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154636805259687071073711001 115977603944765303305283251)
            ·
              refine ⟨173966405917147954957924877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115977603944765303305283251 173966405917147954957924877)
              ·
                refine ⟨65237402218930483109221829, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 173966405917147954957924877 65237402218930483109221829)
                ·
                  refine ⟨12232012916049465582979093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65237402218930483109221829 12232012916049465582979093)
                  ·
                    refine ⟨573375605439818699202145, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12232012916049465582979093 573375605439818699202145)
                    ·
                      rfl

theorem cell23_3349935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 1, 3, 4, 6].length) (baseStart_3349935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349935 prefixEnd_3349935 := by exact prefixLift 3349935
  have htrace : WordTrace (prefixWord ++ tailWord_3349935) baseStart_3349935 baseEnd_3349935 := by
    simpa [prefixWord, tailWord_3349935, baseEnd_3349935] using wordTrace_append hprefix tailTrace_3349935
  have hstable : (prefixWord ++ tailWord_3349935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349935).length < 2 ^ (prefixWord ++ tailWord_3349935).sum := by decide
  have hdescent : baseEnd_3349935 < baseStart_3349935 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349954 : List Nat := [3, 5, 2, 1, 2, 1, 1, 2, 1, 1, 4]
def baseStart_3349954 : Nat := 118140960795 + 3349954 * 2 ^ 59
def prefixEnd_3349954 : Nat := 4983230072969 + 3 ^ 40 * 3349954 * 2
def baseEnd_3349954 : Nat := 1720136572451891523268849

theorem tailTrace_3349954 : CollatzResearch.WordTrace tailWord_3349954 prefixEnd_3349954 1720136572451891523268849 := by
  unfold tailWord_3349954
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545715026424064859746229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81455240070464172959323277 30545715026424064859746229)
  ·
    refine ⟨2863660783727256080601209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 30545715026424064859746229 2863660783727256080601209)
    ·
      refine ⟨2147745587795442060450907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2863660783727256080601209 2147745587795442060450907)
      ·
        refine ⟨3221618381693163090676361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 2147745587795442060450907 3221618381693163090676361)
        ·
          refine ⟨2416213786269872318007271, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221618381693163090676361 2416213786269872318007271)
          ·
            refine ⟨3624320679404808477010907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416213786269872318007271 3624320679404808477010907)
            ·
              refine ⟨5436481019107212715516361, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624320679404808477010907 5436481019107212715516361)
              ·
                refine ⟨4077360764330409536637271, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5436481019107212715516361 4077360764330409536637271)
                ·
                  refine ⟨6116041146495614304955907, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077360764330409536637271 6116041146495614304955907)
                  ·
                    refine ⟨9174061719743421457433861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116041146495614304955907 9174061719743421457433861)
                    ·
                      refine ⟨1720136572451891523268849, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9174061719743421457433861 1720136572451891523268849)
                      ·
                        rfl

theorem cell23_3349954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 2, 1, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_3349954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349954 prefixEnd_3349954 := by exact prefixLift 3349954
  have htrace : WordTrace (prefixWord ++ tailWord_3349954) baseStart_3349954 baseEnd_3349954 := by
    simpa [prefixWord, tailWord_3349954, baseEnd_3349954] using wordTrace_append hprefix tailTrace_3349954
  have hstable : (prefixWord ++ tailWord_3349954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349954).length < 2 ^ (prefixWord ++ tailWord_3349954).sum := by decide
  have hdescent : baseEnd_3349954 < baseStart_3349954 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349959 : List Nat := [1, 1, 4, 1, 1, 3, 2, 3, 1, 4, 2]
def baseStart_3349959 : Nat := 118140960795 + 3349959 * 2 ^ 59
def prefixEnd_3349959 : Nat := 4983230072969 + 3 ^ 40 * 3349959 * 2
def baseEnd_3349959 : Nat := 1720139139855164003706325

theorem tailTrace_3349959 : CollatzResearch.WordTrace tailWord_3349959 prefixEnd_3349959 1720139139855164003706325 := by
  unfold tailWord_3349959
  simp only [CollatzResearch.WordTrace]
  refine ⟨122183042470678145292916931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81455361647118763528611287 122183042470678145292916931)
  ·
    refine ⟨183274563706017217939375397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122183042470678145292916931 183274563706017217939375397)
    ·
      refine ⟨34363980694878228363632887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183274563706017217939375397 34363980694878228363632887)
      ·
        refine ⟨51545971042317342545449331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34363980694878228363632887 51545971042317342545449331)
        ·
          refine ⟨77318956563476013818173997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51545971042317342545449331 77318956563476013818173997)
          ·
            refine ⟨28994608711303505181815249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77318956563476013818173997 28994608711303505181815249)
            ·
              refine ⟨21745956533477628886361437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28994608711303505181815249 21745956533477628886361437)
              ·
                refine ⟨8154733700054110832385539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21745956533477628886361437 8154733700054110832385539)
                ·
                  refine ⟨12232100550081166248578309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8154733700054110832385539 12232100550081166248578309)
                  ·
                    refine ⟨2293518853140218671608433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12232100550081166248578309 2293518853140218671608433)
                    ·
                      refine ⟨1720139139855164003706325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293518853140218671608433 1720139139855164003706325)
                      ·
                        rfl

theorem cell23_3349959_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 2, 3, 1, 4, 2].length) (baseStart_3349959 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349959 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349959 prefixEnd_3349959 := by exact prefixLift 3349959
  have htrace : WordTrace (prefixWord ++ tailWord_3349959) baseStart_3349959 baseEnd_3349959 := by
    simpa [prefixWord, tailWord_3349959, baseEnd_3349959] using wordTrace_append hprefix tailTrace_3349959
  have hstable : (prefixWord ++ tailWord_3349959).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349959).length < 2 ^ (prefixWord ++ tailWord_3349959).sum := by decide
  have hdescent : baseEnd_3349959 < baseStart_3349959 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349959) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3349962 : List Nat := [3, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5]
def baseStart_3349962 : Nat := 118140960795 + 3349962 * 2 ^ 59
def prefixEnd_3349962 : Nat := 4983230072969 + 3 ^ 40 * 3349962 * 2
def baseEnd_3349962 : Nat := 1720140680297127491968811

theorem tailTrace_3349962 : CollatzResearch.WordTrace tailWord_3349962 prefixEnd_3349962 1720140680297127491968811 := by
  unfold tailWord_3349962
  simp only [CollatzResearch.WordTrace]
  refine ⟨30545787972416819201319035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81455434593111517870184093 30545787972416819201319035)
  ·
    refine ⟨45818681958625228801978553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30545787972416819201319035 45818681958625228801978553)
    ·
      refine ⟨34364011468968921601483915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45818681958625228801978553 34364011468968921601483915)
      ·
        refine ⟨51546017203453382402225873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34364011468968921601483915 51546017203453382402225873)
        ·
          refine ⟨38659512902590036801669405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51546017203453382402225873 38659512902590036801669405)
          ·
            refine ⟨14497317338471263800626027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38659512902590036801669405 14497317338471263800626027)
            ·
              refine ⟨21745976007706895700939041, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14497317338471263800626027 21745976007706895700939041)
              ·
                refine ⟨16309482005780171775704281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21745976007706895700939041 16309482005780171775704281)
                ·
                  refine ⟨12232111504335128831778211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16309482005780171775704281 12232111504335128831778211)
                  ·
                    refine ⟨18348167256502693247667317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12232111504335128831778211 18348167256502693247667317)
                    ·
                      refine ⟨1720140680297127491968811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18348167256502693247667317 1720140680297127491968811)
                      ·
                        rfl

theorem cell23_3349962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 3, 1, 2, 2, 1, 5].length) (baseStart_3349962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3349962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3349962 prefixEnd_3349962 := by exact prefixLift 3349962
  have htrace : WordTrace (prefixWord ++ tailWord_3349962) baseStart_3349962 baseEnd_3349962 := by
    simpa [prefixWord, tailWord_3349962, baseEnd_3349962] using wordTrace_append hprefix tailTrace_3349962
  have hstable : (prefixWord ++ tailWord_3349962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3349962).length < 2 ^ (prefixWord ++ tailWord_3349962).sum := by decide
  have hdescent : baseEnd_3349962 < baseStart_3349962 := by decide
  rcases family_descends (prefixWord ++ tailWord_3349962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350012 : List Nat := [2, 2, 2, 1, 2, 1, 2, 2, 4, 5]
def baseStart_3350012 : Nat := 118140960795 + 3350012 * 2 ^ 59
def prefixEnd_3350012 : Nat := 4983230072969 + 3 ^ 40 * 3350012 * 2
def baseEnd_3350012 : Nat := 573388784776617432114527

theorem tailTrace_3350012 : CollatzResearch.WordTrace tailWord_3350012 prefixEnd_3350012 573388784776617432114527 := by
  unfold tailWord_3350012
  simp only [CollatzResearch.WordTrace]
  refine ⟨61092487769743067672298145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81456650359657423563064193 61092487769743067672298145)
  ·
    refine ⟨45819365827307300754223609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61092487769743067672298145 45819365827307300754223609)
    ·
      refine ⟨34364524370480475565667707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45819365827307300754223609 34364524370480475565667707)
      ·
        refine ⟨51546786555720713348501561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34364524370480475565667707 51546786555720713348501561)
        ·
          refine ⟨38660089916790535011376171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51546786555720713348501561 38660089916790535011376171)
          ·
            refine ⟨57990134875185802517064257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38660089916790535011376171 57990134875185802517064257)
            ·
              refine ⟨43492601156389351887798193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57990134875185802517064257 43492601156389351887798193)
              ·
                refine ⟨32619450867292013915848645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43492601156389351887798193 32619450867292013915848645)
                ·
                  refine ⟨6116147037617252609221621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32619450867292013915848645 6116147037617252609221621)
                  ·
                    refine ⟨573388784776617432114527, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6116147037617252609221621 573388784776617432114527)
                    ·
                      rfl

theorem cell23_3350012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 2, 2, 4, 5].length) (baseStart_3350012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350012 prefixEnd_3350012 := by exact prefixLift 3350012
  have htrace : WordTrace (prefixWord ++ tailWord_3350012) baseStart_3350012 baseEnd_3350012 := by
    simpa [prefixWord, tailWord_3350012, baseEnd_3350012] using wordTrace_append hprefix tailTrace_3350012
  have hstable : (prefixWord ++ tailWord_3350012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350012).length < 2 ^ (prefixWord ++ tailWord_3350012).sum := by decide
  have hdescent : baseEnd_3350012 < baseStart_3350012 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350069 : List Nat := [1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 3]
def baseStart_3350069 : Nat := 118140960795 + 3350069 * 2 ^ 59
def prefixEnd_3350069 : Nat := 4983230072969 + 3 ^ 40 * 3350069 * 2
def baseEnd_3350069 : Nat := 1720195622727158573330819

theorem tailTrace_3350069 : CollatzResearch.WordTrace tailWord_3350069 prefixEnd_3350069 1720195622727158573330819 := by
  unfold tailWord_3350069
  simp only [CollatzResearch.WordTrace]
  refine ⟨122187054500279634079421261, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81458036333519756052947507 122187054500279634079421261)
  ·
    refine ⟨45820145437604862779782973, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122187054500279634079421261 45820145437604862779782973)
    ·
      refine ⟨17182554539101823542418615, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45820145437604862779782973 17182554539101823542418615)
      ·
        refine ⟨25773831808652735313627923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17182554539101823542418615 25773831808652735313627923)
        ·
          refine ⟨38660747712979102970441885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25773831808652735313627923 38660747712979102970441885)
          ·
            refine ⟨14497780392367163613915707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38660747712979102970441885 14497780392367163613915707)
            ·
              refine ⟨21746670588550745420873561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14497780392367163613915707 21746670588550745420873561)
              ·
                refine ⟨16310002941413059065655171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21746670588550745420873561 16310002941413059065655171)
                ·
                  refine ⟨24465004412119588598482757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16310002941413059065655171 24465004412119588598482757)
                  ·
                    refine ⟨4587188327272422862215517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24465004412119588598482757 4587188327272422862215517)
                    ·
                      refine ⟨1720195622727158573330819, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587188327272422862215517 1720195622727158573330819)
                      ·
                        rfl

theorem cell23_3350069_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 3, 1, 2, 1, 4, 3].length) (baseStart_3350069 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350069 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350069 prefixEnd_3350069 := by exact prefixLift 3350069
  have htrace : WordTrace (prefixWord ++ tailWord_3350069) baseStart_3350069 baseEnd_3350069 := by
    simpa [prefixWord, tailWord_3350069, baseEnd_3350069] using wordTrace_append hprefix tailTrace_3350069
  have hstable : (prefixWord ++ tailWord_3350069).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350069).length < 2 ^ (prefixWord ++ tailWord_3350069).sum := by decide
  have hdescent : baseEnd_3350069 < baseStart_3350069 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350069) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350112 : List Nat := [2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7]
def baseStart_3350112 : Nat := 118140960795 + 3350112 * 2 ^ 59
def prefixEnd_3350112 : Nat := 4983230072969 + 3 ^ 40 * 3350112 * 2
def baseEnd_3350112 : Nat := 1720217702395301905093121

theorem tailTrace_3350112 : CollatzResearch.WordTrace tailWord_3350112 prefixEnd_3350112 1720217702395301905093121 := by
  unfold tailWord_3350112
  simp only [CollatzResearch.WordTrace]
  refine ⟨61094311419561926211618295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81459081892749234948824393 61094311419561926211618295)
  ·
    refine ⟨91641467129342889317427443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61094311419561926211618295 91641467129342889317427443)
    ·
      refine ⟨137462200694014333976141165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91641467129342889317427443 137462200694014333976141165)
      ·
        refine ⟨51548325260255375241052937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137462200694014333976141165 51548325260255375241052937)
        ·
          refine ⟨38661243945191531430789703, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51548325260255375241052937 38661243945191531430789703)
          ·
            refine ⟨57991865917787297146184555, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38661243945191531430789703 57991865917787297146184555)
            ·
              refine ⟨86987798876680945719276833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57991865917787297146184555 86987798876680945719276833)
              ·
                refine ⟨65240849157510709289457625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 86987798876680945719276833 65240849157510709289457625)
                ·
                  refine ⟨48930636868133031967093219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65240849157510709289457625 48930636868133031967093219)
                  ·
                    refine ⟨73395955302199547950639829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 48930636868133031967093219 73395955302199547950639829)
                    ·
                      refine ⟨1720217702395301905093121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73395955302199547950639829 1720217702395301905093121)
                      ·
                        rfl

theorem cell23_3350112_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 1, 2, 2, 1, 7].length) (baseStart_3350112 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350112 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350112 prefixEnd_3350112 := by exact prefixLift 3350112
  have htrace : WordTrace (prefixWord ++ tailWord_3350112) baseStart_3350112 baseEnd_3350112 := by
    simpa [prefixWord, tailWord_3350112, baseEnd_3350112] using wordTrace_append hprefix tailTrace_3350112
  have hstable : (prefixWord ++ tailWord_3350112).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350112).length < 2 ^ (prefixWord ++ tailWord_3350112).sum := by decide
  have hdescent : baseEnd_3350112 < baseStart_3350112 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350112) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350139 : List Nat := [1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 4]
def baseStart_3350139 : Nat := 118140960795 + 3350139 * 2 ^ 59
def prefixEnd_3350139 : Nat := 4983230072969 + 3 ^ 40 * 3350139 * 2
def baseEnd_3350139 : Nat := 1720231566372973299455497

theorem tailTrace_3350139 : CollatzResearch.WordTrace tailWord_3350139 prefixEnd_3350139 1720231566372973299455497 := by
  unfold tailWord_3350139
  simp only [CollatzResearch.WordTrace]
  refine ⟨122189607610026036034469471, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81459738406684024022979647 122189607610026036034469471)
  ·
    refine ⟨183284411415039054051704207, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122189607610026036034469471 183284411415039054051704207)
    ·
      refine ⟨274926617122558581077556311, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183284411415039054051704207 274926617122558581077556311)
      ·
        refine ⟨412389925683837871616334467, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 274926617122558581077556311 412389925683837871616334467)
        ·
          refine ⟨618584888525756807424501701, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412389925683837871616334467 618584888525756807424501701)
          ·
            refine ⟨115984666598579401392094069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 618584888525756807424501701 115984666598579401392094069)
            ·
              refine ⟨10873562493616818880508819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 115984666598579401392094069 10873562493616818880508819)
              ·
                refine ⟨16310343740425228320763229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10873562493616818880508819 16310343740425228320763229)
                ·
                  refine ⟨6116378902659460620286211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16310343740425228320763229 6116378902659460620286211)
                  ·
                    refine ⟨9174568353989190930429317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116378902659460620286211 9174568353989190930429317)
                    ·
                      refine ⟨1720231566372973299455497, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9174568353989190930429317 1720231566372973299455497)
                      ·
                        rfl

theorem cell23_3350139_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 5, 1, 3, 1, 4].length) (baseStart_3350139 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350139 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350139 prefixEnd_3350139 := by exact prefixLift 3350139
  have htrace : WordTrace (prefixWord ++ tailWord_3350139) baseStart_3350139 baseEnd_3350139 := by
    simpa [prefixWord, tailWord_3350139, baseEnd_3350139] using wordTrace_append hprefix tailTrace_3350139
  have hstable : (prefixWord ++ tailWord_3350139).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350139).length < 2 ^ (prefixWord ++ tailWord_3350139).sum := by decide
  have hdescent : baseEnd_3350139 < baseStart_3350139 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350139) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350149 : List Nat := [1, 3, 1, 1, 4, 1, 3, 2, 1, 6]
def baseStart_3350149 : Nat := 118140960795 + 3350149 * 2 ^ 59
def prefixEnd_3350149 : Nat := 4983230072969 + 3 ^ 40 * 3350149 * 2
def baseEnd_3350149 : Nat := 573412233726506086776817

theorem tailTrace_3350149 : CollatzResearch.WordTrace tailWord_3350149 prefixEnd_3350149 573412233726506086776817 := by
  unfold tailWord_3350149
  simp only [CollatzResearch.WordTrace]
  refine ⟨122189972339989807742333501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81459981559993205161555667 122189972339989807742333501)
  ·
    refine ⟨45821239627496177903375063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122189972339989807742333501 45821239627496177903375063)
    ·
      refine ⟨68731859441244266855062595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45821239627496177903375063 68731859441244266855062595)
      ·
        refine ⟨103097789161866400282593893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68731859441244266855062595 103097789161866400282593893)
        ·
          refine ⟨19330835467849950052986355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103097789161866400282593893 19330835467849950052986355)
          ·
            refine ⟨28996253201774925079479533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19330835467849950052986355 28996253201774925079479533)
            ·
              refine ⟨10873594950665596904804825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 28996253201774925079479533 10873594950665596904804825)
              ·
                refine ⟨8155196212999197678603619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10873594950665596904804825 8155196212999197678603619)
                ·
                  refine ⟨12232794319498796517905429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8155196212999197678603619 12232794319498796517905429)
                  ·
                    refine ⟨573412233726506086776817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12232794319498796517905429 573412233726506086776817)
                    ·
                      rfl

theorem cell23_3350149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 4, 1, 3, 2, 1, 6].length) (baseStart_3350149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350149 prefixEnd_3350149 := by exact prefixLift 3350149
  have htrace : WordTrace (prefixWord ++ tailWord_3350149) baseStart_3350149 baseEnd_3350149 := by
    simpa [prefixWord, tailWord_3350149, baseEnd_3350149] using wordTrace_append hprefix tailTrace_3350149
  have hstable : (prefixWord ++ tailWord_3350149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350149).length < 2 ^ (prefixWord ++ tailWord_3350149).sum := by decide
  have hdescent : baseEnd_3350149 < baseStart_3350149 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350159 : List Nat := [1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 3]
def baseStart_3350159 : Nat := 118140960795 + 3350159 * 2 ^ 59
def prefixEnd_3350159 : Nat := 4983230072969 + 3 ^ 40 * 3350159 * 2
def baseEnd_3350159 : Nat := 1720241835986063221205405

theorem tailTrace_3350159 : CollatzResearch.WordTrace tailWord_3350159 prefixEnd_3350159 1720241835986063221205405 := by
  unfold tailWord_3350159
  simp only [CollatzResearch.WordTrace]
  refine ⟨122190337069953579450197531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81460224713302386300131687 122190337069953579450197531)
  ·
    refine ⟨183285505604930369175296297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122190337069953579450197531 183285505604930369175296297)
    ·
      refine ⟨137464129203697776881472223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183285505604930369175296297 137464129203697776881472223)
      ·
        refine ⟨206196193805546665322208335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137464129203697776881472223 206196193805546665322208335)
        ·
          refine ⟨309294290708319997983312503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206196193805546665322208335 309294290708319997983312503)
          ·
            refine ⟨463941436062479996974968755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309294290708319997983312503 463941436062479996974968755)
            ·
              refine ⟨695912154093719995462453133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 463941436062479996974968755 695912154093719995462453133)
              ·
                refine ⟨260967057785144998298419925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 695912154093719995462453133 260967057785144998298419925)
                ·
                  refine ⟨6116415416839335897619217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 260967057785144998298419925 6116415416839335897619217)
                  ·
                    refine ⟨4587311562629501923214413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6116415416839335897619217 4587311562629501923214413)
                    ·
                      refine ⟨1720241835986063221205405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587311562629501923214413 1720241835986063221205405)
                      ·
                        rfl

theorem cell23_3350159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 3, 7, 2, 3].length) (baseStart_3350159 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350159 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350159 prefixEnd_3350159 := by exact prefixLift 3350159
  have htrace : WordTrace (prefixWord ++ tailWord_3350159) baseStart_3350159 baseEnd_3350159 := by
    simpa [prefixWord, tailWord_3350159, baseEnd_3350159] using wordTrace_append hprefix tailTrace_3350159
  have hstable : (prefixWord ++ tailWord_3350159).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350159).length < 2 ^ (prefixWord ++ tailWord_3350159).sum := by decide
  have hdescent : baseEnd_3350159 < baseStart_3350159 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350167 : List Nat := [1, 1, 3, 3, 2, 4, 2, 2, 1, 1, 3]
def baseStart_3350167 : Nat := 118140960795 + 3350167 * 2 ^ 59
def prefixEnd_3350167 : Nat := 4983230072969 + 3 ^ 40 * 3350167 * 2
def baseEnd_3350167 : Nat := 1720245943831299189905369

theorem tailTrace_3350167 : CollatzResearch.WordTrace tailWord_3350167 prefixEnd_3350167 1720245943831299189905369 := by
  unfold tailWord_3350167
  simp only [CollatzResearch.WordTrace]
  refine ⟨122190628853924596816488755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81460419235949731210992503 122190628853924596816488755)
  ·
    refine ⟨183285943280886895224733133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122190628853924596816488755 183285943280886895224733133)
    ·
      refine ⟨68732228730332585709274925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183285943280886895224733133 68732228730332585709274925)
      ·
        refine ⟨25774585773874719640978097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68732228730332585709274925 25774585773874719640978097)
        ·
          refine ⟨19330939330406039730733573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25774585773874719640978097 19330939330406039730733573)
          ·
            refine ⟨3624551124451132449512545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19330939330406039730733573 3624551124451132449512545)
            ·
              refine ⟨2718413343338349337134409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624551124451132449512545 2718413343338349337134409)
              ·
                refine ⟨2038810007503762002850807, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718413343338349337134409 2038810007503762002850807)
                ·
                  refine ⟨3058215011255643004276211, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038810007503762002850807 3058215011255643004276211)
                  ·
                    refine ⟨4587322516883464506414317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3058215011255643004276211 4587322516883464506414317)
                    ·
                      refine ⟨1720245943831299189905369, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587322516883464506414317 1720245943831299189905369)
                      ·
                        rfl

theorem cell23_3350167_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 4, 2, 2, 1, 1, 3].length) (baseStart_3350167 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350167 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350167 prefixEnd_3350167 := by exact prefixLift 3350167
  have htrace : WordTrace (prefixWord ++ tailWord_3350167) baseStart_3350167 baseEnd_3350167 := by
    simpa [prefixWord, tailWord_3350167, baseEnd_3350167] using wordTrace_append hprefix tailTrace_3350167
  have hstable : (prefixWord ++ tailWord_3350167).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350167).length < 2 ^ (prefixWord ++ tailWord_3350167).sum := by decide
  have hdescent : baseEnd_3350167 < baseStart_3350167 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350167) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350173 : List Nat := [1, 4, 2, 1, 1, 1, 1, 5, 3, 2, 2]
def baseStart_3350173 : Nat := 118140960795 + 3350173 * 2 ^ 59
def prefixEnd_3350173 : Nat := 4983230072969 + 3 ^ 40 * 3350173 * 2
def baseEnd_3350173 : Nat := 1720249024715226166430341

theorem tailTrace_3350173 : CollatzResearch.WordTrace tailWord_3350173 prefixEnd_3350173 1720249024715226166430341 := by
  unfold tailWord_3350173
  simp only [CollatzResearch.WordTrace]
  refine ⟨122190847691902859841207173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81460565127935239894138115 122190847691902859841207173)
  ·
    refine ⟨22910783942231786220226345, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122190847691902859841207173 22910783942231786220226345)
    ·
      refine ⟨17183087956673839665169759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22910783942231786220226345 17183087956673839665169759)
      ·
        refine ⟨25774631935010759497754639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17183087956673839665169759 25774631935010759497754639)
        ·
          refine ⟨38661947902516139246631959, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25774631935010759497754639 38661947902516139246631959)
          ·
            refine ⟨57992921853774208869947939, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38661947902516139246631959 57992921853774208869947939)
            ·
              refine ⟨86989382780661313304921909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 57992921853774208869947939 86989382780661313304921909)
              ·
                refine ⟨8155254635686998122336429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 86989382780661313304921909 8155254635686998122336429)
                ·
                  refine ⟨3058220488382624295876161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8155254635686998122336429 3058220488382624295876161)
                  ·
                    refine ⟨2293665366286968221907121, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058220488382624295876161 2293665366286968221907121)
                    ·
                      refine ⟨1720249024715226166430341, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293665366286968221907121 1720249024715226166430341)
                      ·
                        rfl

theorem cell23_3350173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 5, 3, 2, 2].length) (baseStart_3350173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350173 prefixEnd_3350173 := by exact prefixLift 3350173
  have htrace : WordTrace (prefixWord ++ tailWord_3350173) baseStart_3350173 baseEnd_3350173 := by
    simpa [prefixWord, tailWord_3350173, baseEnd_3350173] using wordTrace_append hprefix tailTrace_3350173
  have hstable : (prefixWord ++ tailWord_3350173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350173).length < 2 ^ (prefixWord ++ tailWord_3350173).sum := by decide
  have hdescent : baseEnd_3350173 < baseStart_3350173 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350176 : List Nat := [2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3]
def baseStart_3350176 : Nat := 118140960795 + 3350176 * 2 ^ 59
def prefixEnd_3350176 : Nat := 4983230072969 + 3 ^ 40 * 3350176 * 2
def baseEnd_3350176 : Nat := 1720250565157189654692827

theorem tailTrace_3350176 : CollatzResearch.WordTrace tailWord_3350176 prefixEnd_3350176 1720250565157189654692827 := by
  unfold tailWord_3350176
  simp only [CollatzResearch.WordTrace]
  refine ⟨61095478555445995676783191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81460638073927994235710921 61095478555445995676783191)
  ·
    refine ⟨91643217833168993515174787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61095478555445995676783191 91643217833168993515174787)
    ·
      refine ⟨137464826749753490272762181, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91643217833168993515174787 137464826749753490272762181)
      ·
        refine ⟨25774655015578779426142909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 137464826749753490272762181 25774655015578779426142909)
        ·
          refine ⟨9665495630842042284803591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25774655015578779426142909 9665495630842042284803591)
          ·
            refine ⟨14498243446263063427205387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665495630842042284803591 14498243446263063427205387)
            ·
              refine ⟨21747365169394595140808081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14498243446263063427205387 21747365169394595140808081)
              ·
                refine ⟨16310523877045946355606061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21747365169394595140808081 16310523877045946355606061)
                ·
                  refine ⟨6116446453892229883352273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16310523877045946355606061 6116446453892229883352273)
                  ·
                    refine ⟨4587334840419172412514205, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6116446453892229883352273 4587334840419172412514205)
                    ·
                      refine ⟨1720250565157189654692827, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587334840419172412514205 1720250565157189654692827)
                      ·
                        rfl

theorem cell23_3350176_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 3, 1, 1, 2, 3, 2, 3].length) (baseStart_3350176 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350176 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350176 prefixEnd_3350176 := by exact prefixLift 3350176
  have htrace : WordTrace (prefixWord ++ tailWord_3350176) baseStart_3350176 baseEnd_3350176 := by
    simpa [prefixWord, tailWord_3350176, baseEnd_3350176] using wordTrace_append hprefix tailTrace_3350176
  have hstable : (prefixWord ++ tailWord_3350176).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350176).length < 2 ^ (prefixWord ++ tailWord_3350176).sum := by decide
  have hdescent : baseEnd_3350176 < baseStart_3350176 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350176) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350237 : List Nat := [1, 4, 3, 3, 2, 1, 1, 1, 1, 2, 4]
def baseStart_3350237 : Nat := 118140960795 + 3350237 * 2 ^ 59
def prefixEnd_3350237 : Nat := 4983230072969 + 3 ^ 40 * 3350237 * 2
def baseEnd_3350237 : Nat := 1720281887477113916030047

theorem tailTrace_3350237 : CollatzResearch.WordTrace tailWord_3350237 prefixEnd_3350237 1720281887477113916030047 := by
  unfold tailWord_3350237
  simp only [CollatzResearch.WordTrace]
  refine ⟨122193181963670998771536965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81462121309113999181024643 122193181963670998771536965)
  ·
    refine ⟨22911221618188312269663181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122193181963670998771536965 22911221618188312269663181)
    ·
      refine ⟨8591708106820617101123693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22911221618188312269663181 8591708106820617101123693)
      ·
        refine ⟨3221890540057731412921385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 8591708106820617101123693 3221890540057731412921385)
        ·
          refine ⟨2416417905043298559691039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3221890540057731412921385 2416417905043298559691039)
          ·
            refine ⟨3624626857564947839536559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416417905043298559691039 3624626857564947839536559)
            ·
              refine ⟨5436940286347421759304839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624626857564947839536559 5436940286347421759304839)
              ·
                refine ⟨8155410429521132638957259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5436940286347421759304839 8155410429521132638957259)
                ·
                  refine ⟨12233115644281698958435889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8155410429521132638957259 12233115644281698958435889)
                  ·
                    refine ⟨9174836733211274218826917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12233115644281698958435889 9174836733211274218826917)
                    ·
                      refine ⟨1720281887477113916030047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9174836733211274218826917 1720281887477113916030047)
                      ·
                        rfl

theorem cell23_3350237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 3, 2, 1, 1, 1, 1, 2, 4].length) (baseStart_3350237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350237 prefixEnd_3350237 := by exact prefixLift 3350237
  have htrace : WordTrace (prefixWord ++ tailWord_3350237) baseStart_3350237 baseEnd_3350237 := by
    simpa [prefixWord, tailWord_3350237, baseEnd_3350237] using wordTrace_append hprefix tailTrace_3350237
  have hstable : (prefixWord ++ tailWord_3350237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350237).length < 2 ^ (prefixWord ++ tailWord_3350237).sum := by decide
  have hdescent : baseEnd_3350237 < baseStart_3350237 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350239 : List Nat := [1, 1, 2, 3, 2, 2, 1, 3, 2, 6]
def baseStart_3350239 : Nat := 118140960795 + 3350239 * 2 ^ 59
def prefixEnd_3350239 : Nat := 4983230072969 + 3 ^ 40 * 3350239 * 2
def baseEnd_3350239 : Nat := 573427638146140969401679

theorem tailTrace_3350239 : CollatzResearch.WordTrace tailWord_3350239 prefixEnd_3350239 573427638146140969401679 := by
  unfold tailWord_3350239
  simp only [CollatzResearch.WordTrace]
  refine ⟨122193254909663753113109771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81462169939775835408739847 122193254909663753113109771)
  ·
    refine ⟨183289882364495629669664657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122193254909663753113109771 183289882364495629669664657)
    ·
      refine ⟨137467411773371722252248493, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183289882364495629669664657 137467411773371722252248493)
      ·
        refine ⟨51550279415014395844593185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137467411773371722252248493 51550279415014395844593185)
        ·
          refine ⟨38662709561260796883444889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51550279415014395844593185 38662709561260796883444889)
          ·
            refine ⟨28997032170945597662583667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38662709561260796883444889 28997032170945597662583667)
            ·
              refine ⟨43495548256418396493875501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28997032170945597662583667 43495548256418396493875501)
              ·
                refine ⟨16310830596156898685203313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43495548256418396493875501 16310830596156898685203313)
                ·
                  refine ⟨12233122947117674013902485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16310830596156898685203313 12233122947117674013902485)
                  ·
                    refine ⟨573427638146140969401679, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12233122947117674013902485 573427638146140969401679)
                    ·
                      rfl

theorem cell23_3350239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 2, 6].length) (baseStart_3350239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350239 prefixEnd_3350239 := by exact prefixLift 3350239
  have htrace : WordTrace (prefixWord ++ tailWord_3350239) baseStart_3350239 baseEnd_3350239 := by
    simpa [prefixWord, tailWord_3350239, baseEnd_3350239] using wordTrace_append hprefix tailTrace_3350239
  have hstable : (prefixWord ++ tailWord_3350239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350239).length < 2 ^ (prefixWord ++ tailWord_3350239).sum := by decide
  have hdescent : baseEnd_3350239 < baseStart_3350239 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350249 : List Nat := [1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 5]
def baseStart_3350249 : Nat := 118140960795 + 3350249 * 2 ^ 59
def prefixEnd_3350249 : Nat := 4983230072969 + 3 ^ 40 * 3350249 * 2
def baseEnd_3350249 : Nat := 1720288049244967869079991

theorem tailTrace_3350249 : CollatzResearch.WordTrace tailWord_3350249 prefixEnd_3350249 1720288049244967869079991 := by
  unfold tailWord_3350249
  simp only [CollatzResearch.WordTrace]
  refine ⟨122193619639627524820973801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81462413093085016547315867 122193619639627524820973801)
  ·
    refine ⟨91645214729720643615730351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122193619639627524820973801 91645214729720643615730351)
    ·
      refine ⟨137467822094580965423595527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91645214729720643615730351 137467822094580965423595527)
      ·
        refine ⟨206201733141871448135393291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137467822094580965423595527 206201733141871448135393291)
        ·
          refine ⟨309302599712807172203089937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206201733141871448135393291 309302599712807172203089937)
          ·
            refine ⟨231976949784605379152317453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309302599712807172203089937 231976949784605379152317453)
            ·
              refine ⟨86991356169227017182119045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 231976949784605379152317453 86991356169227017182119045)
              ·
                refine ⟨16310879281730065721647321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 86991356169227017182119045 16310879281730065721647321)
                ·
                  refine ⟨12233159461297549291235491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16310879281730065721647321 12233159461297549291235491)
                  ·
                    refine ⟨18349739191946323936853237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12233159461297549291235491 18349739191946323936853237)
                    ·
                      refine ⟨1720288049244967869079991, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18349739191946323936853237 1720288049244967869079991)
                      ·
                        rfl

theorem cell23_3350249_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 3, 4, 2, 1, 5].length) (baseStart_3350249 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350249 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350249 prefixEnd_3350249 := by exact prefixLift 3350249
  have htrace : WordTrace (prefixWord ++ tailWord_3350249) baseStart_3350249 baseEnd_3350249 := by
    simpa [prefixWord, tailWord_3350249, baseEnd_3350249] using wordTrace_append hprefix tailTrace_3350249
  have hstable : (prefixWord ++ tailWord_3350249).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350249).length < 2 ^ (prefixWord ++ tailWord_3350249).sum := by decide
  have hdescent : baseEnd_3350249 < baseStart_3350249 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350249) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350259 : List Nat := [1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4]
def baseStart_3350259 : Nat := 118140960795 + 3350259 * 2 ^ 59
def prefixEnd_3350259 : Nat := 4983230072969 + 3 ^ 40 * 3350259 * 2
def baseEnd_3350259 : Nat := 1720293184051512829954945

theorem tailTrace_3350259 : CollatzResearch.WordTrace tailWord_3350259 prefixEnd_3350259 1720293184051512829954945 := by
  unfold tailWord_3350259
  simp only [CollatzResearch.WordTrace]
  refine ⟨122193984369591296528837831, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81462656246394197685891887 122193984369591296528837831)
  ·
    refine ⟨183290976554386944793256747, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122193984369591296528837831 183290976554386944793256747)
    ·
      refine ⟨274936464831580417189885121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183290976554386944793256747 274936464831580417189885121)
      ·
        refine ⟨206202348623685312892413841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274936464831580417189885121 206202348623685312892413841)
        ·
          refine ⟨154651761467763984669310381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206202348623685312892413841 154651761467763984669310381)
          ·
            refine ⟨57994410550411494250991393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154651761467763984669310381 57994410550411494250991393)
            ·
              refine ⟨43495807912808620688243545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57994410550411494250991393 43495807912808620688243545)
              ·
                refine ⟨32621855934606465516182659, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43495807912808620688243545 32621855934606465516182659)
                ·
                  refine ⟨48932783901909698274273989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32621855934606465516182659 48932783901909698274273989)
                  ·
                    refine ⟨9174896981608068426426373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 48932783901909698274273989 9174896981608068426426373)
                    ·
                      refine ⟨1720293184051512829954945, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9174896981608068426426373 1720293184051512829954945)
                      ·
                        rfl

theorem cell23_3350259_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 2, 1, 4, 4].length) (baseStart_3350259 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350259 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350259 prefixEnd_3350259 := by exact prefixLift 3350259
  have htrace : WordTrace (prefixWord ++ tailWord_3350259) baseStart_3350259 baseEnd_3350259 := by
    simpa [prefixWord, tailWord_3350259, baseEnd_3350259] using wordTrace_append hprefix tailTrace_3350259
  have hstable : (prefixWord ++ tailWord_3350259).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350259).length < 2 ^ (prefixWord ++ tailWord_3350259).sum := by decide
  have hdescent : baseEnd_3350259 < baseStart_3350259 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350259) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350263 : List Nat := [1, 1, 3, 1, 1, 1, 5, 2, 4, 2, 2]
def baseStart_3350263 : Nat := 118140960795 + 3350263 * 2 ^ 59
def prefixEnd_3350263 : Nat := 4983230072969 + 3 ^ 40 * 3350263 * 2
def baseEnd_3350263 : Nat := 1720295237974130814304927

theorem tailTrace_3350263 : CollatzResearch.WordTrace tailWord_3350263 prefixEnd_3350263 1720295237974130814304927 := by
  unfold tailWord_3350263
  simp only [CollatzResearch.WordTrace]
  refine ⟨122194130261576805211983443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81462753507717870141322295 122194130261576805211983443)
  ·
    refine ⟨183291195392365207817975165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122194130261576805211983443 183291195392365207817975165)
    ·
      refine ⟨68734198272136952931740687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183291195392365207817975165 68734198272136952931740687)
      ·
        refine ⟨103101297408205429397611031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68734198272136952931740687 103101297408205429397611031)
        ·
          refine ⟨154651946112308144096416547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103101297408205429397611031 154651946112308144096416547)
          ·
            refine ⟨231977919168462216144624821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154651946112308144096416547 231977919168462216144624821)
            ·
              refine ⟨21747929922043332763558577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 231977919168462216144624821 21747929922043332763558577)
              ·
                refine ⟨16310947441532499572668933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21747929922043332763558577 16310947441532499572668933)
                ·
                  refine ⟨3058302645287343669875425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16310947441532499572668933 3058302645287343669875425)
                  ·
                    refine ⟨2293726983965507752406569, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058302645287343669875425 2293726983965507752406569)
                    ·
                      refine ⟨1720295237974130814304927, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293726983965507752406569 1720295237974130814304927)
                      ·
                        rfl

theorem cell23_3350263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 5, 2, 4, 2, 2].length) (baseStart_3350263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350263 prefixEnd_3350263 := by exact prefixLift 3350263
  have htrace : WordTrace (prefixWord ++ tailWord_3350263) baseStart_3350263 baseEnd_3350263 := by
    simpa [prefixWord, tailWord_3350263, baseEnd_3350263] using wordTrace_append hprefix tailTrace_3350263
  have hstable : (prefixWord ++ tailWord_3350263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350263).length < 2 ^ (prefixWord ++ tailWord_3350263).sum := by decide
  have hdescent : baseEnd_3350263 < baseStart_3350263 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350280 : List Nat := [2, 1, 3, 2, 2, 1, 2, 4, 2, 2, 2]
def baseStart_3350280 : Nat := 118140960795 + 3350280 * 2 ^ 59
def prefixEnd_3350280 : Nat := 4983230072969 + 3 ^ 40 * 3350280 * 2
def baseEnd_3350280 : Nat := 1720303967145257247792349

theorem tailTrace_3350280 : CollatzResearch.WordTrace tailWord_3350280 prefixEnd_3350280 1720303967145257247792349 := by
  unfold tailWord_3350280
  simp only [CollatzResearch.WordTrace]
  refine ⟨61097375151257608557676147, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81463166868343478076901529 61097375151257608557676147)
  ·
    refine ⟨91646062726886412836514221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61097375151257608557676147 91646062726886412836514221)
    ·
      refine ⟨34367273522582404813692833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91646062726886412836514221 34367273522582404813692833)
      ·
        refine ⟨25775455141936803610269625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34367273522582404813692833 25775455141936803610269625)
        ·
          refine ⟨19331591356452602707702219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25775455141936803610269625 19331591356452602707702219)
          ·
            refine ⟨28997387034678904061553329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19331591356452602707702219 28997387034678904061553329)
            ·
              refine ⟨21748040276009178046164997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28997387034678904061553329 21748040276009178046164997)
              ·
                refine ⟨4077757551751720883655937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21748040276009178046164997 4077757551751720883655937)
                ·
                  refine ⟨3058318163813790662741953, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4077757551751720883655937 3058318163813790662741953)
                  ·
                    refine ⟨2293738622860342997056465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058318163813790662741953 2293738622860342997056465)
                    ·
                      refine ⟨1720303967145257247792349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293738622860342997056465 1720303967145257247792349)
                      ·
                        rfl

theorem cell23_3350280_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 2, 1, 2, 4, 2, 2, 2].length) (baseStart_3350280 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350280 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350280 prefixEnd_3350280 := by exact prefixLift 3350280
  have htrace : WordTrace (prefixWord ++ tailWord_3350280) baseStart_3350280 baseEnd_3350280 := by
    simpa [prefixWord, tailWord_3350280, baseEnd_3350280] using wordTrace_append hprefix tailTrace_3350280
  have hstable : (prefixWord ++ tailWord_3350280).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350280).length < 2 ^ (prefixWord ++ tailWord_3350280).sum := by decide
  have hdescent : baseEnd_3350280 < baseStart_3350280 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350280) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350286 : List Nat := [4, 1, 1, 2, 1, 1, 5, 1, 7]
def baseStart_3350286 : Nat := 118140960795 + 3350286 * 2 ^ 59
def prefixEnd_3350286 : Nat := 4983230072969 + 3 ^ 40 * 3350286 * 2
def baseEnd_3350286 : Nat := 191145227558798247146369

theorem tailTrace_3350286 : CollatzResearch.WordTrace tailWord_3350286 prefixEnd_3350286 191145227558798247146369 := by
  unfold tailWord_3350286
  simp only [CollatzResearch.WordTrace]
  refine ⟨15274371142561685017508839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81463312760328986760047141 15274371142561685017508839)
  ·
    refine ⟨22911556713842527526263259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15274371142561685017508839 22911556713842527526263259)
    ·
      refine ⟨34367335070763791289394889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22911556713842527526263259 34367335070763791289394889)
      ·
        refine ⟨25775501303072843467046167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34367335070763791289394889 25775501303072843467046167)
        ·
          refine ⟨38663251954609265200569251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25775501303072843467046167 38663251954609265200569251)
          ·
            refine ⟨57994877931913897800853877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38663251954609265200569251 57994877931913897800853877)
            ·
              refine ⟨5437019806116927918830051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 57994877931913897800853877 5437019806116927918830051)
              ·
                refine ⟨8155529709175391878245077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437019806116927918830051 8155529709175391878245077)
                ·
                  refine ⟨191145227558798247146369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8155529709175391878245077 191145227558798247146369)
                  ·
                    rfl

theorem cell23_3350286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 1, 5, 1, 7].length) (baseStart_3350286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350286 prefixEnd_3350286 := by exact prefixLift 3350286
  have htrace : WordTrace (prefixWord ++ tailWord_3350286) baseStart_3350286 baseEnd_3350286 := by
    simpa [prefixWord, tailWord_3350286, baseEnd_3350286] using wordTrace_append hprefix tailTrace_3350286
  have hstable : (prefixWord ++ tailWord_3350286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350286).length < 2 ^ (prefixWord ++ tailWord_3350286).sum := by decide
  have hdescent : baseEnd_3350286 < baseStart_3350286 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350296 : List Nat := [2, 1, 2, 3, 1, 1, 2, 3, 2, 3, 3]
def baseStart_3350296 : Nat := 118140960795 + 3350296 * 2 ^ 59
def prefixEnd_3350296 : Nat := 4983230072969 + 3 ^ 40 * 3350296 * 2
def baseEnd_3350296 : Nat := 1720312182835729185192275

theorem tailTrace_3350296 : CollatzResearch.WordTrace tailWord_3350296 prefixEnd_3350296 1720312182835729185192275 := by
  unfold tailWord_3350296
  simp only [CollatzResearch.WordTrace]
  refine ⟨61097666935228625923967371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81463555913638167898623161 61097666935228625923967371)
  ·
    refine ⟨91646500402842938885951057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61097666935228625923967371 91646500402842938885951057)
    ·
      refine ⟨68734875302132204164463293, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91646500402842938885951057 68734875302132204164463293)
      ·
        refine ⟨25775578238299576561673735, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68734875302132204164463293 25775578238299576561673735)
        ·
          refine ⟨38663367357449364842510603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25775578238299576561673735 38663367357449364842510603)
          ·
            refine ⟨57995051036174047263765905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38663367357449364842510603 57995051036174047263765905)
            ·
              refine ⟨43496288277130535447824429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 57995051036174047263765905 43496288277130535447824429)
              ·
                refine ⟨16311108103923950792934161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 43496288277130535447824429 16311108103923950792934161)
                ·
                  refine ⟨12233331077942963094700621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16311108103923950792934161 12233331077942963094700621)
                  ·
                    refine ⟨4587499154228611160512733, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12233331077942963094700621 4587499154228611160512733)
                    ·
                      refine ⟨1720312182835729185192275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587499154228611160512733 1720312182835729185192275)
                      ·
                        rfl

theorem cell23_3350296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 1, 2, 3, 2, 3, 3].length) (baseStart_3350296 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350296 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350296 prefixEnd_3350296 := by exact prefixLift 3350296
  have htrace : WordTrace (prefixWord ++ tailWord_3350296) baseStart_3350296 baseEnd_3350296 := by
    simpa [prefixWord, tailWord_3350296, baseEnd_3350296] using wordTrace_append hprefix tailTrace_3350296
  have hstable : (prefixWord ++ tailWord_3350296).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350296).length < 2 ^ (prefixWord ++ tailWord_3350296).sum := by decide
  have hdescent : baseEnd_3350296 < baseStart_3350296 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350316 : List Nat := [2, 2, 1, 1, 1, 5, 1, 3, 2, 5]
def baseStart_3350316 : Nat := 118140960795 + 3350316 * 2 ^ 59
def prefixEnd_3350316 : Nat := 4983230072969 + 3 ^ 40 * 3350316 * 2
def baseEnd_3350316 : Nat := 573440817482939702314061

theorem tailTrace_3350316 : CollatzResearch.WordTrace tailWord_3350316 prefixEnd_3350316 573440817482939702314061 := by
  unfold tailWord_3350316
  simp only [CollatzResearch.WordTrace]
  refine ⟨61098031665192397631831401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81464042220256530175775201 61098031665192397631831401)
  ·
    refine ⟨45823523748894298223873551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61098031665192397631831401 45823523748894298223873551)
    ·
      refine ⟨68735285623341447335810327, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45823523748894298223873551 68735285623341447335810327)
      ·
        refine ⟨103102928435012171003715491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68735285623341447335810327 103102928435012171003715491)
        ·
          refine ⟨154654392652518256505573237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103102928435012171003715491 154654392652518256505573237)
          ·
            refine ⟨14498849311173586547397491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 154654392652518256505573237 14498849311173586547397491)
            ·
              refine ⟨21748273966760379821096237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14498849311173586547397491 21748273966760379821096237)
              ·
                refine ⟨8155602737535142432911089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21748273966760379821096237 8155602737535142432911089)
                ·
                  refine ⟨6116702053151356824683317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8155602737535142432911089 6116702053151356824683317)
                  ·
                    refine ⟨573440817482939702314061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6116702053151356824683317 573440817482939702314061)
                    ·
                      rfl

theorem cell23_3350316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 2, 5].length) (baseStart_3350316 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350316 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350316 prefixEnd_3350316 := by exact prefixLift 3350316
  have htrace : WordTrace (prefixWord ++ tailWord_3350316) baseStart_3350316 baseEnd_3350316 := by
    simpa [prefixWord, tailWord_3350316, baseEnd_3350316] using wordTrace_append hprefix tailTrace_3350316
  have hstable : (prefixWord ++ tailWord_3350316).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350316).length < 2 ^ (prefixWord ++ tailWord_3350316).sum := by decide
  have hdescent : baseEnd_3350316 < baseStart_3350316 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350333 : List Nat := [1, 4, 1, 4, 1, 1, 2, 2, 2, 5]
def baseStart_3350333 : Nat := 118140960795 + 3350333 * 2 ^ 59
def prefixEnd_3350333 : Nat := 4983230072969 + 3 ^ 40 * 3350333 * 2
def baseEnd_3350333 : Nat := 573443727206648513476535

theorem tailTrace_3350333 : CollatzResearch.WordTrace tailWord_3350333 prefixEnd_3350333 573443727206648513476535 := by
  unfold tailWord_3350333
  simp only [CollatzResearch.WordTrace]
  refine ⟨122196683371323207167031653, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81464455580882138111354435 122196683371323207167031653)
  ·
    refine ⟨22911878132123101343818435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122196683371323207167031653 22911878132123101343818435)
    ·
      refine ⟨34367817198184652015727653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22911878132123101343818435 34367817198184652015727653)
      ·
        refine ⟨6443965724659622252948935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34367817198184652015727653 6443965724659622252948935)
        ·
          refine ⟨9665948586989433379423403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6443965724659622252948935 9665948586989433379423403)
          ·
            refine ⟨14498922880484150069135105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9665948586989433379423403 14498922880484150069135105)
            ·
              refine ⟨10874192160363112551851329, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14498922880484150069135105 10874192160363112551851329)
              ·
                refine ⟨8155644120272334413888497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10874192160363112551851329 8155644120272334413888497)
                ·
                  refine ⟨6116733090204250810416373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8155644120272334413888497 6116733090204250810416373)
                  ·
                    refine ⟨573443727206648513476535, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6116733090204250810416373 573443727206648513476535)
                    ·
                      rfl

theorem cell23_3350333_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 1, 1, 2, 2, 2, 5].length) (baseStart_3350333 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350333 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350333 prefixEnd_3350333 := by exact prefixLift 3350333
  have htrace : WordTrace (prefixWord ++ tailWord_3350333) baseStart_3350333 baseEnd_3350333 := by
    simpa [prefixWord, tailWord_3350333, baseEnd_3350333] using wordTrace_append hprefix tailTrace_3350333
  have hstable : (prefixWord ++ tailWord_3350333).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350333).length < 2 ^ (prefixWord ++ tailWord_3350333).sum := by decide
  have hdescent : baseEnd_3350333 < baseStart_3350333 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350333) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350353 : List Nat := [1, 2, 2, 1, 5, 1, 1, 1, 1, 6, 2]
def baseStart_3350353 : Nat := 118140960795 + 3350353 * 2 ^ 59
def prefixEnd_3350353 : Nat := 4983230072969 + 3 ^ 40 * 3350353 * 2
def baseEnd_3350353 : Nat := 1720341451233035462179513

theorem tailTrace_3350353 : CollatzResearch.WordTrace tailWord_3350353 prefixEnd_3350353 1720341451233035462179513 := by
  unfold tailWord_3350353
  simp only [CollatzResearch.WordTrace]
  refine ⟨122197412831250750582759713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81464941887500500388506475 122197412831250750582759713)
  ·
    refine ⟨91648059623438062937069785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122197412831250750582759713 91648059623438062937069785)
    ·
      refine ⟨68736044717578547202802339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91648059623438062937069785 68736044717578547202802339)
      ·
        refine ⟨103104067076367820804203509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68736044717578547202802339 103104067076367820804203509)
        ·
          refine ⟨9666006288409483200394079, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103104067076367820804203509 9666006288409483200394079)
          ·
            refine ⟨14499009432614224800591119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666006288409483200394079 14499009432614224800591119)
            ·
              refine ⟨21748514148921337200886679, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14499009432614224800591119 21748514148921337200886679)
              ·
                refine ⟨32622771223382005801330019, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21748514148921337200886679 32622771223382005801330019)
                ·
                  refine ⟨48934156835073008701995029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 32622771223382005801330019 48934156835073008701995029)
                  ·
                    refine ⟨2293788601644047282906017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 48934156835073008701995029 2293788601644047282906017)
                    ·
                      refine ⟨1720341451233035462179513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293788601644047282906017 1720341451233035462179513)
                      ·
                        rfl

theorem cell23_3350353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 1, 1, 1, 6, 2].length) (baseStart_3350353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350353 prefixEnd_3350353 := by exact prefixLift 3350353
  have htrace : WordTrace (prefixWord ++ tailWord_3350353) baseStart_3350353 baseEnd_3350353 := by
    simpa [prefixWord, tailWord_3350353, baseEnd_3350353] using wordTrace_append hprefix tailTrace_3350353
  have hstable : (prefixWord ++ tailWord_3350353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350353).length < 2 ^ (prefixWord ++ tailWord_3350353).sum := by decide
  have hdescent : baseEnd_3350353 < baseStart_3350353 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350370 : List Nat := [3, 3, 2, 1, 2, 1, 3, 1, 2, 1, 4]
def baseStart_3350370 : Nat := 118140960795 + 3350370 * 2 ^ 59
def prefixEnd_3350370 : Nat := 4983230072969 + 3 ^ 40 * 3350370 * 2
def baseEnd_3350370 : Nat := 1720350180404161895666935

theorem tailTrace_3350370 : CollatzResearch.WordTrace tailWord_3350370 prefixEnd_3350370 1720350180404161895666935 := by
  unfold tailWord_3350370
  simp only [CollatzResearch.WordTrace]
  refine ⟨30549508218047290621532141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81465355248126108324085709 30549508218047290621532141)
  ·
    refine ⟨11456065581767733983074553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 30549508218047290621532141 11456065581767733983074553)
    ·
      refine ⟨8592049186325800487305915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11456065581767733983074553 8592049186325800487305915)
      ·
        refine ⟨12888073779488700730958873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8592049186325800487305915 12888073779488700730958873)
        ·
          refine ⟨9666055334616525548219155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12888073779488700730958873 9666055334616525548219155)
          ·
            refine ⟨14499083001924788322328733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9666055334616525548219155 14499083001924788322328733)
            ·
              refine ⟨5437156125721795620873275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14499083001924788322328733 5437156125721795620873275)
              ·
                refine ⟨8155734188582693431309913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437156125721795620873275 8155734188582693431309913)
                ·
                  refine ⟨6116800641437020073482435, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8155734188582693431309913 6116800641437020073482435)
                  ·
                    refine ⟨9175200962155530110223653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6116800641437020073482435 9175200962155530110223653)
                    ·
                      refine ⟨1720350180404161895666935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9175200962155530110223653 1720350180404161895666935)
                      ·
                        rfl

theorem cell23_3350370_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 1, 3, 1, 2, 1, 4].length) (baseStart_3350370 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350370 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350370 prefixEnd_3350370 := by exact prefixLift 3350370
  have htrace : WordTrace (prefixWord ++ tailWord_3350370) baseStart_3350370 baseEnd_3350370 := by
    simpa [prefixWord, tailWord_3350370, baseEnd_3350370] using wordTrace_append hprefix tailTrace_3350370
  have hstable : (prefixWord ++ tailWord_3350370).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350370).length < 2 ^ (prefixWord ++ tailWord_3350370).sum := by decide
  have hdescent : baseEnd_3350370 < baseStart_3350370 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350370) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350376 : List Nat := [2, 1, 4, 2, 1, 1, 2, 2, 8]
def baseStart_3350376 : Nat := 118140960795 + 3350376 * 2 ^ 59
def prefixEnd_3350376 : Nat := 4983230072969 + 3 ^ 40 * 3350376 * 2
def baseEnd_3350376 : Nat := 191150362365343208021323

theorem tailTrace_3350376 : CollatzResearch.WordTrace tailWord_3350376 prefixEnd_3350376 191150362365343208021323 := by
  unfold tailWord_3350376
  simp only [CollatzResearch.WordTrace]
  refine ⟨61099125855083712755423491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81465501140111617007231321 61099125855083712755423491)
  ·
    refine ⟨91648688782625569133135237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61099125855083712755423491 91648688782625569133135237)
    ·
      refine ⟨17184129146742294212462857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91648688782625569133135237 17184129146742294212462857)
      ·
        refine ⟨12888096860056720659347143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17184129146742294212462857 12888096860056720659347143)
        ·
          refine ⟨19332145290085080989020715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12888096860056720659347143 19332145290085080989020715)
          ·
            refine ⟨28998217935127621483531073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19332145290085080989020715 28998217935127621483531073)
            ·
              refine ⟨21748663451345716112648305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 28998217935127621483531073 21748663451345716112648305)
              ·
                refine ⟨16311497588509287084486229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21748663451345716112648305 16311497588509287084486229)
                ·
                  refine ⟨191150362365343208021323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16311497588509287084486229 191150362365343208021323)
                  ·
                    rfl

theorem cell23_3350376_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 1, 2, 2, 8].length) (baseStart_3350376 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350376 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350376 prefixEnd_3350376 := by exact prefixLift 3350376
  have htrace : WordTrace (prefixWord ++ tailWord_3350376) baseStart_3350376 baseEnd_3350376 := by
    simpa [prefixWord, tailWord_3350376, baseEnd_3350376] using wordTrace_append hprefix tailTrace_3350376
  have hstable : (prefixWord ++ tailWord_3350376).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350376).length < 2 ^ (prefixWord ++ tailWord_3350376).sum := by decide
  have hdescent : baseEnd_3350376 < baseStart_3350376 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350376) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350380 : List Nat := [2, 2, 1, 1, 4, 2, 1, 5, 1, 4]
def baseStart_3350380 : Nat := 118140960795 + 3350380 * 2 ^ 59
def prefixEnd_3350380 : Nat := 4983230072969 + 3 ^ 40 * 3350380 * 2
def baseEnd_3350380 : Nat := 573451771736902285513963

theorem tailTrace_3350380 : CollatzResearch.WordTrace tailWord_3350380 prefixEnd_3350380 573451771736902285513963 := by
  unfold tailWord_3350380
  simp only [CollatzResearch.WordTrace]
  refine ⟨61099198801076467096996297, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81465598401435289462661729 61099198801076467096996297)
  ·
    refine ⟨45824399100807350322747223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61099198801076467096996297 45824399100807350322747223)
    ·
      refine ⟨68736598651211025484120835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45824399100807350322747223 68736598651211025484120835)
      ·
        refine ⟨103104897976816538226181253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68736598651211025484120835 103104897976816538226181253)
        ·
          refine ⟨19332168370653100917408985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103104897976816538226181253 19332168370653100917408985)
          ·
            refine ⟨14499126277989825688056739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19332168370653100917408985 14499126277989825688056739)
            ·
              refine ⟨21748689416984738532085109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14499126277989825688056739 21748689416984738532085109)
              ·
                refine ⟨2038939632842319237382979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21748689416984738532085109 2038939632842319237382979)
                ·
                  refine ⟨3058409449263478856074469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2038939632842319237382979 3058409449263478856074469)
                  ·
                    refine ⟨573451771736902285513963, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3058409449263478856074469 573451771736902285513963)
                    ·
                      rfl

theorem cell23_3350380_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 1, 5, 1, 4].length) (baseStart_3350380 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350380 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350380 prefixEnd_3350380 := by exact prefixLift 3350380
  have htrace : WordTrace (prefixWord ++ tailWord_3350380) baseStart_3350380 baseEnd_3350380 := by
    simpa [prefixWord, tailWord_3350380, baseEnd_3350380] using wordTrace_append hprefix tailTrace_3350380
  have hstable : (prefixWord ++ tailWord_3350380).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350380).length < 2 ^ (prefixWord ++ tailWord_3350380).sum := by decide
  have hdescent : baseEnd_3350380 < baseStart_3350380 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350380) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350423 : List Nat := [1, 1, 3, 3, 1, 3, 1, 4, 1, 5]
def baseStart_3350423 : Nat := 118140960795 + 3350423 * 2 ^ 59
def prefixEnd_3350423 : Nat := 4983230072969 + 3 ^ 40 * 3350423 * 2
def baseEnd_3350423 : Nat := 573459131626283396101397

theorem tailTrace_3350423 : CollatzResearch.WordTrace tailWord_3350423 prefixEnd_3350423 573459131626283396101397 := by
  unfold tailWord_3350423
  simp only [CollatzResearch.WordTrace]
  refine ⟨122199965940997152537807923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81466643960664768358538615 122199965940997152537807923)
  ·
    refine ⟨183299948911495728806711885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122199965940997152537807923 183299948911495728806711885)
    ·
      refine ⟨68737480841810898302516957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183299948911495728806711885 68737480841810898302516957)
      ·
        refine ⟨25776555315679086863443859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68737480841810898302516957 25776555315679086863443859)
        ·
          refine ⟨38664832973518630295165789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25776555315679086863443859 38664832973518630295165789)
          ·
            refine ⟨14499312365069486360687171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38664832973518630295165789 14499312365069486360687171)
            ·
              refine ⟨21748968547604229541030757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14499312365069486360687171 21748968547604229541030757)
              ·
                refine ⟨4077931602675793038943267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21748968547604229541030757 4077931602675793038943267)
                ·
                  refine ⟨6116897404013689558414901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4077931602675793038943267 6116897404013689558414901)
                  ·
                    refine ⟨573459131626283396101397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6116897404013689558414901 573459131626283396101397)
                    ·
                      rfl

theorem cell23_3350423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 3, 1, 4, 1, 5].length) (baseStart_3350423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350423 prefixEnd_3350423 := by exact prefixLift 3350423
  have htrace : WordTrace (prefixWord ++ tailWord_3350423) baseStart_3350423 baseEnd_3350423 := by
    simpa [prefixWord, tailWord_3350423, baseEnd_3350423] using wordTrace_append hprefix tailTrace_3350423
  have hstable : (prefixWord ++ tailWord_3350423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350423).length < 2 ^ (prefixWord ++ tailWord_3350423).sum := by decide
  have hdescent : baseEnd_3350423 < baseStart_3350423 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350456 : List Nat := [2, 1, 2, 1, 2, 3, 1, 1, 3, 1, 6]
def baseStart_3350456 : Nat := 118140960795 + 3350456 * 2 ^ 59
def prefixEnd_3350456 : Nat := 4983230072969 + 3 ^ 40 * 3350456 * 2
def baseEnd_3350456 : Nat := 1720394339740448559191539

theorem tailTrace_3350456 : CollatzResearch.WordTrace tailWord_3350456 prefixEnd_3350456 1720394339740448559191539 := by
  unfold tailWord_3350456
  simp only [CollatzResearch.WordTrace]
  refine ⟨61100584774938799586879611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81467446366585066115839481 61100584774938799586879611)
  ·
    refine ⟨91650877162408199380319417, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61100584774938799586879611 91650877162408199380319417)
    ·
      refine ⟨68738157871806149535239563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91650877162408199380319417 68738157871806149535239563)
      ·
        refine ⟨103107236807709224302859345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68738157871806149535239563 103107236807709224302859345)
        ·
          refine ⟨77330427605781918227144509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103107236807709224302859345 77330427605781918227144509)
          ·
            refine ⟨28998910352168219335179191, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77330427605781918227144509 28998910352168219335179191)
            ·
              refine ⟨43498365528252329002768787, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28998910352168219335179191 43498365528252329002768787)
              ·
                refine ⟨65247548292378493504153181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43498365528252329002768787 65247548292378493504153181)
                ·
                  refine ⟨24467830609641935064057443, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65247548292378493504153181 24467830609641935064057443)
                  ·
                    refine ⟨36701745914462902596086165, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24467830609641935064057443 36701745914462902596086165)
                    ·
                      refine ⟨1720394339740448559191539, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36701745914462902596086165 1720394339740448559191539)
                      ·
                        rfl

theorem cell23_3350456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 3, 1, 1, 3, 1, 6].length) (baseStart_3350456 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350456 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350456 prefixEnd_3350456 := by exact prefixLift 3350456
  have htrace : WordTrace (prefixWord ++ tailWord_3350456) baseStart_3350456 baseEnd_3350456 := by
    simpa [prefixWord, tailWord_3350456, baseEnd_3350456] using wordTrace_append hprefix tailTrace_3350456
  have hstable : (prefixWord ++ tailWord_3350456).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350456).length < 2 ^ (prefixWord ++ tailWord_3350456).sum := by decide
  have hdescent : baseEnd_3350456 < baseStart_3350456 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350463 : List Nat := [1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 3]
def baseStart_3350463 : Nat := 118140960795 + 3350463 * 2 ^ 59
def prefixEnd_3350463 : Nat := 4983230072969 + 3 ^ 40 * 3350463 * 2
def baseEnd_3350463 : Nat := 1720397934105030031804007

theorem tailTrace_3350463 : CollatzResearch.WordTrace tailWord_3350463 prefixEnd_3350463 1720397934105030031804007 := by
  unfold tailWord_3350463
  simp only [CollatzResearch.WordTrace]
  refine ⟨122201424860852239369264043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81467616573901492912842695 122201424860852239369264043)
  ·
    refine ⟨183302137291278359053896065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122201424860852239369264043 183302137291278359053896065)
    ·
      refine ⟨137476602968458769290422049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183302137291278359053896065 137476602968458769290422049)
      ·
        refine ⟨103107452226344076967816537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137476602968458769290422049 103107452226344076967816537)
        ·
          refine ⟨77330589169758057725862403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103107452226344076967816537 77330589169758057725862403)
          ·
            refine ⟨115995883754637086588793605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77330589169758057725862403 115995883754637086588793605)
            ·
              refine ⟨21749228203994453735398801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 115995883754637086588793605 21749228203994453735398801)
              ·
                refine ⟨16311921152995840301549101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21749228203994453735398801 16311921152995840301549101)
                ·
                  refine ⟨6116970432373440113080913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16311921152995840301549101 6116970432373440113080913)
                  ·
                    refine ⟨4587727824280080084810685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6116970432373440113080913 4587727824280080084810685)
                    ·
                      refine ⟨1720397934105030031804007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587727824280080084810685 1720397934105030031804007)
                      ·
                        rfl

theorem cell23_3350463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 1, 4, 2, 3, 2, 3].length) (baseStart_3350463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350463 prefixEnd_3350463 := by exact prefixLift 3350463
  have htrace : WordTrace (prefixWord ++ tailWord_3350463) baseStart_3350463 baseEnd_3350463 := by
    simpa [prefixWord, tailWord_3350463, baseEnd_3350463] using wordTrace_append hprefix tailTrace_3350463
  have hstable : (prefixWord ++ tailWord_3350463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350463).length < 2 ^ (prefixWord ++ tailWord_3350463).sum := by decide
  have hdescent : baseEnd_3350463 < baseStart_3350463 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350480 : List Nat := [2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3]
def baseStart_3350480 : Nat := 118140960795 + 3350480 * 2 ^ 59
def prefixEnd_3350480 : Nat := 4983230072969 + 3 ^ 40 * 3350480 * 2
def baseEnd_3350480 : Nat := 1720406663276156465291429

theorem tailTrace_3350480 : CollatzResearch.WordTrace tailWord_3350480 prefixEnd_3350480 1720406663276156465291429 := by
  unfold tailWord_3350480
  simp only [CollatzResearch.WordTrace]
  refine ⟨61101022450895325636316447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81468029934527100848421929 61101022450895325636316447)
  ·
    refine ⟨91651533676342988454474671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61101022450895325636316447 91651533676342988454474671)
    ·
      refine ⟨137477300514514482681712007, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91651533676342988454474671 137477300514514482681712007)
      ·
        refine ⟨206215950771771724022568011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137477300514514482681712007 206215950771771724022568011)
        ·
          refine ⟨309323926157657586033852017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206215950771771724022568011 309323926157657586033852017)
          ·
            refine ⟨231992944618243189525389013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 309323926157657586033852017 231992944618243189525389013)
            ·
              refine ⟨5437334639490074754501305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 231992944618243189525389013 5437334639490074754501305)
              ·
                refine ⟨4078000979617556065875979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437334639490074754501305 4078000979617556065875979)
                ·
                  refine ⟨6117001469426334098813969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078000979617556065875979 6117001469426334098813969)
                  ·
                    refine ⟨4587751102069750574110477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6117001469426334098813969 4587751102069750574110477)
                    ·
                      refine ⟨1720406663276156465291429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587751102069750574110477 1720406663276156465291429)
                      ·
                        rfl

theorem cell23_3350480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 7, 2, 1, 2, 3].length) (baseStart_3350480 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350480 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350480 prefixEnd_3350480 := by exact prefixLift 3350480
  have htrace : WordTrace (prefixWord ++ tailWord_3350480) baseStart_3350480 baseEnd_3350480 := by
    simpa [prefixWord, tailWord_3350480, baseEnd_3350480] using wordTrace_append hprefix tailTrace_3350480
  have hstable : (prefixWord ++ tailWord_3350480).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350480).length < 2 ^ (prefixWord ++ tailWord_3350480).sum := by decide
  have hdescent : baseEnd_3350480 < baseStart_3350480 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350490 : List Nat := [3, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4]
def baseStart_3350490 : Nat := 118140960795 + 3350490 * 2 ^ 59
def prefixEnd_3350490 : Nat := 4983230072969 + 3 ^ 40 * 3350490 * 2
def baseEnd_3350490 : Nat := 1720411798082701426166383

theorem tailTrace_3350490 : CollatzResearch.WordTrace tailWord_3350490 prefixEnd_3350490 1720411798082701426166383 := by
  unfold tailWord_3350490
  simp only [CollatzResearch.WordTrace]
  refine ⟨30550602407938605745124231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81468273087836281986997949 30550602407938605745124231)
  ·
    refine ⟨45825903611907908617686347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30550602407938605745124231 45825903611907908617686347)
    ·
      refine ⟨68738855417861862926529521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45825903611907908617686347 68738855417861862926529521)
      ·
        refine ⟨51554141563396397194897141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68738855417861862926529521 51554141563396397194897141)
        ·
          refine ⟨4833200771568412237021607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 51554141563396397194897141 4833200771568412237021607)
          ·
            refine ⟨7249801157352618355532411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833200771568412237021607 7249801157352618355532411)
            ·
              refine ⟨10874701736028927533298617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7249801157352618355532411 10874701736028927533298617)
              ·
                refine ⟨8156026302021695649973963, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10874701736028927533298617 8156026302021695649973963)
                ·
                  refine ⟨12234039453032543474960945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156026302021695649973963 12234039453032543474960945)
                  ·
                    refine ⟨9175529589774407606220709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12234039453032543474960945 9175529589774407606220709)
                    ·
                      refine ⟨1720411798082701426166383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9175529589774407606220709 1720411798082701426166383)
                      ·
                        rfl

theorem cell23_3350490_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 1, 2, 1, 2, 4].length) (baseStart_3350490 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350490 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350490 prefixEnd_3350490 := by exact prefixLift 3350490
  have htrace : WordTrace (prefixWord ++ tailWord_3350490) baseStart_3350490 baseEnd_3350490 := by
    simpa [prefixWord, tailWord_3350490, baseEnd_3350490] using wordTrace_append hprefix tailTrace_3350490
  have hstable : (prefixWord ++ tailWord_3350490).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350490).length < 2 ^ (prefixWord ++ tailWord_3350490).sum := by decide
  have hdescent : baseEnd_3350490 < baseStart_3350490 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350490) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350496 : List Nat := [2, 1, 1, 3, 1, 1, 1, 2, 4, 7]
def baseStart_3350496 : Nat := 118140960795 + 3350496 * 2 ^ 59
def prefixEnd_3350496 : Nat := 4983230072969 + 3 ^ 40 * 3350496 * 2
def baseEnd_3350496 : Nat := 573471626322209467563785

theorem tailTrace_3350496 : CollatzResearch.WordTrace tailWord_3350496 prefixEnd_3350496 573471626322209467563785 := by
  unfold tailWord_3350496
  simp only [CollatzResearch.WordTrace]
  refine ⟨61101314234866343002607671, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81468418979821790670143561 61101314234866343002607671)
  ·
    refine ⟨91651971352299514503911507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61101314234866343002607671 91651971352299514503911507)
    ·
      refine ⟨137477957028449271755867261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91651971352299514503911507 137477957028449271755867261)
      ·
        refine ⟨51554233885668476908450223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137477957028449271755867261 51554233885668476908450223)
        ·
          refine ⟨77331350828502715362675335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51554233885668476908450223 77331350828502715362675335)
          ·
            refine ⟨115997026242754073044013003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77331350828502715362675335 115997026242754073044013003)
            ·
              refine ⟨173995539364131109566019505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 115997026242754073044013003 173995539364131109566019505)
              ·
                refine ⟨130496654523098332174514629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 173995539364131109566019505 130496654523098332174514629)
                ·
                  refine ⟨24468122723080937282721493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 130496654523098332174514629 24468122723080937282721493)
                  ·
                    refine ⟨573471626322209467563785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24468122723080937282721493 573471626322209467563785)
                    ·
                      rfl

theorem cell23_3350496_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 2, 4, 7].length) (baseStart_3350496 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350496 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350496 prefixEnd_3350496 := by exact prefixLift 3350496
  have htrace : WordTrace (prefixWord ++ tailWord_3350496) baseStart_3350496 baseEnd_3350496 := by
    simpa [prefixWord, tailWord_3350496, baseEnd_3350496] using wordTrace_append hprefix tailTrace_3350496
  have hstable : (prefixWord ++ tailWord_3350496).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350496).length < 2 ^ (prefixWord ++ tailWord_3350496).sum := by decide
  have hdescent : baseEnd_3350496 < baseStart_3350496 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350496) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350520 : List Nat := [2, 1, 2, 1, 1, 3, 3, 2, 3, 3, 2]
def baseStart_3350520 : Nat := 118140960795 + 3350520 * 2 ^ 59
def prefixEnd_3350520 : Nat := 4983230072969 + 3 ^ 40 * 3350520 * 2
def baseEnd_3350520 : Nat := 1720427202502336308791245

theorem tailTrace_3350520 : CollatzResearch.WordTrace tailWord_3350520 prefixEnd_3350520 1720427202502336308791245 := by
  unfold tailWord_3350520
  simp only [CollatzResearch.WordTrace]
  refine ⟨61101751910822869052044507, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81469002547763825402726009 61101751910822869052044507)
  ·
    refine ⟨91652627866234303578066761, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61101751910822869052044507 91652627866234303578066761)
    ·
      refine ⟨68739470899675727683550071, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91652627866234303578066761 68739470899675727683550071)
      ·
        refine ⟨103109206349513591525325107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68739470899675727683550071 103109206349513591525325107)
        ·
          refine ⟨154663809524270387287987661, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103109206349513591525325107 154663809524270387287987661)
          ·
            refine ⟨57998928571601395232995373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154663809524270387287987661 57998928571601395232995373)
            ·
              refine ⟨21749598214350523212373265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 57998928571601395232995373 21749598214350523212373265)
              ·
                refine ⟨16312198660762892409279949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21749598214350523212373265 16312198660762892409279949)
                ·
                  refine ⟨6117074497786084653479981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16312198660762892409279949 6117074497786084653479981)
                  ·
                    refine ⟨2293902936669781745054993, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6117074497786084653479981 2293902936669781745054993)
                    ·
                      refine ⟨1720427202502336308791245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293902936669781745054993 1720427202502336308791245)
                      ·
                        rfl

theorem cell23_3350520_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 3, 3, 2, 3, 3, 2].length) (baseStart_3350520 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350520 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350520 prefixEnd_3350520 := by exact prefixLift 3350520
  have htrace : WordTrace (prefixWord ++ tailWord_3350520) baseStart_3350520 baseEnd_3350520 := by
    simpa [prefixWord, tailWord_3350520, baseEnd_3350520] using wordTrace_append hprefix tailTrace_3350520
  have hstable : (prefixWord ++ tailWord_3350520).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350520).length < 2 ^ (prefixWord ++ tailWord_3350520).sum := by decide
  have hdescent : baseEnd_3350520 < baseStart_3350520 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350520) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350548 : List Nat := [2, 4, 3, 2, 1, 2, 2, 1, 1, 2, 3]
def baseStart_3350548 : Nat := 118140960795 + 3350548 * 2 ^ 59
def prefixEnd_3350548 : Nat := 4983230072969 + 3 ^ 40 * 3350548 * 2
def baseEnd_3350548 : Nat := 1720441579960662199241117

theorem tailTrace_3350548 : CollatzResearch.WordTrace tailWord_3350548 prefixEnd_3350548 1720441579960662199241117 := by
  unfold tailWord_3350548
  simp only [CollatzResearch.WordTrace]
  refine ⟨61102262532772149443054149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81469683377029532590738865 61102262532772149443054149)
  ·
    refine ⟨11456674224894778020572653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61102262532772149443054149 11456674224894778020572653)
    ·
      refine ⟨4296252834335541757714745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 11456674224894778020572653 4296252834335541757714745)
      ·
        refine ⟨3222189625751656318286059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 4296252834335541757714745 3222189625751656318286059)
        ·
          refine ⟨4833284438627484477429089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222189625751656318286059 4833284438627484477429089)
          ·
            refine ⟨3624963328970613358071817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4833284438627484477429089 3624963328970613358071817)
            ·
              refine ⟨2718722496727960018553863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3624963328970613358071817 2718722496727960018553863)
              ·
                refine ⟨4078083745091940027830795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718722496727960018553863 4078083745091940027830795)
                ·
                  refine ⟨6117125617637910041746193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078083745091940027830795 6117125617637910041746193)
                  ·
                    refine ⟨4587844213228432531309645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6117125617637910041746193 4587844213228432531309645)
                    ·
                      refine ⟨1720441579960662199241117, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587844213228432531309645 1720441579960662199241117)
                      ·
                        rfl

theorem cell23_3350548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 2, 1, 2, 2, 1, 1, 2, 3].length) (baseStart_3350548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350548 prefixEnd_3350548 := by exact prefixLift 3350548
  have htrace : WordTrace (prefixWord ++ tailWord_3350548) baseStart_3350548 baseEnd_3350548 := by
    simpa [prefixWord, tailWord_3350548, baseEnd_3350548] using wordTrace_append hprefix tailTrace_3350548
  have hstable : (prefixWord ++ tailWord_3350548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350548).length < 2 ^ (prefixWord ++ tailWord_3350548).sum := by decide
  have hdescent : baseEnd_3350548 < baseStart_3350548 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350554 : List Nat := [3, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2]
def baseStart_3350554 : Nat := 118140960795 + 3350554 * 2 ^ 59
def prefixEnd_3350554 : Nat := 4983230072969 + 3 ^ 40 * 3350554 * 2
def baseEnd_3350554 : Nat := 1720444660844589175766089

theorem tailTrace_3350554 : CollatzResearch.WordTrace tailWord_3350554 prefixEnd_3350554 1720444660844589175766089 := by
  unfold tailWord_3350554
  simp only [CollatzResearch.WordTrace]
  refine ⟨30551185975880640477706679, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81469829269015041273884477 30551185975880640477706679)
  ·
    refine ⟨45826778963820960716560019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30551185975880640477706679 45826778963820960716560019)
    ·
      refine ⟨68740168445731441074840029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45826778963820960716560019 68740168445731441074840029)
      ·
        refine ⟨25777563167149290403065011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68740168445731441074840029 25777563167149290403065011)
        ·
          refine ⟨38666344750723935604597517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25777563167149290403065011 38666344750723935604597517)
          ·
            refine ⟨14499879281521475851724069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38666344750723935604597517 14499879281521475851724069)
            ·
              refine ⟨2718727365285276722198263, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14499879281521475851724069 2718727365285276722198263)
              ·
                refine ⟨4078091047927915083297395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2718727365285276722198263 4078091047927915083297395)
                ·
                  refine ⟨6117136571891872624946093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078091047927915083297395 6117136571891872624946093)
                  ·
                    refine ⟨2293926214459452234354785, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6117136571891872624946093 2293926214459452234354785)
                    ·
                      refine ⟨1720444660844589175766089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293926214459452234354785 1720444660844589175766089)
                      ·
                        rfl

theorem cell23_3350554_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 3, 4, 1, 1, 3, 2].length) (baseStart_3350554 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350554 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350554 prefixEnd_3350554 := by exact prefixLift 3350554
  have htrace : WordTrace (prefixWord ++ tailWord_3350554) baseStart_3350554 baseEnd_3350554 := by
    simpa [prefixWord, tailWord_3350554, baseEnd_3350554] using wordTrace_append hprefix tailTrace_3350554
  have hstable : (prefixWord ++ tailWord_3350554).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350554).length < 2 ^ (prefixWord ++ tailWord_3350554).sum := by decide
  have hdescent : baseEnd_3350554 < baseStart_3350554 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350554) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350561 : List Nat := [1, 2, 3, 2, 5, 1, 1, 2, 2, 1, 3]
def baseStart_3350561 : Nat := 118140960795 + 3350561 * 2 ^ 59
def prefixEnd_3350561 : Nat := 4983230072969 + 3 ^ 40 * 3350561 * 2
def baseEnd_3350561 : Nat := 1720448255209170648378557

theorem tailTrace_3350561 : CollatzResearch.WordTrace tailWord_3350561 prefixEnd_3350561 1720448255209170648378557 := by
  unfold tailWord_3350561
  simp only [CollatzResearch.WordTrace]
  refine ⟨122204999214497202106331537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81469999476331468070887691 122204999214497202106331537)
  ·
    refine ⟨91653749410872901579748653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122204999214497202106331537 91653749410872901579748653)
    ·
      refine ⟨34370156029077338092405745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91653749410872901579748653 34370156029077338092405745)
      ·
        refine ⟨25777617021808003569304309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34370156029077338092405745 25777617021808003569304309)
        ·
          refine ⟨2416651595794500334622279, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 25777617021808003569304309 2416651595794500334622279)
          ·
            refine ⟨3624977393691750501933419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416651595794500334622279 3624977393691750501933419)
            ·
              refine ⟨5437466090537625752900129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3624977393691750501933419 5437466090537625752900129)
              ·
                refine ⟨4078099567903219314675097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5437466090537625752900129 4078099567903219314675097)
                ·
                  refine ⟨3058574675927414486006323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4078099567903219314675097 3058574675927414486006323)
                  ·
                    refine ⟨4587862013891121729009485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3058574675927414486006323 4587862013891121729009485)
                    ·
                      refine ⟨1720448255209170648378557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4587862013891121729009485 1720448255209170648378557)
                      ·
                        rfl

theorem cell23_3350561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 5, 1, 1, 2, 2, 1, 3].length) (baseStart_3350561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350561 prefixEnd_3350561 := by exact prefixLift 3350561
  have htrace : WordTrace (prefixWord ++ tailWord_3350561) baseStart_3350561 baseEnd_3350561 := by
    simpa [prefixWord, tailWord_3350561, baseEnd_3350561] using wordTrace_append hprefix tailTrace_3350561
  have hstable : (prefixWord ++ tailWord_3350561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350561).length < 2 ^ (prefixWord ++ tailWord_3350561).sum := by decide
  have hdescent : baseEnd_3350561 < baseStart_3350561 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350563 : List Nat := [1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4]
def baseStart_3350563 : Nat := 118140960795 + 3350563 * 2 ^ 59
def prefixEnd_3350563 : Nat := 4983230072969 + 3 ^ 40 * 3350563 * 2
def baseEnd_3350563 : Nat := 1720449282170479640553547

theorem tailTrace_3350563 : CollatzResearch.WordTrace tailWord_3350563 prefixEnd_3350563 1720449282170479640553547 := by
  unfold tailWord_3350563
  simp only [CollatzResearch.WordTrace]
  refine ⟨122205072160489956447904343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81470048106993304298602895 122205072160489956447904343)
  ·
    refine ⟨183307608240734934671856515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122205072160489956447904343 183307608240734934671856515)
    ·
      refine ⟨274961412361102402007784773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183307608240734934671856515 274961412361102402007784773)
      ·
        refine ⟨51555264817706700376459645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 274961412361102402007784773 51555264817706700376459645)
        ·
          refine ⟨19333224306640012641172367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51555264817706700376459645 19333224306640012641172367)
          ·
            refine ⟨28999836459960018961758551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19333224306640012641172367 28999836459960018961758551)
            ·
              refine ⟨43499754689940028442637827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 28999836459960018961758551 43499754689940028442637827)
              ·
                refine ⟨65249632034910042663956741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43499754689940028442637827 65249632034910042663956741)
                ·
                  refine ⟨12234306006545632999491889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65249632034910042663956741 12234306006545632999491889)
                  ·
                    refine ⟨9175729504909224749618917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12234306006545632999491889 9175729504909224749618917)
                    ·
                      refine ⟨1720449282170479640553547, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9175729504909224749618917 1720449282170479640553547)
                      ·
                        rfl

theorem cell23_3350563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 1, 1, 4, 2, 4].length) (baseStart_3350563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350563 prefixEnd_3350563 := by exact prefixLift 3350563
  have htrace : WordTrace (prefixWord ++ tailWord_3350563) baseStart_3350563 baseEnd_3350563 := by
    simpa [prefixWord, tailWord_3350563, baseEnd_3350563] using wordTrace_append hprefix tailTrace_3350563
  have hstable : (prefixWord ++ tailWord_3350563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350563).length < 2 ^ (prefixWord ++ tailWord_3350563).sum := by decide
  have hdescent : baseEnd_3350563 < baseStart_3350563 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350584 : List Nat := [2, 1, 2, 1, 6, 2, 1, 1, 1, 4, 2]
def baseStart_3350584 : Nat := 118140960795 + 3350584 * 2 ^ 59
def prefixEnd_3350584 : Nat := 4983230072969 + 3 ^ 40 * 3350584 * 2
def baseEnd_3350584 : Nat := 1720460065264224058390951

theorem tailTrace_3350584 : CollatzResearch.WordTrace tailWord_3350584 prefixEnd_3350584 1720460065264224058390951 := by
  unfold tailWord_3350584
  simp only [CollatzResearch.WordTrace]
  refine ⟨61102919046706938517209403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81470558728942584689612537 61102919046706938517209403)
  ·
    refine ⟨91654378570060407775814105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61102919046706938517209403 91654378570060407775814105)
    ·
      refine ⟨68740783927545305831860579, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91654378570060407775814105 68740783927545305831860579)
      ·
        refine ⟨103111175891317958747790869, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68740783927545305831860579 103111175891317958747790869)
        ·
          refine ⟨4833336369905529316302697, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 103111175891317958747790869 4833336369905529316302697)
          ·
            refine ⟨3625002277429146987227023, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4833336369905529316302697 3625002277429146987227023)
            ·
              refine ⟨5437503416143720480840535, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625002277429146987227023 5437503416143720480840535)
              ·
                refine ⟨8156255124215580721260803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437503416143720480840535 8156255124215580721260803)
                ·
                  refine ⟨12234382686323371081891205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156255124215580721260803 12234382686323371081891205)
                  ·
                    refine ⟨2293946753685632077854601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12234382686323371081891205 2293946753685632077854601)
                    ·
                      refine ⟨1720460065264224058390951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2293946753685632077854601 1720460065264224058390951)
                      ·
                        rfl

theorem cell23_3350584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 6, 2, 1, 1, 1, 4, 2].length) (baseStart_3350584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350584 prefixEnd_3350584 := by exact prefixLift 3350584
  have htrace : WordTrace (prefixWord ++ tailWord_3350584) baseStart_3350584 baseEnd_3350584 := by
    simpa [prefixWord, tailWord_3350584, baseEnd_3350584] using wordTrace_append hprefix tailTrace_3350584
  have hstable : (prefixWord ++ tailWord_3350584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350584).length < 2 ^ (prefixWord ++ tailWord_3350584).sum := by decide
  have hdescent : baseEnd_3350584 < baseStart_3350584 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350620 : List Nat := [2, 2, 4, 1, 1, 2, 1, 1, 4, 5]
def baseStart_3350620 : Nat := 118140960795 + 3350620 * 2 ^ 59
def prefixEnd_3350620 : Nat := 4983230072969 + 3 ^ 40 * 3350620 * 2
def baseEnd_3350620 : Nat := 573492850189261972513595

theorem tailTrace_3350620 : CollatzResearch.WordTrace tailWord_3350620 prefixEnd_3350620 573492850189261972513595 := by
  unfold tailWord_3350620
  simp only [CollatzResearch.WordTrace]
  refine ⟨61103575560641727591364657, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81471434080855636788486209 61103575560641727591364657)
  ·
    refine ⟨45827681670481295693523493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61103575560641727591364657 45827681670481295693523493)
    ·
      refine ⟨8592690313215242942535655, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 45827681670481295693523493 8592690313215242942535655)
      ·
        refine ⟨12889035469822864413803483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8592690313215242942535655 12889035469822864413803483)
        ·
          refine ⟨19333553204734296620705225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889035469822864413803483 19333553204734296620705225)
          ·
            refine ⟨14500164903550722465528919, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19333553204734296620705225 14500164903550722465528919)
            ·
              refine ⟨21750247355326083698293379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14500164903550722465528919 21750247355326083698293379)
              ·
                refine ⟨32625371032989125547440069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21750247355326083698293379 32625371032989125547440069)
                ·
                  refine ⟨6117257068685461040145013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 32625371032989125547440069 6117257068685461040145013)
                  ·
                    refine ⟨573492850189261972513595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6117257068685461040145013 573492850189261972513595)
                    ·
                      rfl

theorem cell23_3350620_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 1, 2, 1, 1, 4, 5].length) (baseStart_3350620 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350620 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350620 prefixEnd_3350620 := by exact prefixLift 3350620
  have htrace : WordTrace (prefixWord ++ tailWord_3350620) baseStart_3350620 baseEnd_3350620 := by
    simpa [prefixWord, tailWord_3350620, baseEnd_3350620] using wordTrace_append hprefix tailTrace_3350620
  have hstable : (prefixWord ++ tailWord_3350620).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350620).length < 2 ^ (prefixWord ++ tailWord_3350620).sum := by decide
  have hdescent : baseEnd_3350620 < baseStart_3350620 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350620) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350623 : List Nat := [1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 4]
def baseStart_3350623 : Nat := 118140960795 + 3350623 * 2 ^ 59
def prefixEnd_3350623 : Nat := 4983230072969 + 3 ^ 40 * 3350623 * 2
def baseEnd_3350623 : Nat := 1720480091009749405803271

theorem tailTrace_3350623 : CollatzResearch.WordTrace tailWord_3350623 prefixEnd_3350623 1720480091009749405803271 := by
  unfold tailWord_3350623
  simp only [CollatzResearch.WordTrace]
  refine ⟨122207260540272586695088523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81471507026848391130059015 122207260540272586695088523)
  ·
    refine ⟨183310890810408880042632785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122207260540272586695088523 183310890810408880042632785)
    ·
      refine ⟨137483168107806660031974589, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183310890810408880042632785 137483168107806660031974589)
      ·
        refine ⟨51556188040427497511990471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137483168107806660031974589 51556188040427497511990471)
        ·
          refine ⟨77334282060641246267985707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51556188040427497511990471 77334282060641246267985707)
          ·
            refine ⟨116001423090961869401978561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77334282060641246267985707 116001423090961869401978561)
            ·
              refine ⟨87001067318221402051483921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 116001423090961869401978561 87001067318221402051483921)
              ·
                refine ⟨65250800488666051538612941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 87001067318221402051483921 65250800488666051538612941)
                ·
                  refine ⟨24469050183249769326979853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 65250800488666051538612941 24469050183249769326979853)
                  ·
                    refine ⟨9175893818718663497617445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24469050183249769326979853 9175893818718663497617445)
                    ·
                      refine ⟨1720480091009749405803271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9175893818718663497617445 1720480091009749405803271)
                      ·
                        rfl

theorem cell23_3350623_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 2, 2, 3, 3, 4].length) (baseStart_3350623 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350623 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350623 prefixEnd_3350623 := by exact prefixLift 3350623
  have htrace : WordTrace (prefixWord ++ tailWord_3350623) baseStart_3350623 baseEnd_3350623 := by
    simpa [prefixWord, tailWord_3350623, baseEnd_3350623] using wordTrace_append hprefix tailTrace_3350623
  have hstable : (prefixWord ++ tailWord_3350623).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350623).length < 2 ^ (prefixWord ++ tailWord_3350623).sum := by decide
  have hdescent : baseEnd_3350623 < baseStart_3350623 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350623) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350663 : List Nat := [1, 1, 4, 2, 1, 1, 2, 1, 10]
def baseStart_3350663 : Nat := 118140960795 + 3350663 * 2 ^ 59
def prefixEnd_3350663 : Nat := 4983230072969 + 3 ^ 40 * 3350663 * 2
def baseEnd_3350663 : Nat := 191166736692881027700343

theorem tailTrace_3350663 : CollatzResearch.WordTrace tailWord_3350663 prefixEnd_3350663 191166736692881027700343 := by
  unfold tailWord_3350663
  simp only [CollatzResearch.WordTrace]
  refine ⟨122208719460127673526544643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81472479640085115684363095 122208719460127673526544643)
  ·
    refine ⟨183313079190191510289816965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122208719460127673526544643 183313079190191510289816965)
    ·
      refine ⟨34371202348160908179340681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183313079190191510289816965 34371202348160908179340681)
      ·
        refine ⟨25778401761120681134505511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34371202348160908179340681 25778401761120681134505511)
        ·
          refine ⟨38667602641681021701758267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25778401761120681134505511 38667602641681021701758267)
          ·
            refine ⟨58001403962521532552637401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38667602641681021701758267 58001403962521532552637401)
            ·
              refine ⟨43501052971891149414478051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58001403962521532552637401 43501052971891149414478051)
              ·
                refine ⟨65251579457836724121717077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43501052971891149414478051 65251579457836724121717077)
                ·
                  refine ⟨191166736692881027700343, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 65251579457836724121717077 191166736692881027700343)
                  ·
                    rfl

theorem cell23_3350663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 1, 2, 1, 10].length) (baseStart_3350663 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350663 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350663 prefixEnd_3350663 := by exact prefixLift 3350663
  have htrace : WordTrace (prefixWord ++ tailWord_3350663) baseStart_3350663 baseEnd_3350663 := by
    simpa [prefixWord, tailWord_3350663, baseEnd_3350663] using wordTrace_append hprefix tailTrace_3350663
  have hstable : (prefixWord ++ tailWord_3350663).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350663).length < 2 ^ (prefixWord ++ tailWord_3350663).sum := by decide
  have hdescent : baseEnd_3350663 < baseStart_3350663 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350684 : List Nat := [2, 2, 3, 2, 1, 1, 3, 4, 1, 4]
def baseStart_3350684 : Nat := 118140960795 + 3350684 * 2 ^ 59
def prefixEnd_3350684 : Nat := 4983230072969 + 3 ^ 40 * 3350684 * 2
def baseEnd_3350684 : Nat := 573503804443224555713497

theorem tailTrace_3350684 : CollatzResearch.WordTrace tailWord_3350684 prefixEnd_3350684 573503804443224555713497 := by
  unfold tailWord_3350684
  simp only [CollatzResearch.WordTrace]
  refine ⟨61104742696525797056529553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81472990262034396075372737 61104742696525797056529553)
  ·
    refine ⟨45828557022394347792397165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61104742696525797056529553 45828557022394347792397165)
    ·
      refine ⟨17185708883397880422148937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45828557022394347792397165 17185708883397880422148937)
      ·
        refine ⟨12889281662548410316611703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17185708883397880422148937 12889281662548410316611703)
        ·
          refine ⟨19333922493822615474917555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12889281662548410316611703 19333922493822615474917555)
          ·
            refine ⟨29000883740733923212376333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19333922493822615474917555 29000883740733923212376333)
            ·
              refine ⟨10875331402775221204641125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29000883740733923212376333 10875331402775221204641125)
              ·
                refine ⟨2039124638020353975870211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10875331402775221204641125 2039124638020353975870211)
                ·
                  refine ⟨3058686957030530963805317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039124638020353975870211 3058686957030530963805317)
                  ·
                    refine ⟨573503804443224555713497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3058686957030530963805317 573503804443224555713497)
                    ·
                      rfl

theorem cell23_3350684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 3, 4, 1, 4].length) (baseStart_3350684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350684 prefixEnd_3350684 := by exact prefixLift 3350684
  have htrace : WordTrace (prefixWord ++ tailWord_3350684) baseStart_3350684 baseEnd_3350684 := by
    simpa [prefixWord, tailWord_3350684, baseEnd_3350684] using wordTrace_append hprefix tailTrace_3350684
  have hstable : (prefixWord ++ tailWord_3350684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350684).length < 2 ^ (prefixWord ++ tailWord_3350684).sum := by decide
  have hdescent : baseEnd_3350684 < baseStart_3350684 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350703 : List Nat := [1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 7]
def baseStart_3350703 : Nat := 118140960795 + 3350703 * 2 ^ 59
def prefixEnd_3350703 : Nat := 4983230072969 + 3 ^ 40 * 3350703 * 2
def baseEnd_3350703 : Nat := 1720521169462109092802903

theorem tailTrace_3350703 : CollatzResearch.WordTrace tailWord_3350703 prefixEnd_3350703 1720521169462109092802903 := by
  unfold tailWord_3350703
  simp only [CollatzResearch.WordTrace]
  refine ⟨122210178379982760358000763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81473452253321840238667175 122210178379982760358000763)
  ·
    refine ⟨183315267569974140537001145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122210178379982760358000763 183315267569974140537001145)
    ·
      refine ⟨137486450677480605402750859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183315267569974140537001145 137486450677480605402750859)
      ·
        refine ⟨206229676016220908104126289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137486450677480605402750859 206229676016220908104126289)
        ·
          refine ⟨154672257012165681078094717, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206229676016220908104126289 154672257012165681078094717)
          ·
            refine ⟨58002096379562130404285519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 154672257012165681078094717 58002096379562130404285519)
            ·
              refine ⟨87003144569343195606428279, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58002096379562130404285519 87003144569343195606428279)
              ·
                refine ⟨130504716854014793409642419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87003144569343195606428279 130504716854014793409642419)
                ·
                  refine ⟨195757075281022190114463629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 130504716854014793409642419 195757075281022190114463629)
                  ·
                    refine ⟨73408903230383321292923861, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 195757075281022190114463629 73408903230383321292923861)
                    ·
                      refine ⟨1720521169462109092802903, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 73408903230383321292923861 1720521169462109092802903)
                      ·
                        rfl

theorem cell23_3350703_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 1, 1, 1, 3, 7].length) (baseStart_3350703 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350703 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350703 prefixEnd_3350703 := by exact prefixLift 3350703
  have htrace : WordTrace (prefixWord ++ tailWord_3350703) baseStart_3350703 baseEnd_3350703 := by
    simpa [prefixWord, tailWord_3350703, baseEnd_3350703] using wordTrace_append hprefix tailTrace_3350703
  have hstable : (prefixWord ++ tailWord_3350703).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350703).length < 2 ^ (prefixWord ++ tailWord_3350703).sum := by decide
  have hdescent : baseEnd_3350703 < baseStart_3350703 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350703) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350723 : List Nat := [1, 1, 1, 3, 1, 1, 1, 2, 2, 10]
def baseStart_3350723 : Nat := 118140960795 + 3350723 * 2 ^ 59
def prefixEnd_3350723 : Nat := 4983230072969 + 3 ^ 40 * 3350723 * 2
def baseEnd_3350723 : Nat := 573510479691733004850937

theorem tailTrace_3350723 : CollatzResearch.WordTrace tailWord_3350723 prefixEnd_3350723 573510479691733004850937 := by
  unfold tailWord_3350723
  simp only [CollatzResearch.WordTrace]
  refine ⟨122210907839910303773728823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81473938559940202515819215 122210907839910303773728823)
  ·
    refine ⟨183316361759865455660593235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122210907839910303773728823 183316361759865455660593235)
    ·
      refine ⟨274974542639798183490889853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183316361759865455660593235 274974542639798183490889853)
      ·
        refine ⟨103115453489924318809083695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 274974542639798183490889853 103115453489924318809083695)
        ·
          refine ⟨154673180234886478213625543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103115453489924318809083695 154673180234886478213625543)
          ·
            refine ⟨232009770352329717320438315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154673180234886478213625543 232009770352329717320438315)
            ·
              refine ⟨348014655528494575980657473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 232009770352329717320438315 348014655528494575980657473)
              ·
                refine ⟨261010991646370931985493105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 348014655528494575980657473 261010991646370931985493105)
                ·
                  refine ⟨195758243734778198989119829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 261010991646370931985493105 195758243734778198989119829)
                  ·
                    refine ⟨573510479691733004850937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 10 195758243734778198989119829 573510479691733004850937)
                    ·
                      rfl

theorem cell23_3350723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 1, 1, 2, 2, 10].length) (baseStart_3350723 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350723 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350723 prefixEnd_3350723 := by exact prefixLift 3350723
  have htrace : WordTrace (prefixWord ++ tailWord_3350723) baseStart_3350723 baseEnd_3350723 := by
    simpa [prefixWord, tailWord_3350723, baseEnd_3350723] using wordTrace_append hprefix tailTrace_3350723
  have hstable : (prefixWord ++ tailWord_3350723).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350723).length < 2 ^ (prefixWord ++ tailWord_3350723).sum := by decide
  have hdescent : baseEnd_3350723 < baseStart_3350723 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350741 : List Nat := [1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 3]
def baseStart_3350741 : Nat := 118140960795 + 3350741 * 2 ^ 59
def prefixEnd_3350741 : Nat := 4983230072969 + 3 ^ 40 * 3350741 * 2
def baseEnd_3350741 : Nat := 1720540681726979944127729

theorem tailTrace_3350741 : CollatzResearch.WordTrace tailWord_3350741 prefixEnd_3350741 1720540681726979944127729 := by
  unfold tailWord_3350741
  simp only [CollatzResearch.WordTrace]
  refine ⟨122211564353845092847884077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81474376235896728565256051 122211564353845092847884077)
  ·
    refine ⟨45829336632691909817956529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122211564353845092847884077 45829336632691909817956529)
    ·
      refine ⟨34372002474518932363467397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45829336632691909817956529 34372002474518932363467397)
      ·
        refine ⟨6444750463972299818150137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 34372002474518932363467397 6444750463972299818150137)
        ·
          refine ⟨4833562847979224863612603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6444750463972299818150137 4833562847979224863612603)
          ·
            refine ⟨7250344271968837295418905, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833562847979224863612603 7250344271968837295418905)
            ·
              refine ⟨5437758203976627971564179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7250344271968837295418905 5437758203976627971564179)
              ·
                refine ⟨8156637305964941957346269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437758203976627971564179 8156637305964941957346269)
                ·
                  refine ⟨3058738989736853234004851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8156637305964941957346269 3058738989736853234004851)
                  ·
                    refine ⟨4588108484605279851007277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3058738989736853234004851 4588108484605279851007277)
                    ·
                      refine ⟨1720540681726979944127729, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4588108484605279851007277 1720540681726979944127729)
                      ·
                        rfl

theorem cell23_3350741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 2, 1, 2, 1, 3, 1, 3].length) (baseStart_3350741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350741 prefixEnd_3350741 := by exact prefixLift 3350741
  have htrace : WordTrace (prefixWord ++ tailWord_3350741) baseStart_3350741 baseEnd_3350741 := by
    simpa [prefixWord, tailWord_3350741, baseEnd_3350741] using wordTrace_append hprefix tailTrace_3350741
  have hstable : (prefixWord ++ tailWord_3350741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350741).length < 2 ^ (prefixWord ++ tailWord_3350741).sum := by decide
  have hdescent : baseEnd_3350741 < baseStart_3350741 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350757 : List Nat := [1, 3, 1, 4, 2, 1, 3, 1, 1, 6]
def baseStart_3350757 : Nat := 118140960795 + 3350757 * 2 ^ 59
def prefixEnd_3350757 : Nat := 4983230072969 + 3 ^ 40 * 3350757 * 2
def baseEnd_3350757 : Nat := 573516299139150627175885

theorem tailTrace_3350757 : CollatzResearch.WordTrace tailWord_3350757 prefixEnd_3350757 573516299139150627175885 := by
  unfold tailWord_3350757
  simp only [CollatzResearch.WordTrace]
  refine ⟨122212147921787127580466525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81474765281191418386977683 122212147921787127580466525)
  ·
    refine ⟨45829555470670172842674947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122212147921787127580466525 45829555470670172842674947)
    ·
      refine ⟨68744333206005259264012421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45829555470670172842674947 68744333206005259264012421)
      ·
        refine ⟨12889562476125986112002329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 68744333206005259264012421 12889562476125986112002329)
        ·
          refine ⟨9667171857094489584001747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12889562476125986112002329 9667171857094489584001747)
          ·
            refine ⟨14500757785641734376002621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9667171857094489584001747 14500757785641734376002621)
            ·
              refine ⟨5437784169615650391000983, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14500757785641734376002621 5437784169615650391000983)
              ·
                refine ⟨8156676254423475586501475, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5437784169615650391000983 8156676254423475586501475)
                ·
                  refine ⟨12235014381635213379752213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8156676254423475586501475 12235014381635213379752213)
                  ·
                    refine ⟨573516299139150627175885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12235014381635213379752213 573516299139150627175885)
                    ·
                      rfl

theorem cell23_3350757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 2, 1, 3, 1, 1, 6].length) (baseStart_3350757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350757 prefixEnd_3350757 := by exact prefixLift 3350757
  have htrace : WordTrace (prefixWord ++ tailWord_3350757) baseStart_3350757 baseEnd_3350757 := by
    simpa [prefixWord, tailWord_3350757, baseEnd_3350757] using wordTrace_append hprefix tailTrace_3350757
  have hstable : (prefixWord ++ tailWord_3350757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350757).length < 2 ^ (prefixWord ++ tailWord_3350757).sum := by decide
  have hdescent : baseEnd_3350757 < baseStart_3350757 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350764 : List Nat := [2, 2, 1, 1, 2, 3, 1, 4, 3, 2, 2]
def baseStart_3350764 : Nat := 118140960795 + 3350764 * 2 ^ 59
def prefixEnd_3350764 : Nat := 4983230072969 + 3 ^ 40 * 3350764 * 2
def baseEnd_3350764 : Nat := 1720552491782033354140123

theorem tailTrace_3350764 : CollatzResearch.WordTrace tailWord_3350764 prefixEnd_3350764 1720552491782033354140123 := by
  unfold tailWord_3350764
  simp only [CollatzResearch.WordTrace]
  refine ⟨61106201616380883887985673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81474935488507845183980897 61106201616380883887985673)
  ·
    refine ⟨45829651212285662915989255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61106201616380883887985673 45829651212285662915989255)
    ·
      refine ⟨68744476818428494373983883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45829651212285662915989255 68744476818428494373983883)
      ·
        refine ⟨103116715227642741560975825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68744476818428494373983883 103116715227642741560975825)
        ·
          refine ⟨77337536420732056170731869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103116715227642741560975825 77337536420732056170731869)
          ·
            refine ⟨29001576157774521064024451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77337536420732056170731869 29001576157774521064024451)
            ·
              refine ⟨43502364236661781596036677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29001576157774521064024451 43502364236661781596036677)
              ·
                refine ⟨8156693294374084049256877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43502364236661781596036677 8156693294374084049256877)
                ·
                  refine ⟨3058759985390281518471329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8156693294374084049256877 3058759985390281518471329)
                  ·
                    refine ⟨2294069989042711138853497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058759985390281518471329 2294069989042711138853497)
                    ·
                      refine ⟨1720552491782033354140123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294069989042711138853497 1720552491782033354140123)
                      ·
                        rfl

theorem cell23_3350764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 4, 3, 2, 2].length) (baseStart_3350764 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350764 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350764 prefixEnd_3350764 := by exact prefixLift 3350764
  have htrace : WordTrace (prefixWord ++ tailWord_3350764) baseStart_3350764 baseEnd_3350764 := by
    simpa [prefixWord, tailWord_3350764, baseEnd_3350764] using wordTrace_append hprefix tailTrace_3350764
  have hstable : (prefixWord ++ tailWord_3350764).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350764).length < 2 ^ (prefixWord ++ tailWord_3350764).sum := by decide
  have hdescent : baseEnd_3350764 < baseStart_3350764 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350849 : List Nat := [1, 2, 5, 2, 3, 1, 2, 2, 1, 2, 2]
def baseStart_3350849 : Nat := 118140960795 + 3350849 * 2 ^ 59
def prefixEnd_3350849 : Nat := 4983230072969 + 3 ^ 40 * 3350849 * 2
def baseEnd_3350849 : Nat := 1720596137637665521577233

theorem tailTrace_3350849 : CollatzResearch.WordTrace tailWord_3350849 prefixEnd_3350849 1720596137637665521577233 := by
  unfold tailWord_3350849
  simp only [CollatzResearch.WordTrace]
  refine ⟨122215503437453827292815601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81477002291635884861877067 122215503437453827292815601)
  ·
    refine ⟨91661627578090370469611701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122215503437453827292815601 91661627578090370469611701)
    ·
      refine ⟨8593277585445972231526097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 91661627578090370469611701 8593277585445972231526097)
      ·
        refine ⟨6444958189084479173644573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8593277585445972231526097 6444958189084479173644573)
        ·
          refine ⟨2416859320906679690116715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6444958189084479173644573 2416859320906679690116715)
          ·
            refine ⟨3625288981360019535175073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416859320906679690116715 3625288981360019535175073)
            ·
              refine ⟨2718966736020014651381305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625288981360019535175073 2718966736020014651381305)
              ·
                refine ⟨2039225052015010988535979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2718966736020014651381305 2039225052015010988535979)
                ·
                  refine ⟨3058837578022516482803969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039225052015010988535979 3058837578022516482803969)
                  ·
                    refine ⟨2294128183516887362102977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058837578022516482803969 2294128183516887362102977)
                    ·
                      refine ⟨1720596137637665521577233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294128183516887362102977 1720596137637665521577233)
                      ·
                        rfl

theorem cell23_3350849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2, 1, 2, 2].length) (baseStart_3350849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350849 prefixEnd_3350849 := by exact prefixLift 3350849
  have htrace : WordTrace (prefixWord ++ tailWord_3350849) baseStart_3350849 baseEnd_3350849 := by
    simpa [prefixWord, tailWord_3350849, baseEnd_3350849] using wordTrace_append hprefix tailTrace_3350849
  have hstable : (prefixWord ++ tailWord_3350849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350849).length < 2 ^ (prefixWord ++ tailWord_3350849).sum := by decide
  have hdescent : baseEnd_3350849 < baseStart_3350849 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350871 : List Nat := [1, 1, 3, 2, 3, 1, 1, 5, 2, 2, 2]
def baseStart_3350871 : Nat := 118140960795 + 3350871 * 2 ^ 59
def prefixEnd_3350871 : Nat := 4983230072969 + 3 ^ 40 * 3350871 * 2
def baseEnd_3350871 : Nat := 1720607434212064435502131

theorem tailTrace_3350871 : CollatzResearch.WordTrace tailWord_3350871 prefixEnd_3350871 1720607434212064435502131 := by
  unfold tailWord_3350871
  simp only [CollatzResearch.WordTrace]
  refine ⟨122216305843374125050116467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81477537228916083366744311 122216305843374125050116467)
  ·
    refine ⟨183324458765061187575174701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122216305843374125050116467 183324458765061187575174701)
    ·
      refine ⟨68746672036897945340690513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183324458765061187575174701 68746672036897945340690513)
      ·
        refine ⟨51560004027673459005517885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68746672036897945340690513 51560004027673459005517885)
        ·
          refine ⟨19335001510377547127069207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51560004027673459005517885 19335001510377547127069207)
          ·
            refine ⟨29002502265566320690603811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335001510377547127069207 29002502265566320690603811)
            ·
              refine ⟨43503753398349481035905717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29002502265566320690603811 43503753398349481035905717)
              ·
                refine ⟨4078476881095263847116161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 43503753398349481035905717 4078476881095263847116161)
                ·
                  refine ⟨3058857660821447885337121, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4078476881095263847116161 3058857660821447885337121)
                  ·
                    refine ⟨2294143245616085914002841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058857660821447885337121 2294143245616085914002841)
                    ·
                      refine ⟨1720607434212064435502131, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294143245616085914002841 1720607434212064435502131)
                      ·
                        rfl

theorem cell23_3350871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 5, 2, 2, 2].length) (baseStart_3350871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350871 prefixEnd_3350871 := by exact prefixLift 3350871
  have htrace : WordTrace (prefixWord ++ tailWord_3350871) baseStart_3350871 baseEnd_3350871 := by
    simpa [prefixWord, tailWord_3350871, baseEnd_3350871] using wordTrace_append hprefix tailTrace_3350871
  have hstable : (prefixWord ++ tailWord_3350871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350871).length < 2 ^ (prefixWord ++ tailWord_3350871).sum := by decide
  have hdescent : baseEnd_3350871 < baseStart_3350871 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350922 : List Nat := [3, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2]
def baseStart_3350922 : Nat := 118140960795 + 3350922 * 2 ^ 59
def prefixEnd_3350922 : Nat := 4983230072969 + 3 ^ 40 * 3350922 * 2
def baseEnd_3350922 : Nat := 1720633621725443735964397

theorem tailTrace_3350922 : CollatzResearch.WordTrace tailWord_3350922 prefixEnd_3350922 1720633621725443735964397 := by
  unfold tailWord_3350922
  simp only [CollatzResearch.WordTrace]
  refine ⟨30554541491547340190055755, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81478777310792907173482013 30554541491547340190055755)
  ·
    refine ⟨45831812237321010285083633, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30554541491547340190055755 45831812237321010285083633)
    ·
      refine ⟨34373859177990757713812725, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45831812237321010285083633 34373859177990757713812725)
      ·
        refine ⟨3222549297936633535669943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34373859177990757713812725 3222549297936633535669943)
        ·
          refine ⟨4833823946904950303504915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 3222549297936633535669943 4833823946904950303504915)
          ·
            refine ⟨7250735920357425455257373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4833823946904950303504915 7250735920357425455257373)
            ·
              refine ⟨2719025970134034545721515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 7250735920357425455257373 2719025970134034545721515)
              ·
                refine ⟨4078538955201051818582273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719025970134034545721515 4078538955201051818582273)
                ·
                  refine ⟨3058904216400788863936705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4078538955201051818582273 3058904216400788863936705)
                  ·
                    refine ⟨2294178162300591647952529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3058904216400788863936705 2294178162300591647952529)
                    ·
                      refine ⟨1720633621725443735964397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294178162300591647952529 1720633621725443735964397)
                      ·
                        rfl

theorem cell23_3350922_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 5, 1, 1, 3, 1, 2, 2, 2].length) (baseStart_3350922 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350922 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350922 prefixEnd_3350922 := by exact prefixLift 3350922
  have htrace : WordTrace (prefixWord ++ tailWord_3350922) baseStart_3350922 baseEnd_3350922 := by
    simpa [prefixWord, tailWord_3350922, baseEnd_3350922] using wordTrace_append hprefix tailTrace_3350922
  have hstable : (prefixWord ++ tailWord_3350922).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350922).length < 2 ^ (prefixWord ++ tailWord_3350922).sum := by decide
  have hdescent : baseEnd_3350922 < baseStart_3350922 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350922) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350945 : List Nat := [1, 2, 3, 5, 2, 1, 1, 3, 5]
def baseStart_3350945 : Nat := 118140960795 + 3350945 * 2 ^ 59
def prefixEnd_3350945 : Nat := 4983230072969 + 3 ^ 40 * 3350945 * 2
def baseEnd_3350945 : Nat := 191182825753388571775199

theorem tailTrace_3350945 : CollatzResearch.WordTrace tailWord_3350945 prefixEnd_3350945 191182825753388571775199 := by
  unfold tailWord_3350945
  simp only [CollatzResearch.WordTrace]
  refine ⟨122219004845106035688310289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81479336563404023792206859 122219004845106035688310289)
  ·
    refine ⟨91664253633829526766232717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122219004845106035688310289 91664253633829526766232717)
    ·
      refine ⟨34374095112686072537337269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91664253633829526766232717 34374095112686072537337269)
      ·
        refine ⟨3222571416814319300375369, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 34374095112686072537337269 3222571416814319300375369)
        ·
          refine ⟨2416928562610739475281527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 3222571416814319300375369 2416928562610739475281527)
          ·
            refine ⟨3625392843916109212922291, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2416928562610739475281527 3625392843916109212922291)
            ·
              refine ⟨5438089265874163819383437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625392843916109212922291 5438089265874163819383437)
              ·
                refine ⟨2039283474702811432268789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5438089265874163819383437 2039283474702811432268789)
                ·
                  refine ⟨191182825753388571775199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039283474702811432268789 191182825753388571775199)
                  ·
                    rfl

theorem cell23_3350945_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 5, 2, 1, 1, 3, 5].length) (baseStart_3350945 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350945 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350945 prefixEnd_3350945 := by exact prefixLift 3350945
  have htrace : WordTrace (prefixWord ++ tailWord_3350945) baseStart_3350945 baseEnd_3350945 := by
    simpa [prefixWord, tailWord_3350945, baseEnd_3350945] using wordTrace_append hprefix tailTrace_3350945
  have hstable : (prefixWord ++ tailWord_3350945).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350945).length < 2 ^ (prefixWord ++ tailWord_3350945).sum := by decide
  have hdescent : baseEnd_3350945 < baseStart_3350945 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350945) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350967 : List Nat := [1, 1, 3, 1, 3, 3, 2, 1, 8]
def baseStart_3350967 : Nat := 118140960795 + 3350967 * 2 ^ 59
def prefixEnd_3350967 : Nat := 4983230072969 + 3 ^ 40 * 3350967 * 2
def baseEnd_3350967 : Nat := 191184080928321784433521

theorem tailTrace_3350967 : CollatzResearch.WordTrace tailWord_3350967 prefixEnd_3350967 191184080928321784433521 := by
  unfold tailWord_3350967
  simp only [CollatzResearch.WordTrace]
  refine ⟨122219807251026333445611155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81479871500684222297074103 122219807251026333445611155)
  ·
    refine ⟨183329710876539500168416733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122219807251026333445611155 183329710876539500168416733)
    ·
      refine ⟨68748641578702312563156275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183329710876539500168416733 68748641578702312563156275)
      ·
        refine ⟨103122962368053468844734413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68748641578702312563156275 103122962368053468844734413)
        ·
          refine ⟨38671110888020050816775405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 103122962368053468844734413 38671110888020050816775405)
          ·
            refine ⟨14501666583007519056290777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38671110888020050816775405 14501666583007519056290777)
            ·
              refine ⟨10876249937255639292218083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14501666583007519056290777 10876249937255639292218083)
              ·
                refine ⟨16314374905883458938327125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10876249937255639292218083 16314374905883458938327125)
                ·
                  refine ⟨191184080928321784433521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 16314374905883458938327125 191184080928321784433521)
                  ·
                    rfl

theorem cell23_3350967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 3, 2, 1, 8].length) (baseStart_3350967 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350967 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350967 prefixEnd_3350967 := by exact prefixLift 3350967
  have htrace : WordTrace (prefixWord ++ tailWord_3350967) baseStart_3350967 baseEnd_3350967 := by
    simpa [prefixWord, tailWord_3350967, baseEnd_3350967] using wordTrace_append hprefix tailTrace_3350967
  have hstable : (prefixWord ++ tailWord_3350967).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350967).length < 2 ^ (prefixWord ++ tailWord_3350967).sum := by decide
  have hdescent : baseEnd_3350967 < baseStart_3350967 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350984 : List Nat := [2, 1, 3, 1, 3, 3, 1, 3, 6]
def baseStart_3350984 : Nat := 118140960795 + 3350984 * 2 ^ 59
def prefixEnd_3350984 : Nat := 4983230072969 + 3 ^ 40 * 3350984 * 2
def baseEnd_3350984 : Nat := 191185050836224721487679

theorem tailTrace_3350984 : CollatzResearch.WordTrace tailWord_3350984 prefixEnd_3350984 191185050836224721487679 := by
  unfold tailWord_3350984
  simp only [CollatzResearch.WordTrace]
  refine ⟨61110213645982372674490003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81480284861309830232653337 61110213645982372674490003)
  ·
    refine ⟨91665320468973559011735005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61110213645982372674490003 91665320468973559011735005)
    ·
      refine ⟨34374495175865084629400627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 91665320468973559011735005 34374495175865084629400627)
      ·
        refine ⟨51561742763797626944100941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34374495175865084629400627 51561742763797626944100941)
        ·
          refine ⟨19335653536424110104037853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51561742763797626944100941 19335653536424110104037853)
          ·
            refine ⟨7250870076159041289014195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19335653536424110104037853 7250870076159041289014195)
            ·
              refine ⟨10876305114238561933521293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7250870076159041289014195 10876305114238561933521293)
              ·
                refine ⟨4078614417839460725070485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10876305114238561933521293 4078614417839460725070485)
                ·
                  refine ⟨191185050836224721487679, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4078614417839460725070485 191185050836224721487679)
                  ·
                    rfl

theorem cell23_3350984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 3, 1, 3, 6].length) (baseStart_3350984 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350984 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350984 prefixEnd_3350984 := by exact prefixLift 3350984
  have htrace : WordTrace (prefixWord ++ tailWord_3350984) baseStart_3350984 baseEnd_3350984 := by
    simpa [prefixWord, tailWord_3350984, baseEnd_3350984] using wordTrace_append hprefix tailTrace_3350984
  have hstable : (prefixWord ++ tailWord_3350984).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350984).length < 2 ^ (prefixWord ++ tailWord_3350984).sum := by decide
  have hdescent : baseEnd_3350984 < baseStart_3350984 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3350998 : List Nat := [5, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3]
def baseStart_3350998 : Nat := 118140960795 + 3350998 * 2 ^ 59
def prefixEnd_3350998 : Nat := 4983230072969 + 3 ^ 40 * 3350998 * 2
def baseEnd_3350998 : Nat := 1720672646255185438614047

theorem tailTrace_3350998 : CollatzResearch.WordTrace tailWord_3350998 prefixEnd_3350998 1720672646255185438614047 := by
  unfold tailWord_3350998
  simp only [CollatzResearch.WordTrace]
  refine ⟨7638808619619626608749353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 81480625275942683826659765 7638808619619626608749353)
  ·
    refine ⟨5729106464714719956562015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7638808619619626608749353 5729106464714719956562015)
    ·
      refine ⟨8593659697072079934843023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5729106464714719956562015 8593659697072079934843023)
      ·
        refine ⟨12890489545608119902264535, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8593659697072079934843023 12890489545608119902264535)
        ·
          refine ⟨19335734318412179853396803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12890489545608119902264535 19335734318412179853396803)
          ·
            refine ⟨29003601477618269780095205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19335734318412179853396803 29003601477618269780095205)
            ·
              refine ⟨5438175277053425583767851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29003601477618269780095205 5438175277053425583767851)
              ·
                refine ⟨8157262915580138375651777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438175277053425583767851 8157262915580138375651777)
                ·
                  refine ⟨6117947186685103781738833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8157262915580138375651777 6117947186685103781738833)
                  ·
                    refine ⟨4588460390013827836304125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6117947186685103781738833 4588460390013827836304125)
                    ·
                      refine ⟨1720672646255185438614047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4588460390013827836304125 1720672646255185438614047)
                      ·
                        rfl

theorem cell23_3350998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 1, 4, 1, 2, 2, 3].length) (baseStart_3350998 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3350998 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3350998 prefixEnd_3350998 := by exact prefixLift 3350998
  have htrace : WordTrace (prefixWord ++ tailWord_3350998) baseStart_3350998 baseEnd_3350998 := by
    simpa [prefixWord, tailWord_3350998, baseEnd_3350998] using wordTrace_append hprefix tailTrace_3350998
  have hstable : (prefixWord ++ tailWord_3350998).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3350998).length < 2 ^ (prefixWord ++ tailWord_3350998).sum := by decide
  have hdescent : baseEnd_3350998 < baseStart_3350998 := by decide
  rcases family_descends (prefixWord ++ tailWord_3350998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351027 : List Nat := [1, 1, 1, 2, 2, 2, 3, 2, 3, 6]
def baseStart_3351027 : Nat := 118140960795 + 3351027 * 2 ^ 59
def prefixEnd_3351027 : Nat := 4983230072969 + 3 ^ 40 * 3351027 * 2
def baseEnd_3351027 : Nat := 573562512398055275050471

theorem tailTrace_3351027 : CollatzResearch.WordTrace tailWord_3351027 prefixEnd_3351027 573562512398055275050471 := by
  unfold tailWord_3351027
  simp only [CollatzResearch.WordTrace]
  refine ⟨122221995630808963692795335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81481330420539309128530223 122221995630808963692795335)
  ·
    refine ⟨183332993446213445539193003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122221995630808963692795335 183332993446213445539193003)
    ·
      refine ⟨274999490169320168308789505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183332993446213445539193003 274999490169320168308789505)
      ·
        refine ⟨206249617626990126231592129, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 274999490169320168308789505 206249617626990126231592129)
        ·
          refine ⟨154687213220242594673694097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 206249617626990126231592129 154687213220242594673694097)
          ·
            refine ⟨116015409915181946005270573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154687213220242594673694097 116015409915181946005270573)
            ·
              refine ⟨43505778718193229751976465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 116015409915181946005270573 43505778718193229751976465)
              ·
                refine ⟨32629334038644922313982349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43505778718193229751976465 32629334038644922313982349)
                ·
                  refine ⟨12236000264491845867743381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32629334038644922313982349 12236000264491845867743381)
                  ·
                    refine ⟨573562512398055275050471, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12236000264491845867743381 573562512398055275050471)
                    ·
                      rfl

theorem cell23_3351027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 3, 2, 3, 6].length) (baseStart_3351027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351027 prefixEnd_3351027 := by exact prefixLift 3351027
  have htrace : WordTrace (prefixWord ++ tailWord_3351027) baseStart_3351027 baseEnd_3351027 := by
    simpa [prefixWord, tailWord_3351027, baseEnd_3351027] using wordTrace_append hprefix tailTrace_3351027
  have hstable : (prefixWord ++ tailWord_3351027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351027).length < 2 ^ (prefixWord ++ tailWord_3351027).sum := by decide
  have hdescent : baseEnd_3351027 < baseStart_3351027 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351068 : List Nat := [2, 2, 3, 1, 2, 2, 4, 1, 1, 1, 4]
def baseStart_3351068 : Nat := 118140960795 + 3351068 * 2 ^ 59
def prefixEnd_3351068 : Nat := 4983230072969 + 3 ^ 40 * 3351068 * 2
def baseEnd_3351068 : Nat := 1720708589901000164738725

theorem tailTrace_3351068 : CollatzResearch.WordTrace tailWord_3351068 prefixEnd_3351068 1720708589901000164738725 := by
  unfold tailWord_3351068
  simp only [CollatzResearch.WordTrace]
  refine ⟨61111745511830213847518929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81482327349106951796691905 61111745511830213847518929)
  ·
    refine ⟨45833809133872660385639197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61111745511830213847518929 45833809133872660385639197)
    ·
      refine ⟨17187678425202247644614699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 45833809133872660385639197 17187678425202247644614699)
      ·
        refine ⟨25781517637803371466922049, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17187678425202247644614699 25781517637803371466922049)
        ·
          refine ⟨19336138228352528600191537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25781517637803371466922049 19336138228352528600191537)
          ·
            refine ⟨14502103671264396450143653, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19336138228352528600191537 14502103671264396450143653)
            ·
              refine ⟨2719144438362074334401935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 14502103671264396450143653 2719144438362074334401935)
              ·
                refine ⟨4078716657543111501602903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719144438362074334401935 4078716657543111501602903)
                ·
                  refine ⟨6118074986314667252404355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078716657543111501602903 6118074986314667252404355)
                  ·
                    refine ⟨9177112479472000878606533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118074986314667252404355 9177112479472000878606533)
                    ·
                      refine ⟨1720708589901000164738725, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9177112479472000878606533 1720708589901000164738725)
                      ·
                        rfl

theorem cell23_3351068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 2, 4, 1, 1, 1, 4].length) (baseStart_3351068 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351068 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351068 prefixEnd_3351068 := by exact prefixLift 3351068
  have htrace : WordTrace (prefixWord ++ tailWord_3351068) baseStart_3351068 baseEnd_3351068 := by
    simpa [prefixWord, tailWord_3351068, baseEnd_3351068] using wordTrace_append hprefix tailTrace_3351068
  have hstable : (prefixWord ++ tailWord_3351068).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351068).length < 2 ^ (prefixWord ++ tailWord_3351068).sum := by decide
  have hdescent : baseEnd_3351068 < baseStart_3351068 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351084 : List Nat := [2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 3]
def baseStart_3351084 : Nat := 118140960795 + 3351084 * 2 ^ 59
def prefixEnd_3351084 : Nat := 4983230072969 + 3 ^ 40 * 3351084 * 2
def baseEnd_3351084 : Nat := 1720716805591472102138651

theorem tailTrace_3351084 : CollatzResearch.WordTrace tailWord_3351084 prefixEnd_3351084 1720716805591472102138651 := by
  unfold tailWord_3351084
  simp only [CollatzResearch.WordTrace]
  refine ⟨61112037295801231213810153, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81482716394401641618413537 61112037295801231213810153)
  ·
    refine ⟨45834027971850923410357615, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61112037295801231213810153 45834027971850923410357615)
    ·
      refine ⟨68751041957776385115536423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45834027971850923410357615 68751041957776385115536423)
      ·
        refine ⟨103126562936664577673304635, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68751041957776385115536423 103126562936664577673304635)
        ·
          refine ⟨154689844404996866509956953, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103126562936664577673304635 154689844404996866509956953)
          ·
            refine ⟨116017383303747649882467715, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 154689844404996866509956953 116017383303747649882467715)
            ·
              refine ⟨174026074955621474823701573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116017383303747649882467715 174026074955621474823701573)
              ·
                refine ⟨32629889054179026529444045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 174026074955621474823701573 32629889054179026529444045)
                ·
                  refine ⟨12236208395317134948541517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 32629889054179026529444045 12236208395317134948541517)
                  ·
                    refine ⟨4588578148243925605703069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12236208395317134948541517 4588578148243925605703069)
                    ·
                      refine ⟨1720716805591472102138651, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4588578148243925605703069 1720716805591472102138651)
                      ·
                        rfl

theorem cell23_3351084_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 3, 3, 3].length) (baseStart_3351084 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351084 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351084 prefixEnd_3351084 := by exact prefixLift 3351084
  have htrace : WordTrace (prefixWord ++ tailWord_3351084) baseStart_3351084 baseEnd_3351084 := by
    simpa [prefixWord, tailWord_3351084, baseEnd_3351084] using wordTrace_append hprefix tailTrace_3351084
  have hstable : (prefixWord ++ tailWord_3351084).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351084).length < 2 ^ (prefixWord ++ tailWord_3351084).sum := by decide
  have hdescent : baseEnd_3351084 < baseStart_3351084 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351084) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351114 : List Nat := [3, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5]
def baseStart_3351114 : Nat := 118140960795 + 3351114 * 2 ^ 59
def prefixEnd_3351114 : Nat := 4983230072969 + 3 ^ 40 * 3351114 * 2
def baseEnd_3351114 : Nat := 1720732210011106984763513

theorem tailTrace_3351114 : CollatzResearch.WordTrace tailWord_3351114 prefixEnd_3351114 1720732210011106984763513 := by
  unfold tailWord_3351114
  simp only [CollatzResearch.WordTrace]
  refine ⟨30556292195373444387803099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81483445854329185034141597 30556292195373444387803099)
  ·
    refine ⟨45834438293060166581704649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30556292195373444387803099 45834438293060166581704649)
    ·
      refine ⟨34375828719795124936278487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45834438293060166581704649 34375828719795124936278487)
      ·
        refine ⟨51563743079692687404417731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34375828719795124936278487 51563743079692687404417731)
        ·
          refine ⟨77345614619539031106626597, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51563743079692687404417731 77345614619539031106626597)
          ·
            refine ⟨14502302741163568332492487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 77345614619539031106626597 14502302741163568332492487)
            ·
              refine ⟨21753454111745352498738731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14502302741163568332492487 21753454111745352498738731)
              ·
                refine ⟨32630181167618028748108097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 21753454111745352498738731 32630181167618028748108097)
                ·
                  refine ⟨24472635875713521561081073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32630181167618028748108097 24472635875713521561081073)
                  ·
                    refine ⟨18354476906785141170810805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24472635875713521561081073 18354476906785141170810805)
                    ·
                      refine ⟨1720732210011106984763513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18354476906785141170810805 1720732210011106984763513)
                      ·
                        rfl

theorem cell23_3351114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 4, 1, 1, 2, 2, 5].length) (baseStart_3351114 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351114 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351114 prefixEnd_3351114 := by exact prefixLift 3351114
  have htrace : WordTrace (prefixWord ++ tailWord_3351114) baseStart_3351114 baseEnd_3351114 := by
    simpa [prefixWord, tailWord_3351114, baseEnd_3351114] using wordTrace_append hprefix tailTrace_3351114
  have hstable : (prefixWord ++ tailWord_3351114).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351114).length < 2 ^ (prefixWord ++ tailWord_3351114).sum := by decide
  have hdescent : baseEnd_3351114 < baseStart_3351114 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351128 : List Nat := [2, 1, 2, 2, 1, 2, 4, 3, 1, 3, 2]
def baseStart_3351128 : Nat := 118140960795 + 3351128 * 2 ^ 59
def prefixEnd_3351128 : Nat := 4983230072969 + 3 ^ 40 * 3351128 * 2
def baseEnd_3351128 : Nat := 1720739398740269929988449

theorem tailTrace_3351128 : CollatzResearch.WordTrace tailWord_3351128 prefixEnd_3351128 1720739398740269929988449 := by
  unfold tailWord_3351128
  simp only [CollatzResearch.WordTrace]
  refine ⟨61112839701721528971111019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81483786268962038628148025 61112839701721528971111019)
  ·
    refine ⟨91669259552582293456666529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61112839701721528971111019 91669259552582293456666529)
    ·
      refine ⟨68751944664436720092499897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91669259552582293456666529 68751944664436720092499897)
      ·
        refine ⟨51563958498327540069374923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68751944664436720092499897 51563958498327540069374923)
        ·
          refine ⟨77345937747491310104062385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51563958498327540069374923 77345937747491310104062385)
          ·
            refine ⟨58009453310618482578046789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77345937747491310104062385 58009453310618482578046789)
            ·
              refine ⟨10876772495740965483383773, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 58009453310618482578046789 10876772495740965483383773)
              ·
                refine ⟨4078789685902862056268915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 10876772495740965483383773 4078789685902862056268915)
                ·
                  refine ⟨6118184528854293084403373, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4078789685902862056268915 6118184528854293084403373)
                  ·
                    refine ⟨2294319198320359906651265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6118184528854293084403373 2294319198320359906651265)
                    ·
                      refine ⟨1720739398740269929988449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294319198320359906651265 1720739398740269929988449)
                      ·
                        rfl

theorem cell23_3351128_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 2, 4, 3, 1, 3, 2].length) (baseStart_3351128 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351128 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351128 prefixEnd_3351128 := by exact prefixLift 3351128
  have htrace : WordTrace (prefixWord ++ tailWord_3351128) baseStart_3351128 baseEnd_3351128 := by
    simpa [prefixWord, tailWord_3351128, baseEnd_3351128] using wordTrace_append hprefix tailTrace_3351128
  have hstable : (prefixWord ++ tailWord_3351128).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351128).length < 2 ^ (prefixWord ++ tailWord_3351128).sum := by decide
  have hdescent : baseEnd_3351128 < baseStart_3351128 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351128) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351152 : List Nat := [2, 1, 1, 1, 7, 2, 2, 1, 2, 1, 3]
def baseStart_3351152 : Nat := 118140960795 + 3351152 * 2 ^ 59
def prefixEnd_3351152 : Nat := 4983230072969 + 3 ^ 40 * 3351152 * 2
def baseEnd_3351152 : Nat := 1720751722275977836088339

theorem tailTrace_3351152 : CollatzResearch.WordTrace tailWord_3351152 prefixEnd_3351152 1720751722275977836088339 := by
  unfold tailWord_3351152
  simp only [CollatzResearch.WordTrace]
  refine ⟨61113277377678055020547855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81484369836904073360730473 61113277377678055020547855)
  ·
    refine ⟨91669916066517082530821783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61113277377678055020547855 91669916066517082530821783)
    ·
      refine ⟨137504874099775623796232675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91669916066517082530821783 137504874099775623796232675)
      ·
        refine ⟨206257311149663435694349013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137504874099775623796232675 206257311149663435694349013)
        ·
          refine ⟨4834155730070236774086305, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 206257311149663435694349013 4834155730070236774086305)
          ·
            refine ⟨3625616797552677580564729, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4834155730070236774086305 3625616797552677580564729)
            ·
              refine ⟨2719212598164508185423547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625616797552677580564729 2719212598164508185423547)
              ·
                refine ⟨4078818897246762278135321, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719212598164508185423547 4078818897246762278135321)
                ·
                  refine ⟨3059114172935071708601491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4078818897246762278135321 3059114172935071708601491)
                  ·
                    refine ⟨4588671259402607562902237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3059114172935071708601491 4588671259402607562902237)
                    ·
                      refine ⟨1720751722275977836088339, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4588671259402607562902237 1720751722275977836088339)
                      ·
                        rfl

theorem cell23_3351152_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 7, 2, 2, 1, 2, 1, 3].length) (baseStart_3351152 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351152 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351152 prefixEnd_3351152 := by exact prefixLift 3351152
  have htrace : WordTrace (prefixWord ++ tailWord_3351152) baseStart_3351152 baseEnd_3351152 := by
    simpa [prefixWord, tailWord_3351152, baseEnd_3351152] using wordTrace_append hprefix tailTrace_3351152
  have hstable : (prefixWord ++ tailWord_3351152).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351152).length < 2 ^ (prefixWord ++ tailWord_3351152).sum := by decide
  have hdescent : baseEnd_3351152 < baseStart_3351152 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351152) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351164 : List Nat := [2, 2, 2, 1, 1, 2, 2, 4, 7]
def baseStart_3351164 : Nat := 118140960795 + 3351164 * 2 ^ 59
def prefixEnd_3351164 : Nat := 4983230072969 + 3 ^ 40 * 3351164 * 2
def baseEnd_3351164 : Nat := 191195320449314643237587

theorem tailTrace_3351164 : CollatzResearch.WordTrace tailWord_3351164 prefixEnd_3351164 191195320449314643237587 := by
  unfold tailWord_3351164
  simp only [CollatzResearch.WordTrace]
  refine ⟨61113496215656318045266273, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81484661620875090727021697 61113496215656318045266273)
  ·
    refine ⟨45835122161742238533949705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61113496215656318045266273 45835122161742238533949705)
    ·
      refine ⟨34376341621306678900462279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45835122161742238533949705 34376341621306678900462279)
      ·
        refine ⟨51564512431960018350693419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34376341621306678900462279 51564512431960018350693419)
        ·
          refine ⟨77346768647940027526040129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51564512431960018350693419 77346768647940027526040129)
          ·
            refine ⟨58010076485955020644530097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 77346768647940027526040129 58010076485955020644530097)
            ·
              refine ⟨43507557364466265483397573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 58010076485955020644530097 43507557364466265483397573)
              ·
                refine ⟨8157667005837424778137045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 43507557364466265483397573 8157667005837424778137045)
                ·
                  refine ⟨191195320449314643237587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 8157667005837424778137045 191195320449314643237587)
                  ·
                    rfl

theorem cell23_3351164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 2, 4, 7].length) (baseStart_3351164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351164 prefixEnd_3351164 := by exact prefixLift 3351164
  have htrace : WordTrace (prefixWord ++ tailWord_3351164) baseStart_3351164 baseEnd_3351164 := by
    simpa [prefixWord, tailWord_3351164, baseEnd_3351164] using wordTrace_append hprefix tailTrace_3351164
  have hstable : (prefixWord ++ tailWord_3351164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351164).length < 2 ^ (prefixWord ++ tailWord_3351164).sum := by decide
  have hdescent : baseEnd_3351164 < baseStart_3351164 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351191 : List Nat := [1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 3]
def baseStart_3351191 : Nat := 118140960795 + 3351191 * 2 ^ 59
def prefixEnd_3351191 : Nat := 4983230072969 + 3 ^ 40 * 3351191 * 2
def baseEnd_3351191 : Nat := 1720771748021503183500659

theorem tailTrace_3351191 : CollatzResearch.WordTrace tailWord_3351191 prefixEnd_3351191 1720771748021503183500659 := by
  unfold tailWord_3351191
  simp only [CollatzResearch.WordTrace]
  refine ⟨122227977202214819701765427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81485318134809879801176951 122227977202214819701765427)
  ·
    refine ⟨183341965803322229552648141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122227977202214819701765427 183341965803322229552648141)
    ·
      refine ⟨68753237176245836082243053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 183341965803322229552648141 68753237176245836082243053)
      ·
        refine ⟨25782463941092188530841145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68753237176245836082243053 25782463941092188530841145)
        ·
          refine ⟨19336847955819141398130859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25782463941092188530841145 19336847955819141398130859)
          ·
            refine ⟨29005271933728712097196289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19336847955819141398130859 29005271933728712097196289)
            ·
              refine ⟨21753953950296534072897217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29005271933728712097196289 21753953950296534072897217)
              ·
                refine ⟨16315465462722400554672913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21753953950296534072897217 16315465462722400554672913)
                ·
                  refine ⟨12236599097041800416004685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16315465462722400554672913 12236599097041800416004685)
                  ·
                    refine ⟨4588724661390675156001757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12236599097041800416004685 4588724661390675156001757)
                    ·
                      refine ⟨1720771748021503183500659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4588724661390675156001757 1720771748021503183500659)
                      ·
                        rfl

theorem cell23_3351191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 1, 2, 2, 2, 3, 3].length) (baseStart_3351191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351191 prefixEnd_3351191 := by exact prefixLift 3351191
  have htrace : WordTrace (prefixWord ++ tailWord_3351191) baseStart_3351191 baseEnd_3351191 := by
    simpa [prefixWord, tailWord_3351191, baseEnd_3351191] using wordTrace_append hprefix tailTrace_3351191
  have hstable : (prefixWord ++ tailWord_3351191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351191).length < 2 ^ (prefixWord ++ tailWord_3351191).sum := by decide
  have hdescent : baseEnd_3351191 < baseStart_3351191 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351231 : List Nat := [1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 4]
def baseStart_3351231 : Nat := 118140960795 + 3351231 * 2 ^ 59
def prefixEnd_3351231 : Nat := 4983230072969 + 3 ^ 40 * 3351231 * 2
def baseEnd_3351231 : Nat := 1720792287247683027000475

theorem tailTrace_3351231 : CollatzResearch.WordTrace tailWord_3351231 prefixEnd_3351231 1720792287247683027000475 := by
  unfold tailWord_3351231
  simp only [CollatzResearch.WordTrace]
  refine ⟨122229436122069906533221547, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81486290748046604355481031 122229436122069906533221547)
  ·
    refine ⟨183344154183104859799832321, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122229436122069906533221547 183344154183104859799832321)
    ·
      refine ⟨137508115637328644849874241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183344154183104859799832321 137508115637328644849874241)
      ·
        refine ⟨103131086727996483637405681, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 137508115637328644849874241 103131086727996483637405681)
        ·
          refine ⟨77348315045997362728054261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 103131086727996483637405681 77348315045997362728054261)
          ·
            refine ⟨7251404535562252755755087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 77348315045997362728054261 7251404535562252755755087)
            ·
              refine ⟨10877106803343379133632631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7251404535562252755755087 10877106803343379133632631)
              ·
                refine ⟨16315660205015068700448947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10877106803343379133632631 16315660205015068700448947)
                ·
                  refine ⟨24473490307522603050673421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16315660205015068700448947 24473490307522603050673421)
                  ·
                    refine ⟨9177558865320976144002533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24473490307522603050673421 9177558865320976144002533)
                    ·
                      refine ⟨1720792287247683027000475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9177558865320976144002533 1720792287247683027000475)
                      ·
                        rfl

theorem cell23_3351231_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 5, 1, 1, 1, 3, 4].length) (baseStart_3351231 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351231 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351231 prefixEnd_3351231 := by exact prefixLift 3351231
  have htrace : WordTrace (prefixWord ++ tailWord_3351231) baseStart_3351231 baseEnd_3351231 := by
    simpa [prefixWord, tailWord_3351231, baseEnd_3351231] using wordTrace_append hprefix tailTrace_3351231
  have hstable : (prefixWord ++ tailWord_3351231).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351231).length < 2 ^ (prefixWord ++ tailWord_3351231).sum := by decide
  have hdescent : baseEnd_3351231 < baseStart_3351231 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351231) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351258 : List Nat := [3, 1, 1, 2, 2, 2, 4, 1, 3, 4]
def baseStart_3351258 : Nat := 118140960795 + 3351258 * 2 ^ 59
def prefixEnd_3351258 : Nat := 4983230072969 + 3 ^ 40 * 3351258 * 2
def baseEnd_3351258 : Nat := 573602050408451473787617

theorem tailTrace_3351258 : CollatzResearch.WordTrace tailWord_3351258 prefixEnd_3351258 573602050408451473787617 := by
  unfold tailWord_3351258
  simp only [CollatzResearch.WordTrace]
  refine ⟨30557605223243022536113607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81486947261981393429636285 30557605223243022536113607)
  ·
    refine ⟨45836407834864533804170411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30557605223243022536113607 45836407834864533804170411)
    ·
      refine ⟨68754611752296800706255617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45836407834864533804170411 68754611752296800706255617)
      ·
        refine ⟨51565958814222600529691713, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68754611752296800706255617 51565958814222600529691713)
        ·
          refine ⟨38674469110666950397268785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51565958814222600529691713 38674469110666950397268785)
          ·
            refine ⟨29005851833000212797951589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38674469110666950397268785 29005851833000212797951589)
            ·
              refine ⟨5438597218687539899615923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29005851833000212797951589 5438597218687539899615923)
              ·
                refine ⟨8157895828031309849423885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5438597218687539899615923 8157895828031309849423885)
                ·
                  refine ⟨3059210935511741193533957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8157895828031309849423885 3059210935511741193533957)
                  ·
                    refine ⟨573602050408451473787617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059210935511741193533957 573602050408451473787617)
                    ·
                      rfl

theorem cell23_3351258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 4, 1, 3, 4].length) (baseStart_3351258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351258 prefixEnd_3351258 := by exact prefixLift 3351258
  have htrace : WordTrace (prefixWord ++ tailWord_3351258) baseStart_3351258 baseEnd_3351258 := by
    simpa [prefixWord, tailWord_3351258, baseEnd_3351258] using wordTrace_append hprefix tailTrace_3351258
  have hstable : (prefixWord ++ tailWord_3351258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351258).length < 2 ^ (prefixWord ++ tailWord_3351258).sum := by decide
  have hdescent : baseEnd_3351258 < baseStart_3351258 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351281 : List Nat := [1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 3]
def baseStart_3351281 : Nat := 118140960795 + 3351281 * 2 ^ 59
def prefixEnd_3351281 : Nat := 4983230072969 + 3 ^ 40 * 3351281 * 2
def baseEnd_3351281 : Nat := 1720817961280407831375245

theorem tailTrace_3351281 : CollatzResearch.WordTrace tailWord_3351281 prefixEnd_3351281 1720817961280407831375245 := by
  unfold tailWord_3351281
  simp only [CollatzResearch.WordTrace]
  refine ⟨122231259771888765072541697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81487506514592510048361131 122231259771888765072541697)
  ·
    refine ⟨91673444828916573804406273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122231259771888765072541697 91673444828916573804406273)
    ·
      refine ⟨68755083621687430353304705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 91673444828916573804406273 68755083621687430353304705)
      ·
        refine ⟨51566312716265572764978529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68755083621687430353304705 51566312716265572764978529)
        ·
          refine ⟨38674734537199179573733897, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51566312716265572764978529 38674734537199179573733897)
          ·
            refine ⟨29006050902899384680300423, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38674734537199179573733897 29006050902899384680300423)
            ·
              refine ⟨43509076354349077020450635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29006050902899384680300423 43509076354349077020450635)
              ·
                refine ⟨65263614531523615530675953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43509076354349077020450635 65263614531523615530675953)
                ·
                  refine ⟨48947710898642711648006965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 65263614531523615530675953 48947710898642711648006965)
                  ·
                    refine ⟨4588847896747754217000653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 48947710898642711648006965 4588847896747754217000653)
                    ·
                      refine ⟨1720817961280407831375245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4588847896747754217000653 1720817961280407831375245)
                      ·
                        rfl

theorem cell23_3351281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 2, 2, 1, 1, 2, 5, 3].length) (baseStart_3351281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351281 prefixEnd_3351281 := by exact prefixLift 3351281
  have htrace : WordTrace (prefixWord ++ tailWord_3351281) baseStart_3351281 baseEnd_3351281 := by
    simpa [prefixWord, tailWord_3351281, baseEnd_3351281] using wordTrace_append hprefix tailTrace_3351281
  have hstable : (prefixWord ++ tailWord_3351281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351281).length < 2 ^ (prefixWord ++ tailWord_3351281).sum := by decide
  have hdescent : baseEnd_3351281 < baseStart_3351281 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351292 : List Nat := [2, 2, 2, 1, 3, 4, 1, 3, 1, 4]
def baseStart_3351292 : Nat := 118140960795 + 3351292 * 2 ^ 59
def prefixEnd_3351292 : Nat := 4983230072969 + 3 ^ 40 * 3351292 * 2
def baseEnd_3351292 : Nat := 573607869855869096112565

theorem tailTrace_3351292 : CollatzResearch.WordTrace tailWord_3351292 prefixEnd_3351292 573607869855869096112565 := by
  unfold tailWord_3351292
  simp only [CollatzResearch.WordTrace]
  refine ⟨61115830487424456975596065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81487773983232609300794753 61115830487424456975596065)
  ·
    refine ⟨45836872865568342731697049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61115830487424456975596065 45836872865568342731697049)
    ·
      refine ⟨34377654649176257048772787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45836872865568342731697049 34377654649176257048772787)
      ·
        refine ⟨51566481973764385573159181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34377654649176257048772787 51566481973764385573159181)
        ·
          refine ⟨19337430740161644589934693, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 51566481973764385573159181 19337430740161644589934693)
          ·
            refine ⟨3625768263780308360612755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 19337430740161644589934693 3625768263780308360612755)
            ·
              refine ⟨5438652395670462540919133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3625768263780308360612755 5438652395670462540919133)
              ·
                refine ⟨2039494648376423452844675, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5438652395670462540919133 2039494648376423452844675)
                ·
                  refine ⟨3059241972564635179267013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039494648376423452844675 3059241972564635179267013)
                  ·
                    refine ⟨573607869855869096112565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059241972564635179267013 573607869855869096112565)
                    ·
                      rfl

theorem cell23_3351292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 4, 1, 3, 1, 4].length) (baseStart_3351292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351292 prefixEnd_3351292 := by exact prefixLift 3351292
  have htrace : WordTrace (prefixWord ++ tailWord_3351292) baseStart_3351292 baseEnd_3351292 := by
    simpa [prefixWord, tailWord_3351292, baseEnd_3351292] using wordTrace_append hprefix tailTrace_3351292
  have hstable : (prefixWord ++ tailWord_3351292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351292).length < 2 ^ (prefixWord ++ tailWord_3351292).sum := by decide
  have hdescent : baseEnd_3351292 < baseStart_3351292 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351331 : List Nat := [1, 1, 1, 4, 2, 1, 1, 5, 1, 6]
def baseStart_3351331 : Nat := 118140960795 + 3351331 * 2 ^ 59
def prefixEnd_3351331 : Nat := 4983230072969 + 3 ^ 40 * 3351331 * 2
def baseEnd_3351331 : Nat := 573614545104377545250005

theorem tailTrace_3351331 : CollatzResearch.WordTrace tailWord_3351331 prefixEnd_3351331 573614545104377545250005 := by
  unfold tailWord_3351331
  simp only [CollatzResearch.WordTrace]
  refine ⟨122233083421707623611861847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81488722281138415741241231 122233083421707623611861847)
  ·
    refine ⟨183349625132561435417792771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122233083421707623611861847 183349625132561435417792771)
    ·
      refine ⟨275024437698842153126689157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183349625132561435417792771 275024437698842153126689157)
      ·
        refine ⟨51567082068532903711254217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 275024437698842153126689157 51567082068532903711254217)
        ·
          refine ⟨38675311551399677783440663, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51567082068532903711254217 38675311551399677783440663)
          ·
            refine ⟨58012967327099516675160995, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38675311551399677783440663 58012967327099516675160995)
            ·
              refine ⟨87019450990649275012741493, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58012967327099516675160995 87019450990649275012741493)
              ·
                refine ⟨8158073530373369532444515, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 87019450990649275012741493 8158073530373369532444515)
                ·
                  refine ⟨12237110295560054298666773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8158073530373369532444515 12237110295560054298666773)
                  ·
                    refine ⟨573614545104377545250005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12237110295560054298666773 573614545104377545250005)
                    ·
                      rfl

theorem cell23_3351331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 1, 1, 5, 1, 6].length) (baseStart_3351331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351331 prefixEnd_3351331 := by exact prefixLift 3351331
  have htrace : WordTrace (prefixWord ++ tailWord_3351331) baseStart_3351331 baseEnd_3351331 := by
    simpa [prefixWord, tailWord_3351331, baseEnd_3351331] using wordTrace_append hprefix tailTrace_3351331
  have hstable : (prefixWord ++ tailWord_3351331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351331).length < 2 ^ (prefixWord ++ tailWord_3351331).sum := by decide
  have hdescent : baseEnd_3351331 < baseStart_3351331 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351342 : List Nat := [4, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2]
def baseStart_3351342 : Nat := 118140960795 + 3351342 * 2 ^ 59
def prefixEnd_3351342 : Nat := 4983230072969 + 3 ^ 40 * 3351342 * 2
def baseEnd_3351342 : Nat := 1720849283600332092712465

theorem tailTrace_3351342 : CollatzResearch.WordTrace tailWord_3351342 prefixEnd_3351342 1720849283600332092712465 := by
  unfold tailWord_3351342
  simp only [CollatzResearch.WordTrace]
  refine ⟨15279185578083471561314035, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81488989749778514993674853 15279185578083471561314035)
  ·
    refine ⟨22918778367125207341971053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15279185578083471561314035 22918778367125207341971053)
    ·
      refine ⟨8594541887671952753239145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 22918778367125207341971053 8594541887671952753239145)
      ·
        refine ⟨6445906415753964564929359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8594541887671952753239145 6445906415753964564929359)
        ·
          refine ⟨9668859623630946847394039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6445906415753964564929359 9668859623630946847394039)
          ·
            refine ⟨14503289435446420271091059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9668859623630946847394039 14503289435446420271091059)
            ·
              refine ⟨21754934153169630406636589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14503289435446420271091059 21754934153169630406636589)
              ·
                refine ⟨8158100307438611402488721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21754934153169630406636589 8158100307438611402488721)
                ·
                  refine ⟨6118575230578958551866541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158100307438611402488721 6118575230578958551866541)
                  ·
                    refine ⟨2294465711467109456949953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6118575230578958551866541 2294465711467109456949953)
                    ·
                      refine ⟨1720849283600332092712465, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294465711467109456949953 1720849283600332092712465)
                      ·
                        rfl

theorem cell23_3351342_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 2, 1, 1, 1, 3, 2, 3, 2].length) (baseStart_3351342 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351342 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351342 prefixEnd_3351342 := by exact prefixLift 3351342
  have htrace : WordTrace (prefixWord ++ tailWord_3351342) baseStart_3351342 baseEnd_3351342 := by
    simpa [prefixWord, tailWord_3351342, baseEnd_3351342] using wordTrace_append hprefix tailTrace_3351342
  have hstable : (prefixWord ++ tailWord_3351342).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351342).length < 2 ^ (prefixWord ++ tailWord_3351342).sum := by decide
  have hdescent : baseEnd_3351342 < baseStart_3351342 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351342) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351391 : List Nat := [1, 1, 2, 3, 1, 3, 1, 2, 2, 7]
def baseStart_3351391 : Nat := 118140960795 + 3351391 * 2 ^ 59
def prefixEnd_3351391 : Nat := 4983230072969 + 3 ^ 40 * 3351391 * 2
def baseEnd_3351391 : Nat := 573624814717467466999913

theorem tailTrace_3351391 : CollatzResearch.WordTrace tailWord_3351391 prefixEnd_3351391 573624814717467466999913 := by
  unfold tailWord_3351391
  simp only [CollatzResearch.WordTrace]
  refine ⟨122235271801490253859046027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81490181200993502572697351 122235271801490253859046027)
  ·
    refine ⟨183352907702235380788569041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122235271801490253859046027 183352907702235380788569041)
    ·
      refine ⟨137514680776676535591426781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183352907702235380788569041 137514680776676535591426781)
      ·
        refine ⟨51568005291253700846785043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137514680776676535591426781 51568005291253700846785043)
        ·
          refine ⟨77352007936880551270177565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51568005291253700846785043 77352007936880551270177565)
          ·
            refine ⟨29007002976330206726316587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77352007936880551270177565 29007002976330206726316587)
            ·
              refine ⟨43510504464495310089474881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29007002976330206726316587 43510504464495310089474881)
              ·
                refine ⟨32632878348371482567106161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 43510504464495310089474881 32632878348371482567106161)
                ·
                  refine ⟨24474658761278611925329621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 32632878348371482567106161 24474658761278611925329621)
                  ·
                    refine ⟨573624814717467466999913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 24474658761278611925329621 573624814717467466999913)
                    ·
                      rfl

theorem cell23_3351391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 2, 7].length) (baseStart_3351391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351391 prefixEnd_3351391 := by exact prefixLift 3351391
  have htrace : WordTrace (prefixWord ++ tailWord_3351391) baseStart_3351391 baseEnd_3351391 := by
    simpa [prefixWord, tailWord_3351391, baseEnd_3351391] using wordTrace_append hprefix tailTrace_3351391
  have hstable : (prefixWord ++ tailWord_3351391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351391).length < 2 ^ (prefixWord ++ tailWord_3351391).sum := by decide
  have hdescent : baseEnd_3351391 < baseStart_3351391 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351405 : List Nat := [1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 3]
def baseStart_3351405 : Nat := 118140960795 + 3351405 * 2 ^ 59
def prefixEnd_3351405 : Nat := 4983230072969 + 3 ^ 40 * 3351405 * 2
def baseEnd_3351405 : Nat := 1720881632881565346224675

theorem tailTrace_3351405 : CollatzResearch.WordTrace tailWord_3351405 prefixEnd_3351405 1720881632881565346224675 := by
  unfold tailWord_3351405
  simp only [CollatzResearch.WordTrace]
  refine ⟨122235782423439534250055669, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81490521615626356166703779 122235782423439534250055669)
  ·
    refine ⟨11459604602197456335942719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 122235782423439534250055669 11459604602197456335942719)
    ·
      refine ⟨17189406903296184503914079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11459604602197456335942719 17189406903296184503914079)
      ·
        refine ⟨25784110354944276755871119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17189406903296184503914079 25784110354944276755871119)
        ·
          refine ⟨38676165532416415133806679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25784110354944276755871119 38676165532416415133806679)
          ·
            refine ⟨58014248298624622700710019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38676165532416415133806679 58014248298624622700710019)
            ·
              refine ⟨87021372447936934051065029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58014248298624622700710019 87021372447936934051065029)
              ·
                refine ⟨16316507333988175134574693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87021372447936934051065029 16316507333988175134574693)
                ·
                  refine ⟨3059345125122782837732755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16316507333988175134574693 3059345125122782837732755)
                  ·
                    refine ⟨4589017687684174256599133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3059345125122782837732755 4589017687684174256599133)
                    ·
                      refine ⟨1720881632881565346224675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4589017687684174256599133 1720881632881565346224675)
                      ·
                        rfl

theorem cell23_3351405_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 1, 4, 4, 1, 3].length) (baseStart_3351405 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351405 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351405 prefixEnd_3351405 := by exact prefixLift 3351405
  have htrace : WordTrace (prefixWord ++ tailWord_3351405) baseStart_3351405 baseEnd_3351405 := by
    simpa [prefixWord, tailWord_3351405, baseEnd_3351405] using wordTrace_append hprefix tailTrace_3351405
  have hstable : (prefixWord ++ tailWord_3351405).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351405).length < 2 ^ (prefixWord ++ tailWord_3351405).sum := by decide
  have hdescent : baseEnd_3351405 < baseStart_3351405 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351405) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351406 : List Nat := [4, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4]
def baseStart_3351406 : Nat := 118140960795 + 3351406 * 2 ^ 59
def prefixEnd_3351406 : Nat := 4983230072969 + 3 ^ 40 * 3351406 * 2
def baseEnd_3351406 : Nat := 1720882146362219842312171

theorem tailTrace_3351406 : CollatzResearch.WordTrace tailWord_3351406 prefixEnd_3351406 1720882146362219842312171 := by
  unfold tailWord_3351406
  simp only [CollatzResearch.WordTrace]
  refine ⟨15279477362054488927605259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81490545930957274280561381 15279477362054488927605259)
  ·
    refine ⟨22919216043081733391407889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15279477362054488927605259 22919216043081733391407889)
    ·
      refine ⟨17189412032311300043555917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22919216043081733391407889 17189412032311300043555917)
      ·
        refine ⟨6446029512116737516333469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17189412032311300043555917 6446029512116737516333469)
        ·
          refine ⟨2417261067043776568625051, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 6446029512116737516333469 2417261067043776568625051)
          ·
            refine ⟨3625891600565664852937577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2417261067043776568625051 3625891600565664852937577)
            ·
              refine ⟨2719418700424248639703183, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3625891600565664852937577 2719418700424248639703183)
              ·
                refine ⟨4079128050636372959554775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719418700424248639703183 4079128050636372959554775)
                ·
                  refine ⟨6118692075954559439332163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079128050636372959554775 6118692075954559439332163)
                  ·
                    refine ⟨9178038113931839158998245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118692075954559439332163 9178038113931839158998245)
                    ·
                      refine ⟨1720882146362219842312171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9178038113931839158998245 1720882146362219842312171)
                      ·
                        rfl

theorem cell23_3351406_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 3, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_3351406 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351406 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351406 prefixEnd_3351406 := by exact prefixLift 3351406
  have htrace : WordTrace (prefixWord ++ tailWord_3351406) baseStart_3351406 baseEnd_3351406 := by
    simpa [prefixWord, tailWord_3351406, baseEnd_3351406] using wordTrace_append hprefix tailTrace_3351406
  have hstable : (prefixWord ++ tailWord_3351406).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351406).length < 2 ^ (prefixWord ++ tailWord_3351406).sum := by decide
  have hdescent : baseEnd_3351406 < baseStart_3351406 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351406) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351498 : List Nat := [3, 1, 2, 1, 2, 1, 1, 1, 6, 5]
def baseStart_3351498 : Nat := 118140960795 + 3351498 * 2 ^ 59
def prefixEnd_3351498 : Nat := 4983230072969 + 3 ^ 40 * 3351498 * 2
def baseEnd_3351498 : Nat := 573643128860811160787249

theorem tailTrace_3351498 : CollatzResearch.WordTrace tailWord_3351498 prefixEnd_3351498 573643128860811160787249 := by
  unfold tailWord_3351498
  simp only [CollatzResearch.WordTrace]
  refine ⟨30559793603025652783297787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81492782941401740755460765 30559793603025652783297787)
  ·
    refine ⟨45839690404538479174946681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30559793603025652783297787 45839690404538479174946681)
    ·
      refine ⟨34379767803403859381210011, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45839690404538479174946681 34379767803403859381210011)
      ·
        refine ⟨51569651705105789071815017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34379767803403859381210011 51569651705105789071815017)
        ·
          refine ⟨38677238778829341803861263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51569651705105789071815017 38677238778829341803861263)
          ·
            refine ⟨58015858168244012705791895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38677238778829341803861263 58015858168244012705791895)
            ·
              refine ⟨87023787252366019058687843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58015858168244012705791895 87023787252366019058687843)
              ·
                refine ⟨130535680878549028588031765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 87023787252366019058687843 130535680878549028588031765)
                ·
                  refine ⟨6118860041181985715063989, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 130535680878549028588031765 6118860041181985715063989)
                  ·
                    refine ⟨573643128860811160787249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6118860041181985715063989 573643128860811160787249)
                    ·
                      rfl

theorem cell23_3351498_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_3351498 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351498 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351498 prefixEnd_3351498 := by exact prefixLift 3351498
  have htrace : WordTrace (prefixWord ++ tailWord_3351498) baseStart_3351498 baseEnd_3351498 := by
    simpa [prefixWord, tailWord_3351498, baseEnd_3351498] using wordTrace_append hprefix tailTrace_3351498
  have hstable : (prefixWord ++ tailWord_3351498).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351498).length < 2 ^ (prefixWord ++ tailWord_3351498).sum := by decide
  have hdescent : baseEnd_3351498 < baseStart_3351498 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351498) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351535 : List Nat := [1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 4]
def baseStart_3351535 : Nat := 118140960795 + 3351535 * 2 ^ 59
def prefixEnd_3351535 : Nat := 4983230072969 + 3 ^ 40 * 3351535 * 2
def baseEnd_3351535 : Nat := 1720948385366649837599077

theorem tailTrace_3351535 : CollatzResearch.WordTrace tailWord_3351535 prefixEnd_3351535 1720948385366649837599077 := by
  unfold tailWord_3351535
  simp only [CollatzResearch.WordTrace]
  refine ⟨122240523912968566452288059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81493682608645710968192039 122240523912968566452288059)
  ·
    refine ⟨183360785869452849678432089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122240523912968566452288059 183360785869452849678432089)
    ·
      refine ⟨137520589402089637258824067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 183360785869452849678432089 137520589402089637258824067)
      ·
        refine ⟨206280884103134455888236101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 137520589402089637258824067 206280884103134455888236101)
        ·
          refine ⟨38677665769337710479044269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 206280884103134455888236101 38677665769337710479044269)
          ·
            refine ⟨14504124663501641429641601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38677665769337710479044269 14504124663501641429641601)
            ·
              refine ⟨10878093497626231072231201, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14504124663501641429641601 10878093497626231072231201)
              ·
                refine ⟨8158570123219673304173401, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10878093497626231072231201 8158570123219673304173401)
                ·
                  refine ⟨6118927592414754978130051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8158570123219673304173401 6118927592414754978130051)
                  ·
                    refine ⟨9178391388622132467195077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6118927592414754978130051 9178391388622132467195077)
                    ·
                      refine ⟨1720948385366649837599077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9178391388622132467195077 1720948385366649837599077)
                      ·
                        rfl

theorem cell23_3351535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 2, 2, 2, 1, 4].length) (baseStart_3351535 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351535 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351535 prefixEnd_3351535 := by exact prefixLift 3351535
  have htrace : WordTrace (prefixWord ++ tailWord_3351535) baseStart_3351535 baseEnd_3351535 := by
    simpa [prefixWord, tailWord_3351535, baseEnd_3351535] using wordTrace_append hprefix tailTrace_3351535
  have hstable : (prefixWord ++ tailWord_3351535).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351535).length < 2 ^ (prefixWord ++ tailWord_3351535).sum := by decide
  have hdescent : baseEnd_3351535 < baseStart_3351535 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351545 : List Nat := [1, 2, 1, 3, 1, 3, 2, 3, 3, 4]
def baseStart_3351545 : Nat := 118140960795 + 3351545 * 2 ^ 59
def prefixEnd_3351545 : Nat := 4983230072969 + 3 ^ 40 * 3351545 * 2
def baseEnd_3351545 : Nat := 573651173391064932824677

theorem tailTrace_3351545 : CollatzResearch.WordTrace tailWord_3351545 prefixEnd_3351545 573651173391064932824677 := by
  unfold tailWord_3351545
  simp only [CollatzResearch.WordTrace]
  refine ⟨122240888642932338160152089, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81493925761954892106768059 122240888642932338160152089)
  ·
    refine ⟨91680666482199253620114067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 122240888642932338160152089 91680666482199253620114067)
    ·
      refine ⟨137520999723298880430171101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 91680666482199253620114067 137520999723298880430171101)
      ·
        refine ⟨51570374896237080161314163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 137520999723298880430171101 51570374896237080161314163)
        ·
          refine ⟨77355562344355620241971245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51570374896237080161314163 77355562344355620241971245)
          ·
            refine ⟨29008335879133357590739217, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 77355562344355620241971245 29008335879133357590739217)
            ·
              refine ⟨21756251909350018193054413, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29008335879133357590739217 21756251909350018193054413)
              ·
                refine ⟨8158594466006256822395405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21756251909350018193054413 8158594466006256822395405)
                ·
                  refine ⟨3059472924752346308398277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8158594466006256822395405 3059472924752346308398277)
                  ·
                    refine ⟨573651173391064932824677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059472924752346308398277 573651173391064932824677)
                    ·
                      rfl

theorem cell23_3351545_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 1, 3, 2, 3, 3, 4].length) (baseStart_3351545 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351545 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351545 prefixEnd_3351545 := by exact prefixLift 3351545
  have htrace : WordTrace (prefixWord ++ tailWord_3351545) baseStart_3351545 baseEnd_3351545 := by
    simpa [prefixWord, tailWord_3351545, baseEnd_3351545] using wordTrace_append hprefix tailTrace_3351545
  have hstable : (prefixWord ++ tailWord_3351545).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351545).length < 2 ^ (prefixWord ++ tailWord_3351545).sum := by decide
  have hdescent : baseEnd_3351545 < baseStart_3351545 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351545) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351562 : List Nat := [3, 1, 2, 2, 3, 2, 1, 2, 3, 4]
def baseStart_3351562 : Nat := 118140960795 + 3351562 * 2 ^ 59
def prefixEnd_3351562 : Nat := 4983230072969 + 3 ^ 40 * 3351562 * 2
def baseEnd_3351562 : Nat := 573654083114773743987151

theorem tailTrace_3351562 : CollatzResearch.WordTrace tailWord_3351562 prefixEnd_3351562 573654083114773743987151 := by
  unfold tailWord_3351562
  simp only [CollatzResearch.WordTrace]
  refine ⟨30560377170967687515880235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81494339122580500042347293 30560377170967687515880235)
  ·
    refine ⟨45840565756451531273820353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30560377170967687515880235 45840565756451531273820353)
    ·
      refine ⟨34380424317338648455365265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45840565756451531273820353 34380424317338648455365265)
      ·
        refine ⟨25785318238003986341523949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34380424317338648455365265 25785318238003986341523949)
        ·
          refine ⟨9669494339251494878071481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 25785318238003986341523949 9669494339251494878071481)
          ·
            refine ⟨7252120754438621158553611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9669494339251494878071481 7252120754438621158553611)
            ·
              refine ⟨10878181131657931737830417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252120754438621158553611 10878181131657931737830417)
              ·
                refine ⟨8158635848743448803372813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10878181131657931737830417 8158635848743448803372813)
                ·
                  refine ⟨3059488443278793301264805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 8158635848743448803372813 3059488443278793301264805)
                  ·
                    refine ⟨573654083114773743987151, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059488443278793301264805 573654083114773743987151)
                    ·
                      rfl

theorem cell23_3351562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_3351562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351562 prefixEnd_3351562 := by exact prefixLift 3351562
  have htrace : WordTrace (prefixWord ++ tailWord_3351562) baseStart_3351562 baseEnd_3351562 := by
    simpa [prefixWord, tailWord_3351562, baseEnd_3351562] using wordTrace_append hprefix tailTrace_3351562
  have hstable : (prefixWord ++ tailWord_3351562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351562).length < 2 ^ (prefixWord ++ tailWord_3351562).sum := by decide
  have hdescent : baseEnd_3351562 < baseStart_3351562 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351612 : List Nat := [2, 2, 2, 2, 2, 2, 1, 2, 1, 5, 2]
def baseStart_3351612 : Nat := 118140960795 + 3351612 * 2 ^ 59
def prefixEnd_3351612 : Nat := 4983230072969 + 3 ^ 40 * 3351612 * 2
def baseEnd_3351612 : Nat := 1720987923377046036336223

theorem tailTrace_3351612 : CollatzResearch.WordTrace tailWord_3351612 prefixEnd_3351612 1720987923377046036336223 := by
  unfold tailWord_3351612
  simp only [CollatzResearch.WordTrace]
  refine ⟨61121666166844804301420545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81495554889126405735227393 61121666166844804301420545)
  ·
    refine ⟨45841249625133603226065409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61121666166844804301420545 45841249625133603226065409)
    ·
      refine ⟨34380937218850202419549057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 45841249625133603226065409 34380937218850202419549057)
      ·
        refine ⟨25785702914137651814661793, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34380937218850202419549057 25785702914137651814661793)
        ·
          refine ⟨19339277185603238860996345, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25785702914137651814661793 19339277185603238860996345)
          ·
            refine ⟨14504457889202429145747259, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19339277185603238860996345 14504457889202429145747259)
            ·
              refine ⟨21756686833803643718620889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14504457889202429145747259 21756686833803643718620889)
              ·
                refine ⟨16317515125352732788965667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21756686833803643718620889 16317515125352732788965667)
                ·
                  refine ⟨24476272688029099183448501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16317515125352732788965667 24476272688029099183448501)
                  ·
                    refine ⟨2294650564502728048448297, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24476272688029099183448501 2294650564502728048448297)
                    ·
                      refine ⟨1720987923377046036336223, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294650564502728048448297 1720987923377046036336223)
                      ·
                        rfl

theorem cell23_3351612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 2, 1, 2, 1, 5, 2].length) (baseStart_3351612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351612 prefixEnd_3351612 := by exact prefixLift 3351612
  have htrace : WordTrace (prefixWord ++ tailWord_3351612) baseStart_3351612 baseEnd_3351612 := by
    simpa [prefixWord, tailWord_3351612, baseEnd_3351612] using wordTrace_append hprefix tailTrace_3351612
  have hstable : (prefixWord ++ tailWord_3351612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351612).length < 2 ^ (prefixWord ++ tailWord_3351612).sum := by decide
  have hdescent : baseEnd_3351612 < baseStart_3351612 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351629 : List Nat := [1, 6, 1, 1, 1, 2, 2, 1, 1, 5, 2]
def baseStart_3351629 : Nat := 118140960795 + 3351629 * 2 ^ 59
def prefixEnd_3351629 : Nat := 4983230072969 + 3 ^ 40 * 3351629 * 2
def baseEnd_3351629 : Nat := 1720996652548172469823645

theorem tailTrace_3351629 : CollatzResearch.WordTrace tailWord_3351629 prefixEnd_3351629 1720996652548172469823645 := by
  unfold tailWord_3351629
  simp only [CollatzResearch.WordTrace]
  refine ⟨122243952374628020506209941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81495968249752013670806627 122243952374628020506209941)
  ·
    refine ⟨5730185267560688461228591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 122243952374628020506209941 5730185267560688461228591)
    ·
      refine ⟨8595277901341032691842887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5730185267560688461228591 8595277901341032691842887)
      ·
        refine ⟨12892916852011549037764331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8595277901341032691842887 12892916852011549037764331)
        ·
          refine ⟨19339375278017323556646497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12892916852011549037764331 19339375278017323556646497)
          ·
            refine ⟨14504531458512992667484873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19339375278017323556646497 14504531458512992667484873)
            ·
              refine ⟨10878398593884744500613655, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14504531458512992667484873 10878398593884744500613655)
              ·
                refine ⟨16317597890827116750920483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10878398593884744500613655 16317597890827116750920483)
                ·
                  refine ⟨24476396836240675126380725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16317597890827116750920483 24476396836240675126380725)
                  ·
                    refine ⟨2294662203397563293098193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24476396836240675126380725 2294662203397563293098193)
                    ·
                      refine ⟨1720996652548172469823645, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294662203397563293098193 1720996652548172469823645)
                      ·
                        rfl

theorem cell23_3351629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 2, 2, 1, 1, 5, 2].length) (baseStart_3351629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351629 prefixEnd_3351629 := by exact prefixLift 3351629
  have htrace : WordTrace (prefixWord ++ tailWord_3351629) baseStart_3351629 baseEnd_3351629 := by
    simpa [prefixWord, tailWord_3351629, baseEnd_3351629] using wordTrace_append hprefix tailTrace_3351629
  have hstable : (prefixWord ++ tailWord_3351629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351629).length < 2 ^ (prefixWord ++ tailWord_3351629).sum := by decide
  have hdescent : baseEnd_3351629 < baseStart_3351629 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351635 : List Nat := [1, 1, 1, 2, 1, 1, 2, 6, 4, 4]
def baseStart_3351635 : Nat := 118140960795 + 3351635 * 2 ^ 59
def prefixEnd_3351635 : Nat := 4983230072969 + 3 ^ 40 * 3351635 * 2
def baseEnd_3351635 : Nat := 573666577810699815449539

theorem tailTrace_3351635 : CollatzResearch.WordTrace tailWord_3351635 prefixEnd_3351635 573666577810699815449539 := by
  unfold tailWord_3351635
  simp only [CollatzResearch.WordTrace]
  refine ⟨122244171212606283530928359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81496114141737522353952239 122244171212606283530928359)
  ·
    refine ⟨183366256818909425296392539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122244171212606283530928359 183366256818909425296392539)
    ·
      refine ⟨275049385228364137944588809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183366256818909425296392539 275049385228364137944588809)
      ·
        refine ⟨206287038921273103458441607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275049385228364137944588809 206287038921273103458441607)
        ·
          refine ⟨309430558381909655187662411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 206287038921273103458441607 309430558381909655187662411)
          ·
            refine ⟨464145837572864482781493617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 309430558381909655187662411 464145837572864482781493617)
            ·
              refine ⟨348109378179648362086120213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 464145837572864482781493617 348109378179648362086120213)
              ·
                refine ⟨16317627102171016972786885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 348109378179648362086120213 16317627102171016972786885)
                ·
                  refine ⟨3059555081657065682397541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16317627102171016972786885 3059555081657065682397541)
                  ·
                    refine ⟨573666577810699815449539, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059555081657065682397541 573666577810699815449539)
                    ·
                      rfl

theorem cell23_3351635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 2, 6, 4, 4].length) (baseStart_3351635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351635 prefixEnd_3351635 := by exact prefixLift 3351635
  have htrace : WordTrace (prefixWord ++ tailWord_3351635) baseStart_3351635 baseEnd_3351635 := by
    simpa [prefixWord, tailWord_3351635, baseEnd_3351635] using wordTrace_append hprefix tailTrace_3351635
  have hstable : (prefixWord ++ tailWord_3351635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351635).length < 2 ^ (prefixWord ++ tailWord_3351635).sum := by decide
  have hdescent : baseEnd_3351635 < baseStart_3351635 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351636 : List Nat := [2, 4, 1, 1, 1, 1, 5, 3, 1, 1, 3]
def baseStart_3351636 : Nat := 118140960795 + 3351636 * 2 ^ 59
def prefixEnd_3351636 : Nat := 4983230072969 + 3 ^ 40 * 3351636 * 2
def baseEnd_3351636 : Nat := 1721000246912753942436113

theorem tailTrace_3351636 : CollatzResearch.WordTrace tailWord_3351636 prefixEnd_3351636 1721000246912753942436113 := by
  unfold tailWord_3351636
  simp only [CollatzResearch.WordTrace]
  refine ⟨61122103842801330350857381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81496138457068440467809841 61122103842801330350857381)
  ·
    refine ⟨11460394470525249440785759, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61122103842801330350857381 11460394470525249440785759)
    ·
      refine ⟨17190591705787874161178639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11460394470525249440785759 17190591705787874161178639)
      ·
        refine ⟨25785887558681811241767959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17190591705787874161178639 25785887558681811241767959)
        ·
          refine ⟨38678831338022716862651939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25785887558681811241767959 38678831338022716862651939)
          ·
            refine ⟨58018247007034075293977909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38678831338022716862651939 58018247007034075293977909)
            ·
              refine ⟨5439210656909444558810429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 58018247007034075293977909 5439210656909444558810429)
              ·
                refine ⟨2039703996341041709553911, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439210656909444558810429 2039703996341041709553911)
                ·
                  refine ⟨3059555994511562564330867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039703996341041709553911 3059555994511562564330867)
                  ·
                    refine ⟨4589333991767343846496301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3059555994511562564330867 4589333991767343846496301)
                    ·
                      refine ⟨1721000246912753942436113, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4589333991767343846496301 1721000246912753942436113)
                      ·
                        rfl

theorem cell23_3351636_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 1, 5, 3, 1, 1, 3].length) (baseStart_3351636 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351636 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351636 prefixEnd_3351636 := by exact prefixLift 3351636
  have htrace : WordTrace (prefixWord ++ tailWord_3351636) baseStart_3351636 baseEnd_3351636 := by
    simpa [prefixWord, tailWord_3351636, baseEnd_3351636] using wordTrace_append hprefix tailTrace_3351636
  have hstable : (prefixWord ++ tailWord_3351636).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351636).length < 2 ^ (prefixWord ++ tailWord_3351636).sum := by decide
  have hdescent : baseEnd_3351636 < baseStart_3351636 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351636) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351652 : List Nat := [2, 3, 1, 1, 2, 1, 1, 6, 2, 4]
def baseStart_3351652 : Nat := 118140960795 + 3351652 * 2 ^ 59
def prefixEnd_3351652 : Nat := 4983230072969 + 3 ^ 40 * 3351652 * 2
def baseEnd_3351652 : Nat := 573669487534408626612013

theorem tailTrace_3351652 : CollatzResearch.WordTrace tailWord_3351652 prefixEnd_3351652 573669487534408626612013 := by
  unfold tailWord_3351652
  simp only [CollatzResearch.WordTrace]
  refine ⟨61122395626772347717148605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81496527502363130289531473 61122395626772347717148605)
  ·
    refine ⟨22920898360039630393930727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 61122395626772347717148605 22920898360039630393930727)
    ·
      refine ⟨34381347540059445590896091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22920898360039630393930727 34381347540059445590896091)
      ·
        refine ⟨51572021310089168386344137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34381347540059445590896091 51572021310089168386344137)
        ·
          refine ⟨38679015982566876289758103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51572021310089168386344137 38679015982566876289758103)
          ·
            refine ⟨58018523973850314434637155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 38679015982566876289758103 58018523973850314434637155)
            ·
              refine ⟨87027785960775471651955733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 58018523973850314434637155 87027785960775471651955733)
              ·
                refine ⟨4079427466911350233685425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 87027785960775471651955733 4079427466911350233685425)
                ·
                  refine ⟨3059570600183512675264069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 4079427466911350233685425 3059570600183512675264069)
                  ·
                    refine ⟨573669487534408626612013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059570600183512675264069 573669487534408626612013)
                    ·
                      rfl

theorem cell23_3351652_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 6, 2, 4].length) (baseStart_3351652 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351652 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351652 prefixEnd_3351652 := by exact prefixLift 3351652
  have htrace : WordTrace (prefixWord ++ tailWord_3351652) baseStart_3351652 baseEnd_3351652 := by
    simpa [prefixWord, tailWord_3351652, baseEnd_3351652] using wordTrace_append hprefix tailTrace_3351652
  have hstable : (prefixWord ++ tailWord_3351652).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351652).length < 2 ^ (prefixWord ++ tailWord_3351652).sum := by decide
  have hdescent : baseEnd_3351652 < baseStart_3351652 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351652) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351655 : List Nat := [1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 6]
def baseStart_3351655 : Nat := 118140960795 + 3351655 * 2 ^ 59
def prefixEnd_3351655 : Nat := 4983230072969 + 3 ^ 40 * 3351655 * 2
def baseEnd_3351655 : Nat := 1721010003045189368098525

theorem tailTrace_3351655 : CollatzResearch.WordTrace tailWord_3351655 prefixEnd_3351655 1721010003045189368098525 := by
  unfold tailWord_3351655
  simp only [CollatzResearch.WordTrace]
  refine ⟨122244900672533826946656419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81496600448355884631104279 122244900672533826946656419)
  ·
    refine ⟨183367351008800740419984629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122244900672533826946656419 183367351008800740419984629)
    ·
      refine ⟨17190689157075069414373559, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183367351008800740419984629 17190689157075069414373559)
      ·
        refine ⟨25786033735612604121560339, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17190689157075069414373559 25786033735612604121560339)
        ·
          refine ⟨38679050603418906182340509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25786033735612604121560339 38679050603418906182340509)
          ·
            refine ⟨14504643976282089818377691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 38679050603418906182340509 14504643976282089818377691)
            ·
              refine ⟨21756965964423134727566537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14504643976282089818377691 21756965964423134727566537)
              ·
                refine ⟨16317724473317351045674903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 21756965964423134727566537 16317724473317351045674903)
                ·
                  refine ⟨24476586709976026568512355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16317724473317351045674903 24476586709976026568512355)
                  ·
                    refine ⟨36714880064964039852768533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24476586709976026568512355 36714880064964039852768533)
                    ·
                      refine ⟨1721010003045189368098525, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 36714880064964039852768533 1721010003045189368098525)
                      ·
                        rfl

theorem cell23_3351655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_3351655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351655 prefixEnd_3351655 := by exact prefixLift 3351655
  have htrace : WordTrace (prefixWord ++ tailWord_3351655) baseStart_3351655 baseEnd_3351655 := by
    simpa [prefixWord, tailWord_3351655, baseEnd_3351655] using wordTrace_append hprefix tailTrace_3351655
  have hstable : (prefixWord ++ tailWord_3351655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351655).length < 2 ^ (prefixWord ++ tailWord_3351655).sum := by decide
  have hdescent : baseEnd_3351655 < baseStart_3351655 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351662 : List Nat := [4, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5]
def baseStart_3351662 : Nat := 118140960795 + 3351662 * 2 ^ 59
def prefixEnd_3351662 : Nat := 4983230072969 + 3 ^ 40 * 3351662 * 2
def baseEnd_3351662 : Nat := 1721013597409770840710993

theorem tailTrace_3351662 : CollatzResearch.WordTrace tailWord_3351662 prefixEnd_3351662 1721013597409770840710993 := by
  unfold tailWord_3351662
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280644497938558392770155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81496770655672311428107493 15280644497938558392770155)
  ·
    refine ⟨22920966746907837589155233, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 15280644497938558392770155 22920966746907837589155233)
    ·
      refine ⟨17190725060180878191866425, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22920966746907837589155233 17190725060180878191866425)
      ·
        refine ⟨12893043795135658643899819, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17190725060180878191866425 12893043795135658643899819)
        ·
          refine ⟨19339565692703487965849729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893043795135658643899819 19339565692703487965849729)
          ·
            refine ⟨14504674269527615974387297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19339565692703487965849729 14504674269527615974387297)
            ·
              refine ⟨10878505702145711980790473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14504674269527615974387297 10878505702145711980790473)
              ·
                refine ⟨8158879276609283985592855, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 10878505702145711980790473 8158879276609283985592855)
                ·
                  refine ⟨12238318914913925978389283, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8158879276609283985592855 12238318914913925978389283)
                  ·
                    refine ⟨18357478372370888967583925, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12238318914913925978389283 18357478372370888967583925)
                    ·
                      refine ⟨1721013597409770840710993, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 18357478372370888967583925 1721013597409770840710993)
                      ·
                        rfl

theorem cell23_3351662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_3351662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351662 prefixEnd_3351662 := by exact prefixLift 3351662
  have htrace : WordTrace (prefixWord ++ tailWord_3351662) baseStart_3351662 baseEnd_3351662 := by
    simpa [prefixWord, tailWord_3351662, baseEnd_3351662] using wordTrace_append hprefix tailTrace_3351662
  have hstable : (prefixWord ++ tailWord_3351662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351662).length < 2 ^ (prefixWord ++ tailWord_3351662).sum := by decide
  have hdescent : baseEnd_3351662 < baseStart_3351662 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351675 : List Nat := [1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 3]
def baseStart_3351675 : Nat := 118140960795 + 3351675 * 2 ^ 59
def prefixEnd_3351675 : Nat := 4983230072969 + 3 ^ 40 * 3351675 * 2
def baseEnd_3351675 : Nat := 1721020272658279289848433

theorem tailTrace_3351675 : CollatzResearch.WordTrace tailWord_3351675 prefixEnd_3351675 1721020272658279289848433 := by
  unfold tailWord_3351675
  simp only [CollatzResearch.WordTrace]
  refine ⟨122245630132461370362384479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81497086754974246908256319 122245630132461370362384479)
  ·
    refine ⟨183368445198692055543576719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122245630132461370362384479 183368445198692055543576719)
    ·
      refine ⟨275052667798038083315365079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183368445198692055543576719 275052667798038083315365079)
      ·
        refine ⟨412579001697057124973047619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 275052667798038083315365079 412579001697057124973047619)
        ·
          refine ⟨618868502545585687459571429, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 412579001697057124973047619 618868502545585687459571429)
          ·
            refine ⟨116037844227297316398669643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 618868502545585687459571429 116037844227297316398669643)
            ·
              refine ⟨174056766340945974598004465, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116037844227297316398669643 174056766340945974598004465)
              ·
                refine ⟨130542574755709480948503349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 174056766340945974598004465 130542574755709480948503349)
                ·
                  refine ⟨12238366383347763838922189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 130542574755709480948503349 12238366383347763838922189)
                  ·
                    refine ⟨4589387393755411439595821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12238366383347763838922189 4589387393755411439595821)
                    ·
                      refine ⟨1721020272658279289848433, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4589387393755411439595821 1721020272658279289848433)
                      ·
                        rfl

theorem cell23_3351675_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 1, 2, 5, 3, 3].length) (baseStart_3351675 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351675 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351675 prefixEnd_3351675 := by exact prefixLift 3351675
  have htrace : WordTrace (prefixWord ++ tailWord_3351675) baseStart_3351675 baseEnd_3351675 := by
    simpa [prefixWord, tailWord_3351675, baseEnd_3351675] using wordTrace_append hprefix tailTrace_3351675
  have hstable : (prefixWord ++ tailWord_3351675).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351675).length < 2 ^ (prefixWord ++ tailWord_3351675).sum := by decide
  have hdescent : baseEnd_3351675 < baseStart_3351675 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351675) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351692 : List Nat := [2, 2, 1, 2, 1, 1, 1, 3, 6, 1, 3]
def baseStart_3351692 : Nat := 118140960795 + 3351692 * 2 ^ 59
def prefixEnd_3351692 : Nat := 4983230072969 + 3 ^ 40 * 3351692 * 2
def baseEnd_3351692 : Nat := 1721029001829405723335855

theorem tailTrace_3351692 : CollatzResearch.WordTrace tailWord_3351692 prefixEnd_3351692 1721029001829405723335855 := by
  unfold tailWord_3351692
  simp only [CollatzResearch.WordTrace]
  refine ⟨61123125086699891132876665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81497500115599854843835553 61123125086699891132876665)
  ·
    refine ⟨45842343815024918349657499, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61123125086699891132876665 45842343815024918349657499)
    ·
      refine ⟨68763515722537377524486249, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45842343815024918349657499 68763515722537377524486249)
      ·
        refine ⟨51572636791903033143364687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 68763515722537377524486249 51572636791903033143364687)
        ·
          refine ⟨77358955187854549715047031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 51572636791903033143364687 77358955187854549715047031)
          ·
            refine ⟨116038432781781824572570547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 77358955187854549715047031 116038432781781824572570547)
            ·
              refine ⟨174057649172672736858855821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 116038432781781824572570547 174057649172672736858855821)
              ·
                refine ⟨65271618439752276322070933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 174057649172672736858855821 65271618439752276322070933)
                ·
                  refine ⟨3059607114363387952597075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 65271618439752276322070933 3059607114363387952597075)
                  ·
                    refine ⟨4589410671545081928895613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 3059607114363387952597075 4589410671545081928895613)
                    ·
                      refine ⟨1721029001829405723335855, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4589410671545081928895613 1721029001829405723335855)
                      ·
                        rfl

theorem cell23_3351692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 3, 6, 1, 3].length) (baseStart_3351692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351692 prefixEnd_3351692 := by exact prefixLift 3351692
  have htrace : WordTrace (prefixWord ++ tailWord_3351692) baseStart_3351692 baseEnd_3351692 := by
    simpa [prefixWord, tailWord_3351692, baseEnd_3351692] using wordTrace_append hprefix tailTrace_3351692
  have hstable : (prefixWord ++ tailWord_3351692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351692).length < 2 ^ (prefixWord ++ tailWord_3351692).sum := by decide
  have hdescent : baseEnd_3351692 < baseStart_3351692 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351710 : List Nat := [4, 3, 1, 1, 2, 2, 1, 4, 1, 2, 2]
def baseStart_3351710 : Nat := 118140960795 + 3351710 * 2 ^ 59
def prefixEnd_3351710 : Nat := 4983230072969 + 3 ^ 40 * 3351710 * 2
def baseEnd_3351710 : Nat := 1721038244481186652910773

theorem tailTrace_3351710 : CollatzResearch.WordTrace tailWord_3351710 prefixEnd_3351710 1721038244481186652910773 := by
  unfold tailWord_3351710
  simp only [CollatzResearch.WordTrace]
  refine ⟨15280863335916821417488573, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81497937791556380893272389 15280863335916821417488573)
  ·
    refine ⟨5730323750968808031558215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 15280863335916821417488573 5730323750968808031558215)
    ·
      refine ⟨8595485626453212047337323, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5730323750968808031558215 8595485626453212047337323)
      ·
        refine ⟨12893228439679818071005985, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8595485626453212047337323 12893228439679818071005985)
        ·
          refine ⟨9669921329759863553254489, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12893228439679818071005985 9669921329759863553254489)
          ·
            refine ⟨7252440997319897664940867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9669921329759863553254489 7252440997319897664940867)
            ·
              refine ⟨10878661495979846497411301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252440997319897664940867 10878661495979846497411301)
              ·
                refine ⟨2039749030496221218264619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 10878661495979846497411301 2039749030496221218264619)
                ·
                  refine ⟨3059623545744331827396929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039749030496221218264619 3059623545744331827396929)
                  ·
                    refine ⟨2294717659308248870547697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059623545744331827396929 2294717659308248870547697)
                    ·
                      refine ⟨1721038244481186652910773, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294717659308248870547697 1721038244481186652910773)
                      ·
                        rfl

theorem cell23_3351710_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 2, 1, 4, 1, 2, 2].length) (baseStart_3351710 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351710 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351710 prefixEnd_3351710 := by exact prefixLift 3351710
  have htrace : WordTrace (prefixWord ++ tailWord_3351710) baseStart_3351710 baseEnd_3351710 := by
    simpa [prefixWord, tailWord_3351710, baseEnd_3351710] using wordTrace_append hprefix tailTrace_3351710
  have hstable : (prefixWord ++ tailWord_3351710).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351710).length < 2 ^ (prefixWord ++ tailWord_3351710).sum := by decide
  have hdescent : baseEnd_3351710 < baseStart_3351710 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351710) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351749 : List Nat := [1, 3, 1, 1, 1, 1, 3, 4, 4, 2, 2]
def baseStart_3351749 : Nat := 118140960795 + 3351749 * 2 ^ 59
def prefixEnd_3351749 : Nat := 4983230072969 + 3 ^ 40 * 3351749 * 2
def baseEnd_3351749 : Nat := 1721058270226712000323093

theorem tailTrace_3351749 : CollatzResearch.WordTrace tailWord_3351749 prefixEnd_3351749 1721058270226712000323093 := by
  unfold tailWord_3351749
  simp only [CollatzResearch.WordTrace]
  refine ⟨122248329134193281000578301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81498886089462187333718867 122248329134193281000578301)
  ·
    refine ⟨45843123425322480375216863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122248329134193281000578301 45843123425322480375216863)
    ·
      refine ⟨68764685137983720562825295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45843123425322480375216863 68764685137983720562825295)
      ·
        refine ⟨103147027706975580844237943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68764685137983720562825295 103147027706975580844237943)
        ·
          refine ⟨154720541560463371266356915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103147027706975580844237943 154720541560463371266356915)
          ·
            refine ⟨232080812340695056899535373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154720541560463371266356915 232080812340695056899535373)
            ·
              refine ⟨87030304627760646337325765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 232080812340695056899535373 87030304627760646337325765)
              ·
                refine ⟨16318182117705121188248581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 87030304627760646337325765 16318182117705121188248581)
                ·
                  refine ⟨3059659147069710222796609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 16318182117705121188248581 3059659147069710222796609)
                  ·
                    refine ⟨2294744360302282667097457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059659147069710222796609 2294744360302282667097457)
                    ·
                      refine ⟨1721058270226712000323093, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294744360302282667097457 1721058270226712000323093)
                      ·
                        rfl

theorem cell23_3351749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 4, 4, 2, 2].length) (baseStart_3351749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351749 prefixEnd_3351749 := by exact prefixLift 3351749
  have htrace : WordTrace (prefixWord ++ tailWord_3351749) baseStart_3351749 baseEnd_3351749 := by
    simpa [prefixWord, tailWord_3351749, baseEnd_3351749] using wordTrace_append hprefix tailTrace_3351749
  have hstable : (prefixWord ++ tailWord_3351749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351749).length < 2 ^ (prefixWord ++ tailWord_3351749).sum := by decide
  have hdescent : baseEnd_3351749 < baseStart_3351749 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351762 : List Nat := [3, 2, 2, 2, 1, 1, 1, 1, 4, 2, 4]
def baseStart_3351762 : Nat := 118140960795 + 3351762 * 2 ^ 59
def prefixEnd_3351762 : Nat := 4983230072969 + 3 ^ 40 * 3351762 * 2
def baseEnd_3351762 : Nat := 1721064945475220449460533

theorem tailTrace_3351762 : CollatzResearch.WordTrace tailWord_3351762 prefixEnd_3351762 1721064945475220449460533 := by
  unfold tailWord_3351762
  simp only [CollatzResearch.WordTrace]
  refine ⟨30562200820786546055200385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81499202188764122813867693 30562200820786546055200385)
  ·
    refine ⟨22921650615589909541400289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 30562200820786546055200385 22921650615589909541400289)
    ·
      refine ⟨17191237961692432156050217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 22921650615589909541400289 17191237961692432156050217)
      ·
        refine ⟨12893428471269324117037663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17191237961692432156050217 12893428471269324117037663)
        ·
          refine ⟨19340142706903986175556495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893428471269324117037663 19340142706903986175556495)
          ·
            refine ⟨29010214060355979263334743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19340142706903986175556495 29010214060355979263334743)
            ·
              refine ⟨43515321090533968895002115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29010214060355979263334743 43515321090533968895002115)
              ·
                refine ⟨65272981635800953342503173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 43515321090533968895002115 65272981635800953342503173)
                ·
                  refine ⟨12238684056712678751719345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 65272981635800953342503173 12238684056712678751719345)
                  ·
                    refine ⟨9179013042534509063789509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12238684056712678751719345 9179013042534509063789509)
                    ·
                      refine ⟨1721064945475220449460533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 9179013042534509063789509 1721064945475220449460533)
                      ·
                        rfl

theorem cell23_3351762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 1, 1, 4, 2, 4].length) (baseStart_3351762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351762 prefixEnd_3351762 := by exact prefixLift 3351762
  have htrace : WordTrace (prefixWord ++ tailWord_3351762) baseStart_3351762 baseEnd_3351762 := by
    simpa [prefixWord, tailWord_3351762, baseEnd_3351762] using wordTrace_append hprefix tailTrace_3351762
  have hstable : (prefixWord ++ tailWord_3351762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351762).length < 2 ^ (prefixWord ++ tailWord_3351762).sum := by decide
  have hdescent : baseEnd_3351762 < baseStart_3351762 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351783 : List Nat := [1, 1, 5, 3, 2, 2, 1, 1, 1, 4, 2]
def baseStart_3351783 : Nat := 118140960795 + 3351783 * 2 ^ 59
def prefixEnd_3351783 : Nat := 4983230072969 + 3 ^ 40 * 3351783 * 2
def baseEnd_3351783 : Nat := 1721075728568964867297937

theorem tailTrace_3351783 : CollatzResearch.WordTrace tailWord_3351783 prefixEnd_3351783 1721075728568964867297937 := by
  unfold tailWord_3351783
  simp only [CollatzResearch.WordTrace]
  refine ⟨122249569216070104807316003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81499712810713403204877335 122249569216070104807316003)
  ·
    refine ⟨183374353824105157210974005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122249569216070104807316003 183374353824105157210974005)
    ·
      refine ⟨17191345671009858488528813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 183374353824105157210974005 17191345671009858488528813)
      ·
        refine ⟨6446754626628696933198305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17191345671009858488528813 6446754626628696933198305)
        ·
          refine ⟨4835065969971522699898729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6446754626628696933198305 4835065969971522699898729)
          ·
            refine ⟨3626299477478642024924047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4835065969971522699898729 3626299477478642024924047)
            ·
              refine ⟨5439449216217963037386071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3626299477478642024924047 5439449216217963037386071)
              ·
                refine ⟨8159173824326944556079107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439449216217963037386071 8159173824326944556079107)
                ·
                  refine ⟨12238760736490416834118661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159173824326944556079107 12238760736490416834118661)
                  ·
                    refine ⟨2294767638091953156397249, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 12238760736490416834118661 2294767638091953156397249)
                    ·
                      refine ⟨1721075728568964867297937, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294767638091953156397249 1721075728568964867297937)
                      ·
                        rfl

theorem cell23_3351783_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_3351783 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351783 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351783 prefixEnd_3351783 := by exact prefixLift 3351783
  have htrace : WordTrace (prefixWord ++ tailWord_3351783) baseStart_3351783 baseEnd_3351783 := by
    simpa [prefixWord, tailWord_3351783, baseEnd_3351783] using wordTrace_append hprefix tailTrace_3351783
  have hstable : (prefixWord ++ tailWord_3351783).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351783).length < 2 ^ (prefixWord ++ tailWord_3351783).sum := by decide
  have hdescent : baseEnd_3351783 < baseStart_3351783 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351783) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351802 : List Nat := [3, 1, 1, 1, 1, 4, 2, 3, 2, 5]
def baseStart_3351802 : Nat := 118140960795 + 3351802 * 2 ^ 59
def prefixEnd_3351802 : Nat := 4983230072969 + 3 ^ 40 * 3351802 * 2
def baseEnd_3351802 : Nat := 573695161567133430986783

theorem tailTrace_3351802 : CollatzResearch.WordTrace tailWord_3351802 prefixEnd_3351802 573695161567133430986783 := by
  unfold tailWord_3351802
  simp only [CollatzResearch.WordTrace]
  refine ⟨30562565550750317763064415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81500174802000847368171773 30562565550750317763064415)
  ·
    refine ⟨45843848326125476644596623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30562565550750317763064415 45843848326125476644596623)
    ·
      refine ⟨68765772489188214966894935, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45843848326125476644596623 68765772489188214966894935)
      ·
        refine ⟨103148658733782322450342403, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68765772489188214966894935 103148658733782322450342403)
        ·
          refine ⟨154722988100673483675513605, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103148658733782322450342403 154722988100673483675513605)
          ·
            refine ⟨29010560268876278189158801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 154722988100673483675513605 29010560268876278189158801)
            ·
              refine ⟨21757920201657208641869101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29010560268876278189158801 21757920201657208641869101)
              ·
                refine ⟨8159220075621453240700913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21757920201657208641869101 8159220075621453240700913)
                ·
                  refine ⟨6119415056716089930525685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8159220075621453240700913 6119415056716089930525685)
                  ·
                    refine ⟨573695161567133430986783, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6119415056716089930525685 573695161567133430986783)
                    ·
                      rfl

theorem cell23_3351802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 4, 2, 3, 2, 5].length) (baseStart_3351802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351802 prefixEnd_3351802 := by exact prefixLift 3351802
  have htrace : WordTrace (prefixWord ++ tailWord_3351802) baseStart_3351802 baseEnd_3351802 := by
    simpa [prefixWord, tailWord_3351802, baseEnd_3351802] using wordTrace_append hprefix tailTrace_3351802
  have hstable : (prefixWord ++ tailWord_3351802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351802).length < 2 ^ (prefixWord ++ tailWord_3351802).sum := by decide
  have hdescent : baseEnd_3351802 < baseStart_3351802 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351806 : List Nat := [4, 2, 2, 1, 1, 2, 3, 3, 5]
def baseStart_3351806 : Nat := 118140960795 + 3351806 * 2 ^ 59
def prefixEnd_3351806 : Nat := 4983230072969 + 3 ^ 40 * 3351806 * 2
def baseEnd_3351806 : Nat := 191231948736002030812259

theorem tailTrace_3351806 : CollatzResearch.WordTrace tailWord_3351806 prefixEnd_3351806 191231948736002030812259 := by
  unfold tailWord_3351806
  simp only [CollatzResearch.WordTrace]
  refine ⟨15281301011873347466925409, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 81500272063324519823602181 15281301011873347466925409)
  ·
    refine ⟨11460975758905010600194057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15281301011873347466925409 11460975758905010600194057)
    ·
      refine ⟨8595731819178757950145543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11460975758905010600194057 8595731819178757950145543)
      ·
        refine ⟨12893597728768136925218315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8595731819178757950145543 12893597728768136925218315)
        ·
          refine ⟨19340396593152205387827473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 12893597728768136925218315 19340396593152205387827473)
          ·
            refine ⟨14505297444864154040870605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19340396593152205387827473 14505297444864154040870605)
            ·
              refine ⟨5439486541824057765326477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14505297444864154040870605 5439486541824057765326477)
              ·
                refine ⟨2039807453184021661997429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439486541824057765326477 2039807453184021661997429)
                ·
                  refine ⟨191231948736002030812259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 2039807453184021661997429 191231948736002030812259)
                  ·
                    rfl

theorem cell23_3351806_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 3, 3, 5].length) (baseStart_3351806 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351806 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351806 prefixEnd_3351806 := by exact prefixLift 3351806
  have htrace : WordTrace (prefixWord ++ tailWord_3351806) baseStart_3351806 baseEnd_3351806 := by
    simpa [prefixWord, tailWord_3351806, baseEnd_3351806] using wordTrace_append hprefix tailTrace_3351806
  have hstable : (prefixWord ++ tailWord_3351806).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351806).length < 2 ^ (prefixWord ++ tailWord_3351806).sum := by decide
  have hdescent : baseEnd_3351806 < baseStart_3351806 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351806) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351859 : List Nat := [1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 3]
def baseStart_3351859 : Nat := 118140960795 + 3351859 * 2 ^ 59
def prefixEnd_3351859 : Nat := 4983230072969 + 3 ^ 40 * 3351859 * 2
def baseEnd_3351859 : Nat := 1721114753098706569947587

theorem tailTrace_3351859 : CollatzResearch.WordTrace tailWord_3351859 prefixEnd_3351859 1721114753098706569947587 := by
  unfold tailWord_3351859
  simp only [CollatzResearch.WordTrace]
  refine ⟨122252341163794769787082631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81501560775863179858055087 122252341163794769787082631)
  ·
    refine ⟨183378511745692154680623947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122252341163794769787082631 183378511745692154680623947)
    ·
      refine ⟨275067767618538232020935921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 183378511745692154680623947 275067767618538232020935921)
      ·
        refine ⟨206300825713903674015701941, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 275067767618538232020935921 206300825713903674015701941)
        ·
          refine ⟨19340702410678469438972057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 206300825713903674015701941 19340702410678469438972057)
          ·
            refine ⟨14505526808008852079229043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19340702410678469438972057 14505526808008852079229043)
            ·
              refine ⟨21758290212013278118843565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14505526808008852079229043 21758290212013278118843565)
              ·
                refine ⟨8159358829504979294566337, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 21758290212013278118843565 8159358829504979294566337)
                ·
                  refine ⟨6119519122128734470924753, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8159358829504979294566337 6119519122128734470924753)
                  ·
                    refine ⟨4589639341596550853193565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6119519122128734470924753 4589639341596550853193565)
                    ·
                      refine ⟨1721114753098706569947587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 4589639341596550853193565 1721114753098706569947587)
                      ·
                        rfl

theorem cell23_3351859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 2, 1, 3, 2, 2, 3].length) (baseStart_3351859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351859 prefixEnd_3351859 := by exact prefixLift 3351859
  have htrace : WordTrace (prefixWord ++ tailWord_3351859) baseStart_3351859 baseEnd_3351859 := by
    simpa [prefixWord, tailWord_3351859, baseEnd_3351859] using wordTrace_append hprefix tailTrace_3351859
  have hstable : (prefixWord ++ tailWord_3351859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351859).length < 2 ^ (prefixWord ++ tailWord_3351859).sum := by decide
  have hdescent : baseEnd_3351859 < baseStart_3351859 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351866 : List Nat := [3, 1, 1, 1, 4, 1, 2, 5, 1, 4]
def baseStart_3351866 : Nat := 118140960795 + 3351866 * 2 ^ 59
def prefixEnd_3351866 : Nat := 4983230072969 + 3 ^ 40 * 3351866 * 2
def baseEnd_3351866 : Nat := 573706115821096014186685

theorem tailTrace_3351866 : CollatzResearch.WordTrace tailWord_3351866 prefixEnd_3351866 573706115821096014186685 := by
  unfold tailWord_3351866
  simp only [CollatzResearch.WordTrace]
  refine ⟨30563149118692352495646863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 81501730983179606655058301 30563149118692352495646863)
  ·
    refine ⟨45844723678038528743470295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 30563149118692352495646863 45844723678038528743470295)
    ·
      refine ⟨68767085517057793115205443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45844723678038528743470295 68767085517057793115205443)
      ·
        refine ⟨103150628275586689672808165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68767085517057793115205443 103150628275586689672808165)
        ·
          refine ⟨19340742801672504313651531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 103150628275586689672808165 19340742801672504313651531)
          ·
            refine ⟨29011114202508756470477297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19340742801672504313651531 29011114202508756470477297)
            ·
              refine ⟨21758335651881567352857973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29011114202508756470477297 21758335651881567352857973)
              ·
                refine ⟨2039843967363896939330435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 21758335651881567352857973 2039843967363896939330435)
                ·
                  refine ⟨3059765951045845408995653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039843967363896939330435 3059765951045845408995653)
                  ·
                    refine ⟨573706115821096014186685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 3059765951045845408995653 573706115821096014186685)
                    ·
                      rfl

theorem cell23_3351866_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 2, 5, 1, 4].length) (baseStart_3351866 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351866 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351866 prefixEnd_3351866 := by exact prefixLift 3351866
  have htrace : WordTrace (prefixWord ++ tailWord_3351866) baseStart_3351866 baseEnd_3351866 := by
    simpa [prefixWord, tailWord_3351866, baseEnd_3351866] using wordTrace_append hprefix tailTrace_3351866
  have hstable : (prefixWord ++ tailWord_3351866).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351866).length < 2 ^ (prefixWord ++ tailWord_3351866).sum := by decide
  have hdescent : baseEnd_3351866 < baseStart_3351866 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351866) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351879 : List Nat := [1, 1, 4, 1, 2, 4, 2, 2, 6]
def baseStart_3351879 : Nat := 118140960795 + 3351879 * 2 ^ 59
def prefixEnd_3351879 : Nat := 4983230072969 + 3 ^ 40 * 3351879 * 2
def baseEnd_3351879 : Nat := 191236113634644054633055

theorem tailTrace_3351879 : CollatzResearch.WordTrace tailWord_3351879 prefixEnd_3351879 191236113634644054633055 := by
  unfold tailWord_3351879
  simp only [CollatzResearch.WordTrace]
  refine ⟨122253070623722313202810691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81502047082481542135207127 122253070623722313202810691)
  ·
    refine ⟨183379605935583469804216037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 122253070623722313202810691 183379605935583469804216037)
    ·
      refine ⟨34383676112921900588290507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 183379605935583469804216037 34383676112921900588290507)
      ·
        refine ⟨51575514169382850882435761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 34383676112921900588290507 51575514169382850882435761)
        ·
          refine ⟨38681635627037138161826821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 51575514169382850882435761 38681635627037138161826821)
          ·
            refine ⟨7252806680069463405342529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 38681635627037138161826821 7252806680069463405342529)
            ·
              refine ⟨5439605010052097554006897, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7252806680069463405342529 5439605010052097554006897)
              ·
                refine ⟨4079703757539073165505173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5439605010052097554006897 4079703757539073165505173)
                ·
                  refine ⟨191236113634644054633055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 4079703757539073165505173 191236113634644054633055)
                  ·
                    rfl

theorem cell23_3351879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 4, 2, 2, 6].length) (baseStart_3351879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351879 prefixEnd_3351879 := by exact prefixLift 3351879
  have htrace : WordTrace (prefixWord ++ tailWord_3351879) baseStart_3351879 baseEnd_3351879 := by
    simpa [prefixWord, tailWord_3351879, baseEnd_3351879] using wordTrace_append hprefix tailTrace_3351879
  have hstable : (prefixWord ++ tailWord_3351879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351879).length < 2 ^ (prefixWord ++ tailWord_3351879).sum := by decide
  have hdescent : baseEnd_3351879 < baseStart_3351879 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351909 : List Nat := [1, 3, 1, 3, 1, 2, 2, 4, 1, 5]
def baseStart_3351909 : Nat := 118140960795 + 3351909 * 2 ^ 59
def prefixEnd_3351909 : Nat := 4983230072969 + 3 ^ 40 * 3351909 * 2
def baseEnd_3351909 : Nat := 573713475710477124774119

theorem tailTrace_3351909 : CollatzResearch.WordTrace tailWord_3351909 prefixEnd_3351909 573713475710477124774119 := by
  unfold tailWord_3351909
  simp only [CollatzResearch.WordTrace]
  refine ⟨122254164813613628326402781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81502776542409085550935187 122254164813613628326402781)
  ·
    refine ⟨45845311805105110622401043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 122254164813613628326402781 45845311805105110622401043)
    ·
      refine ⟨68767967707657665933601565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45845311805105110622401043 68767967707657665933601565)
      ·
        refine ⟨25787987890371624725100587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 68767967707657665933601565 25787987890371624725100587)
        ·
          refine ⟨38681981835557437087650881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25787987890371624725100587 38681981835557437087650881)
          ·
            refine ⟨29011486376668077815738161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38681981835557437087650881 29011486376668077815738161)
            ·
              refine ⟨21758614782501058361803621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29011486376668077815738161 21758614782501058361803621)
              ·
                refine ⟨4079740271718948442838179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 21758614782501058361803621 4079740271718948442838179)
                ·
                  refine ⟨6119610407578422664257269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079740271718948442838179 6119610407578422664257269)
                  ·
                    refine ⟨573713475710477124774119, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 6119610407578422664257269 573713475710477124774119)
                    ·
                      rfl

theorem cell23_3351909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 1, 2, 2, 4, 1, 5].length) (baseStart_3351909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351909 prefixEnd_3351909 := by exact prefixLift 3351909
  have htrace : WordTrace (prefixWord ++ tailWord_3351909) baseStart_3351909 baseEnd_3351909 := by
    simpa [prefixWord, tailWord_3351909, baseEnd_3351909] using wordTrace_append hprefix tailTrace_3351909
  have hstable : (prefixWord ++ tailWord_3351909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351909).length < 2 ^ (prefixWord ++ tailWord_3351909).sum := by decide
  have hdescent : baseEnd_3351909 < baseStart_3351909 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351916 : List Nat := [2, 2, 1, 1, 5, 2, 1, 1, 1, 5, 2]
def baseStart_3351916 : Nat := 118140960795 + 3351916 * 2 ^ 59
def prefixEnd_3351916 : Nat := 4983230072969 + 3 ^ 40 * 3351916 * 2
def baseEnd_3351916 : Nat := 1721144021496012846934825

theorem tailTrace_3351916 : CollatzResearch.WordTrace tailWord_3351916 prefixEnd_3351916 1721144021496012846934825 := by
  unfold tailWord_3351916
  simp only [CollatzResearch.WordTrace]
  refine ⟨61127210062294134260953801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81502946749725512347938401 61127210062294134260953801)
  ·
    refine ⟨45845407546720600695715351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61127210062294134260953801 45845407546720600695715351)
    ·
      refine ⟨68768111320080901043573027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45845407546720600695715351 68768111320080901043573027)
      ·
        refine ⟨103152166980121351565359541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68768111320080901043573027 103152166980121351565359541)
        ·
          refine ⟨9670515654386376709252457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 103152166980121351565359541 9670515654386376709252457)
          ·
            refine ⟨7252886740789782531939343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9670515654386376709252457 7252886740789782531939343)
            ·
              refine ⟨10879330111184673797909015, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7252886740789782531939343 10879330111184673797909015)
              ·
                refine ⟨16318995166777010696863523, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 10879330111184673797909015 16318995166777010696863523)
                ·
                  refine ⟨24478492750165516045295285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16318995166777010696863523 24478492750165516045295285)
                  ·
                    refine ⟨2294858695328017129246433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 24478492750165516045295285 2294858695328017129246433)
                    ·
                      refine ⟨1721144021496012846934825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294858695328017129246433 1721144021496012846934825)
                      ·
                        rfl

theorem cell23_3351916_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 5, 2].length) (baseStart_3351916 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351916 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351916 prefixEnd_3351916 := by exact prefixLift 3351916
  have htrace : WordTrace (prefixWord ++ tailWord_3351916) baseStart_3351916 baseEnd_3351916 := by
    simpa [prefixWord, tailWord_3351916, baseEnd_3351916] using wordTrace_append hprefix tailTrace_3351916
  have hstable : (prefixWord ++ tailWord_3351916).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351916).length < 2 ^ (prefixWord ++ tailWord_3351916).sum := by decide
  have hdescent : baseEnd_3351916 < baseStart_3351916 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351916) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351956 : List Nat := [2, 4, 2, 1, 2, 1, 3, 1, 1, 6]
def baseStart_3351956 : Nat := 118140960795 + 3351956 * 2 ^ 59
def prefixEnd_3351956 : Nat := 4983230072969 + 3 ^ 40 * 3351956 * 2
def baseEnd_3351956 : Nat := 573721520240730896811547

theorem tailTrace_3351956 : CollatzResearch.WordTrace tailWord_3351956 prefixEnd_3351956 573721520240730896811547 := by
  unfold tailWord_3351956
  simp only [CollatzResearch.WordTrace]
  refine ⟨61127939522221677676681861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81503919362962236902242481 61127939522221677676681861)
  ·
    refine ⟨11461488660416564564377849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 61127939522221677676681861 11461488660416564564377849)
    ·
      refine ⟨8596116495312423423283387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11461488660416564564377849 8596116495312423423283387)
      ·
        refine ⟨12894174742968635134925081, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8596116495312423423283387 12894174742968635134925081)
        ·
          refine ⟨9670631057226476351193811, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 12894174742968635134925081 9670631057226476351193811)
          ·
            refine ⟨14505946585839714526790717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9670631057226476351193811 14505946585839714526790717)
            ·
              refine ⟨5439729969689892947546519, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14505946585839714526790717 5439729969689892947546519)
              ·
                refine ⟨8159594954534839421319779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5439729969689892947546519 8159594954534839421319779)
                ·
                  refine ⟨12239392431802259131979669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8159594954534839421319779 12239392431802259131979669)
                  ·
                    refine ⟨573721520240730896811547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 12239392431802259131979669 573721520240730896811547)
                    ·
                      rfl

theorem cell23_3351956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 2, 1, 3, 1, 1, 6].length) (baseStart_3351956 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351956 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351956 prefixEnd_3351956 := by exact prefixLift 3351956
  have htrace : WordTrace (prefixWord ++ tailWord_3351956) baseStart_3351956 baseEnd_3351956 := by
    simpa [prefixWord, tailWord_3351956, baseEnd_3351956] using wordTrace_append hprefix tailTrace_3351956
  have hstable : (prefixWord ++ tailWord_3351956).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351956).length < 2 ^ (prefixWord ++ tailWord_3351956).sum := by decide
  have hdescent : baseEnd_3351956 < baseStart_3351956 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351980 : List Nat := [2, 2, 1, 1, 1, 1, 7, 3, 1, 2, 2]
def baseStart_3351980 : Nat := 118140960795 + 3351980 * 2 ^ 59
def prefixEnd_3351980 : Nat := 4983230072969 + 3 ^ 40 * 3351980 * 2
def baseEnd_3351980 : Nat := 1721176884257900596534531

theorem tailTrace_3351980 : CollatzResearch.WordTrace tailWord_3351980 prefixEnd_3351980 1721176884257900596534531 := by
  unfold tailWord_3351980
  simp only [CollatzResearch.WordTrace]
  refine ⟨61128377198178203726118697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81504502930904271634824929 61128377198178203726118697)
  ·
    refine ⟨45846282898633652794589023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 61128377198178203726118697 45846282898633652794589023)
    ·
      refine ⟨68769424347950479191883535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 45846282898633652794589023 68769424347950479191883535)
      ·
        refine ⟨103154136521925718787825303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 68769424347950479191883535 103154136521925718787825303)
        ·
          refine ⟨154731204782888578181737955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 103154136521925718787825303 154731204782888578181737955)
          ·
            refine ⟨232096807174332867272606933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 154731204782888578181737955 232096807174332867272606933)
            ·
              refine ⟨5439768918148426576701725, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 232096807174332867272606933 5439768918148426576701725)
              ·
                refine ⟨2039913344305659966263147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 5439768918148426576701725 2039913344305659966263147)
                ·
                  refine ⟨3059870016458489949394721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039913344305659966263147 3059870016458489949394721)
                  ·
                    refine ⟨2294902512343867462046041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059870016458489949394721 2294902512343867462046041)
                    ·
                      refine ⟨1721176884257900596534531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294902512343867462046041 1721176884257900596534531)
                      ·
                        rfl

theorem cell23_3351980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 1, 7, 3, 1, 2, 2].length) (baseStart_3351980 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351980 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351980 prefixEnd_3351980 := by exact prefixLift 3351980
  have htrace : WordTrace (prefixWord ++ tailWord_3351980) baseStart_3351980 baseEnd_3351980 := by
    simpa [prefixWord, tailWord_3351980, baseEnd_3351980] using wordTrace_append hprefix tailTrace_3351980
  have hstable : (prefixWord ++ tailWord_3351980).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351980).length < 2 ^ (prefixWord ++ tailWord_3351980).sum := by decide
  have hdescent : baseEnd_3351980 < baseStart_3351980 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3351997 : List Nat := [1, 4, 1, 2, 2, 1, 5, 2, 1, 2, 2]
def baseStart_3351997 : Nat := 118140960795 + 3351997 * 2 ^ 59
def prefixEnd_3351997 : Nat := 4983230072969 + 3 ^ 40 * 3351997 * 2
def baseEnd_3351997 : Nat := 1721185613429027030021953

theorem tailTrace_3351997 : CollatzResearch.WordTrace tailWord_3351997 prefixEnd_3351997 1721185613429027030021953 := by
  unfold tailWord_3351997
  simp only [CollatzResearch.WordTrace]
  refine ⟨122257374437294819355606245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 81504916291529879570404163 122257374437294819355606245)
  ·
    refine ⟨22923257706992778629176171, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 122257374437294819355606245 22923257706992778629176171)
    ·
      refine ⟨34384886560489167943764257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 22923257706992778629176171 34384886560489167943764257)
      ·
        refine ⟨25788664920366875957823193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 34384886560489167943764257 25788664920366875957823193)
        ·
          refine ⟨19341498690275156968367395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 25788664920366875957823193 19341498690275156968367395)
          ·
            refine ⟨29012248035412735452551093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19341498690275156968367395 29012248035412735452551093)
            ·
              refine ⟨2719898253319943948676665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29012248035412735452551093 2719898253319943948676665)
              ·
                refine ⟨2039923689989957961507499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2719898253319943948676665 2039923689989957961507499)
                ·
                  refine ⟨3059885534984936942261249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 2039923689989957961507499 3059885534984936942261249)
                  ·
                    refine ⟨2294914151238702706695937, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 3059885534984936942261249 2294914151238702706695937)
                    ·
                      refine ⟨1721185613429027030021953, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294914151238702706695937 1721185613429027030021953)
                      ·
                        rfl

theorem cell23_3351997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 2, 1, 5, 2, 1, 2, 2].length) (baseStart_3351997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3351997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3351997 prefixEnd_3351997 := by exact prefixLift 3351997
  have htrace : WordTrace (prefixWord ++ tailWord_3351997) baseStart_3351997 baseEnd_3351997 := by
    simpa [prefixWord, tailWord_3351997, baseEnd_3351997] using wordTrace_append hprefix tailTrace_3351997
  have hstable : (prefixWord ++ tailWord_3351997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3351997).length < 2 ^ (prefixWord ++ tailWord_3351997).sum := by decide
  have hdescent : baseEnd_3351997 < baseStart_3351997 := by decide
  rcases family_descends (prefixWord ++ tailWord_3351997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_3352040 : List Nat := [2, 1, 4, 1, 1, 2, 5, 1, 1, 3, 2]
def baseStart_3352040 : Nat := 118140960795 + 3352040 * 2 ^ 59
def prefixEnd_3352040 : Nat := 4983230072969 + 3 ^ 40 * 3352040 * 2
def baseEnd_3352040 : Nat := 1721207693097170361784255

theorem tailTrace_3352040 : CollatzResearch.WordTrace tailWord_3352040 prefixEnd_3352040 1721207693097170361784255 := by
  unfold tailWord_3352040
  simp only [CollatzResearch.WordTrace]
  refine ⟨61129471388069518849710787, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 81505961850759358466281049 61129471388069518849710787)
  ·
    refine ⟨91694207082104278274566181, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 61129471388069518849710787 91694207082104278274566181)
    ·
      refine ⟨17192663827894552176481159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 91694207082104278274566181 17192663827894552176481159)
      ·
        refine ⟨25788995741841828264721739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17192663827894552176481159 25788995741841828264721739)
        ·
          refine ⟨38683493612762742397082609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 25788995741841828264721739 38683493612762742397082609)
          ·
            refine ⟨29012620209572056797811957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 38683493612762742397082609 29012620209572056797811957)
            ·
              refine ⟨2719933144647380324794871, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 29012620209572056797811957 2719933144647380324794871)
              ·
                refine ⟨4079899716971070487192307, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2719933144647380324794871 4079899716971070487192307)
                ·
                  refine ⟨6119849575456605730788461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4079899716971070487192307 6119849575456605730788461)
                  ·
                    refine ⟨2294943590796227149045673, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 6119849575456605730788461 2294943590796227149045673)
                    ·
                      refine ⟨1721207693097170361784255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 2294943590796227149045673 1721207693097170361784255)
                      ·
                        rfl

theorem cell23_3352040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 2, 5, 1, 1, 3, 2].length) (baseStart_3352040 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_3352040 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_3352040 prefixEnd_3352040 := by exact prefixLift 3352040
  have htrace : WordTrace (prefixWord ++ tailWord_3352040) baseStart_3352040 baseEnd_3352040 := by
    simpa [prefixWord, tailWord_3352040, baseEnd_3352040] using wordTrace_append hprefix tailTrace_3352040
  have hstable : (prefixWord ++ tailWord_3352040).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_3352040).length < 2 ^ (prefixWord ++ tailWord_3352040).sum := by decide
  have hdescent : baseEnd_3352040 < baseStart_3352040 := by decide
  rcases family_descends (prefixWord ++ tailWord_3352040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
