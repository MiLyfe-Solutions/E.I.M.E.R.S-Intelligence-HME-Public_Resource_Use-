import V185TrunkScan21Chunk027

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental

namespace V185TrunkScan21Incremental

def tailWord_338206 : List Nat := [4, 3, 2, 1, 1, 1, 1, 5, 3]
def baseStart_338206 : Nat := 118140960795 + 338206 * 2 ^ 59
def prefixEnd_338206 : Nat := 4983230072969 + 3 ^ 40 * 338206 * 2
def baseEnd_338206 : Nat := 77183216993159556075389

theorem tailTrace_338206 : CollatzResearch.WordTrace tailWord_338206 prefixEnd_338206 77183216993159556075389 := by
  unfold tailWord_338206
  simp only [CollatzResearch.WordTrace]
  refine ⟨1541923276593112228915309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8223590808496598554214981 1541923276593112228915309)
  ·
    refine ⟨578221228722417085843241, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1541923276593112228915309 578221228722417085843241)
    ·
      refine ⟨433665921541812814382431, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 578221228722417085843241 433665921541812814382431)
      ·
        refine ⟨650498882312719221573647, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 433665921541812814382431 650498882312719221573647)
        ·
          refine ⟨975748323469078832360471, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650498882312719221573647 975748323469078832360471)
          ·
            refine ⟨1463622485203618248540707, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 975748323469078832360471 1463622485203618248540707)
            ·
              refine ⟨2195433727805427372811061, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1463622485203618248540707 2195433727805427372811061)
              ·
                refine ⟨205821911981758816201037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2195433727805427372811061 205821911981758816201037)
                ·
                  refine ⟨77183216993159556075389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205821911981758816201037 77183216993159556075389)
                  ·
                    rfl

theorem cell21_338206_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 1, 1, 1, 5, 3].length) (baseStart_338206 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338206 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338206 prefixEnd_338206 := by exact prefixLift 338206
  have htrace : WordTrace (prefixWord ++ tailWord_338206) baseStart_338206 baseEnd_338206 := by
    simpa [prefixWord, tailWord_338206, baseEnd_338206] using wordTrace_append hprefix tailTrace_338206
  have hstable : (prefixWord ++ tailWord_338206).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338206).length < 2 ^ (prefixWord ++ tailWord_338206).sum := by decide
  have hdescent : baseEnd_338206 < baseStart_338206 := by decide
  rcases family_descends (prefixWord ++ tailWord_338206) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338282 : List Nat := [3, 1, 3, 3, 1, 2, 3, 2, 3]
def baseStart_338282 : Nat := 118140960795 + 338282 * 2 ^ 59
def prefixEnd_338282 : Nat := 4983230072969 + 3 ^ 40 * 338282 * 2
def baseEnd_338282 : Nat := 77200561228600312808567

theorem tailTrace_338282 : CollatzResearch.WordTrace tailWord_338282 prefixEnd_338282 77200561228600312808567 := by
  unfold tailWord_338282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3084539540117390702772275, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8225438773646375207392733 3084539540117390702772275)
  ·
    refine ⟨4626809310176086054158413, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3084539540117390702772275 4626809310176086054158413)
    ·
      refine ⟨1735053491316032270309405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4626809310176086054158413 1735053491316032270309405)
      ·
        refine ⟨650645059243512101366027, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1735053491316032270309405 650645059243512101366027)
        ·
          refine ⟨975967588865268152049041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 650645059243512101366027 975967588865268152049041)
          ·
            refine ⟨731975691648951114036781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975967588865268152049041 731975691648951114036781)
            ·
              refine ⟨274490884368356667763793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 731975691648951114036781 274490884368356667763793)
              ·
                refine ⟨205868163276267500822845, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 274490884368356667763793 205868163276267500822845)
                ·
                  refine ⟨77200561228600312808567, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 205868163276267500822845 77200561228600312808567)
                  ·
                    rfl

theorem cell21_338282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 1, 2, 3, 2, 3].length) (baseStart_338282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338282 prefixEnd_338282 := by exact prefixLift 338282
  have htrace : WordTrace (prefixWord ++ tailWord_338282) baseStart_338282 baseEnd_338282 := by
    simpa [prefixWord, tailWord_338282, baseEnd_338282] using wordTrace_append hprefix tailTrace_338282
  have hstable : (prefixWord ++ tailWord_338282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338282).length < 2 ^ (prefixWord ++ tailWord_338282).sum := by decide
  have hdescent : baseEnd_338282 < baseStart_338282 := by decide
  rcases family_descends (prefixWord ++ tailWord_338282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338293 : List Nat := [1, 3, 4, 1, 2, 2, 2, 6]
def baseStart_338293 : Nat := 118140960795 + 338293 * 2 ^ 59
def prefixEnd_338293 : Nat := 4983230072969 + 3 ^ 40 * 338293 * 2
def baseEnd_338293 : Nat := 25734357192822246041737

theorem tailTrace_338293 : CollatzResearch.WordTrace tailWord_338293 prefixEnd_338293 25734357192822246041737 := by
  unfold tailWord_338293
  simp only [CollatzResearch.WordTrace]
  refine ⟨12338559363429711689739533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8225706242286474459826355 12338559363429711689739533)
  ·
    refine ⟨4626959761286141883652325, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12338559363429711689739533 4626959761286141883652325)
    ·
      refine ⟨867554955241151603184811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4626959761286141883652325 867554955241151603184811)
      ·
        refine ⟨1301332432861727404777217, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 867554955241151603184811 1301332432861727404777217)
        ·
          refine ⟨975999324646295553582913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1301332432861727404777217 975999324646295553582913)
          ·
            refine ⟨731999493484721665187185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 975999324646295553582913 731999493484721665187185)
            ·
              refine ⟨548999620113541248890389, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 731999493484721665187185 548999620113541248890389)
              ·
                refine ⟨25734357192822246041737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 548999620113541248890389 25734357192822246041737)
                ·
                  rfl

theorem cell21_338293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 2, 2, 6].length) (baseStart_338293 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338293 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338293 prefixEnd_338293 := by exact prefixLift 338293
  have htrace : WordTrace (prefixWord ++ tailWord_338293) baseStart_338293 baseEnd_338293 := by
    simpa [prefixWord, tailWord_338293, baseEnd_338293] using wordTrace_append hprefix tailTrace_338293
  have hstable : (prefixWord ++ tailWord_338293).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338293).length < 2 ^ (prefixWord ++ tailWord_338293).sum := by decide
  have hdescent : baseEnd_338293 < baseStart_338293 := by decide
  rcases family_descends (prefixWord ++ tailWord_338293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338411 : List Nat := [1, 1, 1, 1, 2, 3, 4, 8]
def baseStart_338411 : Nat := 118140960795 + 338411 * 2 ^ 59
def prefixEnd_338411 : Nat := 4983230072969 + 3 ^ 40 * 338411 * 2
def baseEnd_338411 : Nat := 25743333595374918386101

theorem tailTrace_338411 : CollatzResearch.WordTrace tailWord_338411 prefixEnd_338411 25743333595374918386101 := by
  unfold tailWord_338411
  simp only [CollatzResearch.WordTrace]
  refine ⟨12342863177002217842535087, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8228575451334811895023391 12342863177002217842535087)
  ·
    refine ⟨18514294765503326763802631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12342863177002217842535087 18514294765503326763802631)
    ·
      refine ⟨27771442148254990145703947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18514294765503326763802631 27771442148254990145703947)
      ·
        refine ⟨41657163222382485218555921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27771442148254990145703947 41657163222382485218555921)
        ·
          refine ⟨31242872416786863913916941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 41657163222382485218555921 31242872416786863913916941)
          ·
            refine ⟨11716077156295073967718853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 31242872416786863913916941 11716077156295073967718853)
            ·
              refine ⟨2196764466805326368947285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11716077156295073967718853 2196764466805326368947285)
              ·
                refine ⟨25743333595374918386101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2196764466805326368947285 25743333595374918386101)
                ·
                  rfl

theorem cell21_338411_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 4, 8].length) (baseStart_338411 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338411 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338411 prefixEnd_338411 := by exact prefixLift 338411
  have htrace : WordTrace (prefixWord ++ tailWord_338411) baseStart_338411 baseEnd_338411 := by
    simpa [prefixWord, tailWord_338411, baseEnd_338411] using wordTrace_append hprefix tailTrace_338411
  have hstable : (prefixWord ++ tailWord_338411).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338411).length < 2 ^ (prefixWord ++ tailWord_338411).sum := by decide
  have hdescent : baseEnd_338411 < baseStart_338411 := by decide
  rcases family_descends (prefixWord ++ tailWord_338411) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338487 : List Nat := [1, 1, 3, 1, 2, 3, 1, 9]
def baseStart_338487 : Nat := 118140960795 + 338487 * 2 ^ 59
def prefixEnd_338487 : Nat := 4983230072969 + 3 ^ 40 * 338487 * 2
def baseEnd_338487 : Nat := 25749115007188503963827

theorem tailTrace_338487 : CollatzResearch.WordTrace tailWord_338487 prefixEnd_338487 25749115007188503963827 := by
  unfold tailWord_338487
  simp only [CollatzResearch.WordTrace]
  refine ⟨12345635124726882822301715, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8230423416484588548201143 12345635124726882822301715)
  ·
    refine ⟨18518452687090324233452573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12345635124726882822301715 18518452687090324233452573)
    ·
      refine ⟨6944419757658871587544715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18518452687090324233452573 6944419757658871587544715)
      ·
        refine ⟨10416629636488307381317073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6944419757658871587544715 10416629636488307381317073)
        ·
          refine ⟨7812472227366230535987805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10416629636488307381317073 7812472227366230535987805)
          ·
            refine ⟨2929677085262336450995427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7812472227366230535987805 2929677085262336450995427)
            ·
              refine ⟨4394515627893504676493141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2929677085262336450995427 4394515627893504676493141)
              ·
                refine ⟨25749115007188503963827, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4394515627893504676493141 25749115007188503963827)
                ·
                  rfl

theorem cell21_338487_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 3, 1, 9].length) (baseStart_338487 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338487 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338487 prefixEnd_338487 := by exact prefixLift 338487
  have htrace : WordTrace (prefixWord ++ tailWord_338487) baseStart_338487 baseEnd_338487 := by
    simpa [prefixWord, tailWord_338487, baseEnd_338487] using wordTrace_append hprefix tailTrace_338487
  have hstable : (prefixWord ++ tailWord_338487).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338487).length < 2 ^ (prefixWord ++ tailWord_338487).sum := by decide
  have hdescent : baseEnd_338487 < baseStart_338487 := by decide
  rcases family_descends (prefixWord ++ tailWord_338487) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338614 : List Nat := [5, 1, 3, 1, 2, 2, 7]
def baseStart_338614 : Nat := 118140960795 + 338614 * 2 ^ 59
def prefixEnd_338614 : Nat := 4983230072969 + 3 ^ 40 * 338614 * 2
def baseEnd_338614 : Nat := 8586258683537945919395

theorem tailTrace_338614 : CollatzResearch.WordTrace tailWord_338614 prefixEnd_338614 8586258683537945919395 := by
  unfold tailWord_338614
  simp only [CollatzResearch.WordTrace]
  refine ⟨771891699704173969510931, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8233511463511189008116597 771891699704173969510931)
  ·
    refine ⟨1157837549556260954266397, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 771891699704173969510931 1157837549556260954266397)
    ·
      refine ⟨434189081083597857849899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1157837549556260954266397 434189081083597857849899)
      ·
        refine ⟨651283621625396786774849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 434189081083597857849899 651283621625396786774849)
        ·
          refine ⟨488462716219047590081137, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 651283621625396786774849 488462716219047590081137)
          ·
            refine ⟨366347037164285692560853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 488462716219047590081137 366347037164285692560853)
            ·
              refine ⟨8586258683537945919395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 366347037164285692560853 8586258683537945919395)
              ·
                rfl

theorem cell21_338614_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 3, 1, 2, 2, 7].length) (baseStart_338614 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338614 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338614 prefixEnd_338614 := by exact prefixLift 338614
  have htrace : WordTrace (prefixWord ++ tailWord_338614) baseStart_338614 baseEnd_338614 := by
    simpa [prefixWord, tailWord_338614, baseEnd_338614] using wordTrace_append hprefix tailTrace_338614
  have hstable : (prefixWord ++ tailWord_338614).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338614).length < 2 ^ (prefixWord ++ tailWord_338614).sum := by decide
  have hdescent : baseEnd_338614 < baseStart_338614 := by decide
  rcases family_descends (prefixWord ++ tailWord_338614) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338628 : List Nat := [2, 3, 3, 1, 1, 4, 1, 1, 5]
def baseStart_338628 : Nat := 118140960795 + 338628 * 2 ^ 59
def prefixEnd_338628 : Nat := 4983230072969 + 3 ^ 40 * 338628 * 2
def baseEnd_338628 : Nat := 77279523142580600041193

theorem tailTrace_338628 : CollatzResearch.WordTrace tailWord_338628 prefixEnd_338628 77279523142580600041193 := by
  unfold tailWord_338628
  simp only [CollatzResearch.WordTrace]
  refine ⟨6175388908608031951592269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8233851878144042602123025 6175388908608031951592269)
  ·
    refine ⟨2315770840728011981847101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6175388908608031951592269 2315770840728011981847101)
    ·
      refine ⟨868414065273004493192663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2315770840728011981847101 868414065273004493192663)
      ·
        refine ⟨1302621097909506739788995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 868414065273004493192663 1302621097909506739788995)
        ·
          refine ⟨1953931646864260109683493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1302621097909506739788995 1953931646864260109683493)
          ·
            refine ⟨366362183787048770565655, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1953931646864260109683493 366362183787048770565655)
            ·
              refine ⟨549543275680573155848483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 366362183787048770565655 549543275680573155848483)
              ·
                refine ⟨824314913520859733772725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 549543275680573155848483 824314913520859733772725)
                ·
                  refine ⟨77279523142580600041193, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 824314913520859733772725 77279523142580600041193)
                  ·
                    rfl

theorem cell21_338628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 4, 1, 1, 5].length) (baseStart_338628 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338628 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338628 prefixEnd_338628 := by exact prefixLift 338628
  have htrace : WordTrace (prefixWord ++ tailWord_338628) baseStart_338628 baseEnd_338628 := by
    simpa [prefixWord, tailWord_338628, baseEnd_338628] using wordTrace_append hprefix tailTrace_338628
  have hstable : (prefixWord ++ tailWord_338628).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338628).length < 2 ^ (prefixWord ++ tailWord_338628).sum := by decide
  have hdescent : baseEnd_338628 < baseStart_338628 := by decide
  rcases family_descends (prefixWord ++ tailWord_338628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338791 : List Nat := [1, 1, 5, 1, 2, 2, 9]
def baseStart_338791 : Nat := 118140960795 + 338791 * 2 ^ 59
def prefixEnd_338791 : Nat := 4983230072969 + 3 ^ 40 * 338791 * 2
def baseEnd_338791 : Nat := 8590746884814282091577

theorem tailTrace_338791 : CollatzResearch.WordTrace tailWord_338791 prefixEnd_338791 8590746884814282091577 := by
  unfold tailWord_338791
  simp only [CollatzResearch.WordTrace]
  refine ⟨12356722915625542741368227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8237815277083695160912151 12356722915625542741368227)
  ·
    refine ⟨18535084373438314112052341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12356722915625542741368227 18535084373438314112052341)
    ·
      refine ⟨1737664160009841948004907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18535084373438314112052341 1737664160009841948004907)
      ·
        refine ⟨2606496240014762922007361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1737664160009841948004907 2606496240014762922007361)
        ·
          refine ⟨1954872180011072191505521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2606496240014762922007361 1954872180011072191505521)
          ·
            refine ⟨1466154135008304143629141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1954872180011072191505521 1466154135008304143629141)
            ·
              refine ⟨8590746884814282091577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1466154135008304143629141 8590746884814282091577)
              ·
                rfl

theorem cell21_338791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 9].length) (baseStart_338791 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338791 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338791 prefixEnd_338791 := by exact prefixLift 338791
  have htrace : WordTrace (prefixWord ++ tailWord_338791) baseStart_338791 baseEnd_338791 := by
    simpa [prefixWord, tailWord_338791, baseEnd_338791] using wordTrace_append hprefix tailTrace_338791
  have hstable : (prefixWord ++ tailWord_338791).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338791).length < 2 ^ (prefixWord ++ tailWord_338791).sum := by decide
  have hdescent : baseEnd_338791 < baseStart_338791 := by decide
  rcases family_descends (prefixWord ++ tailWord_338791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338839 : List Nat := [1, 1, 3, 3, 1, 2, 2, 5, 3]
def baseStart_338839 : Nat := 118140960795 + 338839 * 2 ^ 59
def prefixEnd_338839 : Nat := 4983230072969 + 3 ^ 40 * 338839 * 2
def baseEnd_338839 : Nat := 77327676217291122024095

theorem tailTrace_338839 : CollatzResearch.WordTrace tailWord_338839 prefixEnd_338839 77327676217291122024095 := by
  unfold tailWord_338839
  simp only [CollatzResearch.WordTrace]
  refine ⟨12358473619451646939115571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8238982412967764626077047 12358473619451646939115571)
  ·
    refine ⟨18537710429177470408673357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12358473619451646939115571 18537710429177470408673357)
    ·
      refine ⟨6951641410941551403252509, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18537710429177470408673357 6951641410941551403252509)
      ·
        refine ⟨2606865529103081776219691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6951641410941551403252509 2606865529103081776219691)
        ·
          refine ⟨3910298293654622664329537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2606865529103081776219691 3910298293654622664329537)
          ·
            refine ⟨2932723720240966998247153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3910298293654622664329537 2932723720240966998247153)
            ·
              refine ⟨2199542790180725248685365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2932723720240966998247153 2199542790180725248685365)
              ·
                refine ⟨206207136579442992064253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2199542790180725248685365 206207136579442992064253)
                ·
                  refine ⟨77327676217291122024095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206207136579442992064253 77327676217291122024095)
                  ·
                    rfl

theorem cell21_338839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 1, 2, 2, 5, 3].length) (baseStart_338839 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338839 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338839 prefixEnd_338839 := by exact prefixLift 338839
  have htrace : WordTrace (prefixWord ++ tailWord_338839) baseStart_338839 baseEnd_338839 := by
    simpa [prefixWord, tailWord_338839, baseEnd_338839] using wordTrace_append hprefix tailTrace_338839
  have hstable : (prefixWord ++ tailWord_338839).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338839).length < 2 ^ (prefixWord ++ tailWord_338839).sum := by decide
  have hdescent : baseEnd_338839 < baseStart_338839 := by decide
  rcases family_descends (prefixWord ++ tailWord_338839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_338915 : List Nat := [1, 1, 1, 6, 1, 1, 1, 6, 3]
def baseStart_338915 : Nat := 118140960795 + 338915 * 2 ^ 59
def prefixEnd_338915 : Nat := 4983230072969 + 3 ^ 40 * 338915 * 2
def baseEnd_338915 : Nat := 77345020452731878757273

theorem tailTrace_338915 : CollatzResearch.WordTrace tailWord_338915 prefixEnd_338915 77345020452731878757273 := by
  unfold tailWord_338915
  simp only [CollatzResearch.WordTrace]
  refine ⟨12361245567176311918882199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8240830378117541279254799 12361245567176311918882199)
  ·
    refine ⟨18541868350764467878323299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12361245567176311918882199 18541868350764467878323299)
    ·
      refine ⟨27812802526146701817484949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18541868350764467878323299 27812802526146701817484949)
      ·
        refine ⟨1303725118413126647694607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 27812802526146701817484949 1303725118413126647694607)
        ·
          refine ⟨1955587677619689971541911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1303725118413126647694607 1955587677619689971541911)
          ·
            refine ⟨2933381516429534957312867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1955587677619689971541911 2933381516429534957312867)
            ·
              refine ⟨4400072274644302435969301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2933381516429534957312867 4400072274644302435969301)
              ·
                refine ⟨206253387873951676686061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4400072274644302435969301 206253387873951676686061)
                ·
                  refine ⟨77345020452731878757273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206253387873951676686061 77345020452731878757273)
                  ·
                    rfl

theorem cell21_338915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 1, 1, 6, 3].length) (baseStart_338915 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_338915 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_338915 prefixEnd_338915 := by exact prefixLift 338915
  have htrace : WordTrace (prefixWord ++ tailWord_338915) baseStart_338915 baseEnd_338915 := by
    simpa [prefixWord, tailWord_338915, baseEnd_338915] using wordTrace_append hprefix tailTrace_338915
  have hstable : (prefixWord ++ tailWord_338915).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_338915).length < 2 ^ (prefixWord ++ tailWord_338915).sum := by decide
  have hdescent : baseEnd_338915 < baseStart_338915 := by decide
  rcases family_descends (prefixWord ++ tailWord_338915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339050 : List Nat := [3, 1, 3, 2, 2, 1, 1, 1, 7]
def baseStart_339050 : Nat := 118140960795 + 339050 * 2 ^ 59
def prefixEnd_339050 : Nat := 4983230072969 + 3 ^ 40 * 339050 * 2
def baseEnd_339050 : Nat := 77375829292001644006997

theorem tailTrace_339050 : CollatzResearch.WordTrace tailWord_339050 prefixEnd_339050 77375829292001644006997 := by
  unfold tailWord_339050
  simp only [CollatzResearch.WordTrace]
  refine ⟨3091542355421807493761651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8244112947791486650031069 3091542355421807493761651)
  ·
    refine ⟨4637313533132711240642477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3091542355421807493761651 4637313533132711240642477)
    ·
      refine ⟨1738992574924766715240929, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4637313533132711240642477 1738992574924766715240929)
      ·
        refine ⟨1304244431193575036430697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1738992574924766715240929 1304244431193575036430697)
        ·
          refine ⟨978183323395181277323023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1304244431193575036430697 978183323395181277323023)
          ·
            refine ⟨1467274985092771915984535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 978183323395181277323023 1467274985092771915984535)
            ·
              refine ⟨2200912477639157873976803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1467274985092771915984535 2200912477639157873976803)
              ·
                refine ⟨3301368716458736810965205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2200912477639157873976803 3301368716458736810965205)
                ·
                  refine ⟨77375829292001644006997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3301368716458736810965205 77375829292001644006997)
                  ·
                    rfl

theorem cell21_339050_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 1, 1, 1, 7].length) (baseStart_339050 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339050 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339050 prefixEnd_339050 := by exact prefixLift 339050
  have htrace : WordTrace (prefixWord ++ tailWord_339050) baseStart_339050 baseEnd_339050 := by
    simpa [prefixWord, tailWord_339050, baseEnd_339050] using wordTrace_append hprefix tailTrace_339050
  have hstable : (prefixWord ++ tailWord_339050).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339050).length < 2 ^ (prefixWord ++ tailWord_339050).sum := by decide
  have hdescent : baseEnd_339050 < baseStart_339050 := by decide
  rcases family_descends (prefixWord ++ tailWord_339050) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339070 : List Nat := [4, 2, 4, 1, 1, 1, 8]
def baseStart_339070 : Nat := 118140960795 + 339070 * 2 ^ 59
def prefixEnd_339070 : Nat := 4983230072969 + 3 ^ 40 * 339070 * 2
def baseEnd_339070 : Nat := 8597821507165117074847

theorem tailTrace_339070 : CollatzResearch.WordTrace tailWord_339070 prefixEnd_339070 8597821507165117074847 := by
  unfold tailWord_339070
  simp only [CollatzResearch.WordTrace]
  refine ⟨1545862360201846673846833, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8244599254409848927183109 1545862360201846673846833)
  ·
    refine ⟨1159396770151385005385125, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1545862360201846673846833 1159396770151385005385125)
    ·
      refine ⟨217386894403384688509711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1159396770151385005385125 217386894403384688509711)
      ·
        refine ⟨326080341605077032764567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 217386894403384688509711 326080341605077032764567)
        ·
          refine ⟨489120512407615549146851, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326080341605077032764567 489120512407615549146851)
          ·
            refine ⟨733680768611423323720277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 489120512407615549146851 733680768611423323720277)
            ·
              refine ⟨8597821507165117074847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 733680768611423323720277 8597821507165117074847)
              ·
                rfl

theorem cell21_339070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 4, 1, 1, 1, 8].length) (baseStart_339070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339070 prefixEnd_339070 := by exact prefixLift 339070
  have htrace : WordTrace (prefixWord ++ tailWord_339070) baseStart_339070 baseEnd_339070 := by
    simpa [prefixWord, tailWord_339070, baseEnd_339070] using wordTrace_append hprefix tailTrace_339070
  have hstable : (prefixWord ++ tailWord_339070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339070).length < 2 ^ (prefixWord ++ tailWord_339070).sum := by decide
  have hdescent : baseEnd_339070 < baseStart_339070 := by decide
  rcases family_descends (prefixWord ++ tailWord_339070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339081 : List Nat := [1, 2, 1, 1, 4, 3, 3, 2, 4]
def baseStart_339081 : Nat := 118140960795 + 339081 * 2 ^ 59
def prefixEnd_339081 : Nat := 4983230072969 + 3 ^ 40 * 339081 * 2
def baseEnd_339081 : Nat := 77382903914352478990267

theorem tailTrace_339081 : CollatzResearch.WordTrace tailWord_339081 prefixEnd_339081 77382903914352478990267 := by
  unfold tailWord_339081
  simp only [CollatzResearch.WordTrace]
  refine ⟨12367300084574922269425097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8244866723049948179616731 12367300084574922269425097)
  ·
    refine ⟨9275475063431191702068823, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12367300084574922269425097 9275475063431191702068823)
    ·
      refine ⟨13913212595146787553103235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9275475063431191702068823 13913212595146787553103235)
      ·
        refine ⟨20869818892720181329654853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13913212595146787553103235 20869818892720181329654853)
        ·
          refine ⟨3913091042385033999310285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20869818892720181329654853 3913091042385033999310285)
          ·
            refine ⟨1467409140894387749741357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3913091042385033999310285 1467409140894387749741357)
            ·
              refine ⟨550278427835395406153009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1467409140894387749741357 550278427835395406153009)
              ·
                refine ⟨412708820876546554614757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550278427835395406153009 412708820876546554614757)
                ·
                  refine ⟨77382903914352478990267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412708820876546554614757 77382903914352478990267)
                  ·
                    rfl

theorem cell21_339081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 3, 2, 4].length) (baseStart_339081 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339081 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339081 prefixEnd_339081 := by exact prefixLift 339081
  have htrace : WordTrace (prefixWord ++ tailWord_339081) baseStart_339081 baseEnd_339081 := by
    simpa [prefixWord, tailWord_339081, baseEnd_339081] using wordTrace_append hprefix tailTrace_339081
  have hstable : (prefixWord ++ tailWord_339081).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339081).length < 2 ^ (prefixWord ++ tailWord_339081).sum := by decide
  have hdescent : baseEnd_339081 < baseStart_339081 := by decide
  rcases family_descends (prefixWord ++ tailWord_339081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339149 : List Nat := [1, 6, 2, 2, 1, 2, 2, 1, 4]
def baseStart_339149 : Nat := 118140960795 + 339149 * 2 ^ 59
def prefixEnd_339149 : Nat := 4983230072969 + 3 ^ 40 * 339149 * 2
def baseEnd_339149 : Nat := 77398422440799471856795

theorem tailTrace_339149 : CollatzResearch.WordTrace tailWord_339149 prefixEnd_339149 77398422440799471856795 := by
  unfold tailWord_339149
  simp only [CollatzResearch.WordTrace]
  refine ⟨12369780248328569882900501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8246520165552379921933667 12369780248328569882900501)
  ·
    refine ⟨579833449140401713260961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12369780248328569882900501 579833449140401713260961)
    ·
      refine ⟨434875086855301284945721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 579833449140401713260961 434875086855301284945721)
      ·
        refine ⟨326156315141475963709291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 434875086855301284945721 326156315141475963709291)
        ·
          refine ⟨489234472712213945563937, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 326156315141475963709291 489234472712213945563937)
          ·
            refine ⟨366925854534160459172953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 489234472712213945563937 366925854534160459172953)
            ·
              refine ⟨275194390900620344379715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 366925854534160459172953 275194390900620344379715)
              ·
                refine ⟨412791586350930516569573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275194390900620344379715 412791586350930516569573)
                ·
                  refine ⟨77398422440799471856795, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412791586350930516569573 77398422440799471856795)
                  ·
                    rfl

theorem cell21_339149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 2, 1, 2, 2, 1, 4].length) (baseStart_339149 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339149 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339149 prefixEnd_339149 := by exact prefixLift 339149
  have htrace : WordTrace (prefixWord ++ tailWord_339149) baseStart_339149 baseEnd_339149 := by
    simpa [prefixWord, tailWord_339149, baseEnd_339149] using wordTrace_append hprefix tailTrace_339149
  have hstable : (prefixWord ++ tailWord_339149).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339149).length < 2 ^ (prefixWord ++ tailWord_339149).sum := by decide
  have hdescent : baseEnd_339149 < baseStart_339149 := by decide
  rcases family_descends (prefixWord ++ tailWord_339149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339250 : List Nat := [3, 2, 1, 1, 4, 3, 1, 2, 4]
def baseStart_339250 : Nat := 118140960795 + 339250 * 2 ^ 59
def prefixEnd_339250 : Nat := 4983230072969 + 3 ^ 40 * 339250 * 2
def baseEnd_339250 : Nat := 77421472016845740673255

theorem tailTrace_339250 : CollatzResearch.WordTrace tailWord_339250 prefixEnd_339250 77421472016845740673255 := by
  unfold tailWord_339250
  simp only [CollatzResearch.WordTrace]
  refine ⟨3093366005240666033081801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8248976013975109421551469 3093366005240666033081801)
  ·
    refine ⟨2320024503930499524811351, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3093366005240666033081801 2320024503930499524811351)
    ·
      refine ⟨3480036755895749287217027, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2320024503930499524811351 3480036755895749287217027)
      ·
        refine ⟨5220055133843623930825541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3480036755895749287217027 5220055133843623930825541)
        ·
          refine ⟨978760337595679487029789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5220055133843623930825541 978760337595679487029789)
          ·
            refine ⟨367035126598379807636171, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 978760337595679487029789 367035126598379807636171)
            ·
              refine ⟨550552689897569711454257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367035126598379807636171 550552689897569711454257)
              ·
                refine ⟨412914517423177283590693, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 550552689897569711454257 412914517423177283590693)
                ·
                  refine ⟨77421472016845740673255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 412914517423177283590693 77421472016845740673255)
                  ·
                    rfl

theorem cell21_339250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 4, 3, 1, 2, 4].length) (baseStart_339250 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339250 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339250 prefixEnd_339250 := by exact prefixLift 339250
  have htrace : WordTrace (prefixWord ++ tailWord_339250) baseStart_339250 baseEnd_339250 := by
    simpa [prefixWord, tailWord_339250, baseEnd_339250] using wordTrace_append hprefix tailTrace_339250
  have hstable : (prefixWord ++ tailWord_339250).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339250).length < 2 ^ (prefixWord ++ tailWord_339250).sum := by decide
  have hdescent : baseEnd_339250 < baseStart_339250 := by decide
  rcases family_descends (prefixWord ++ tailWord_339250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339399 : List Nat := [1, 1, 4, 1, 1, 3, 5, 5]
def baseStart_339399 : Nat := 118140960795 + 339399 * 2 ^ 59
def prefixEnd_339399 : Nat := 4983230072969 + 3 ^ 40 * 339399 * 2
def baseEnd_339399 : Nat := 25818491948951530896539

theorem tailTrace_339399 : CollatzResearch.WordTrace tailWord_339399 prefixEnd_339399 25818491948951530896539 := by
  unfold tailWord_339399
  simp only [CollatzResearch.WordTrace]
  refine ⟨12378898497422862579501251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8252598998281908386334167 12378898497422862579501251)
  ·
    refine ⟨18568347746134293869251877, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12378898497422862579501251 18568347746134293869251877)
    ·
      refine ⟨3481565202400180100484727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18568347746134293869251877 3481565202400180100484727)
      ·
        refine ⟨5222347803600270150727091, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3481565202400180100484727 5222347803600270150727091)
        ·
          refine ⟨7833521705400405226090637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5222347803600270150727091 7833521705400405226090637)
          ·
            refine ⟨2937570639525151959783989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 7833521705400405226090637 2937570639525151959783989)
            ·
              refine ⟨275397247455482996229749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2937570639525151959783989 275397247455482996229749)
              ·
                refine ⟨25818491948951530896539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275397247455482996229749 25818491948951530896539)
                ·
                  rfl

theorem cell21_339399_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 3, 5, 5].length) (baseStart_339399 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339399 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339399 prefixEnd_339399 := by exact prefixLift 339399
  have htrace : WordTrace (prefixWord ++ tailWord_339399) baseStart_339399 baseEnd_339399 := by
    simpa [prefixWord, tailWord_339399, baseEnd_339399] using wordTrace_append hprefix tailTrace_339399
  have hstable : (prefixWord ++ tailWord_339399).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339399).length < 2 ^ (prefixWord ++ tailWord_339399).sum := by decide
  have hdescent : baseEnd_339399 < baseStart_339399 := by decide
  rcases family_descends (prefixWord ++ tailWord_339399) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339413 : List Nat := [1, 3, 2, 3, 1, 1, 1, 2, 7]
def baseStart_339413 : Nat := 118140960795 + 339413 * 2 ^ 59
def prefixEnd_339413 : Nat := 4983230072969 + 3 ^ 40 * 339413 * 2
def baseEnd_339413 : Nat := 77458670837593679456255

theorem tailTrace_339413 : CollatzResearch.WordTrace tailWord_339413 prefixEnd_339413 77458670837593679456255 := by
  unfold tailWord_339413
  simp only [CollatzResearch.WordTrace]
  refine ⟨12379409119372142970510893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8252939412914761980340595 12379409119372142970510893)
  ·
    refine ⟨4642278419764553613941585, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12379409119372142970510893 4642278419764553613941585)
    ·
      refine ⟨3481708814823415210456189, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4642278419764553613941585 3481708814823415210456189)
      ·
        refine ⟨1305640805558780703921071, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3481708814823415210456189 1305640805558780703921071)
        ·
          refine ⟨1958461208338171055881607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1305640805558780703921071 1958461208338171055881607)
          ·
            refine ⟨2937691812507256583822411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1958461208338171055881607 2937691812507256583822411)
            ·
              refine ⟨4406537718760884875733617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2937691812507256583822411 4406537718760884875733617)
              ·
                refine ⟨3304903289070663656800213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4406537718760884875733617 3304903289070663656800213)
                ·
                  refine ⟨77458670837593679456255, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3304903289070663656800213 77458670837593679456255)
                  ·
                    rfl

theorem cell21_339413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 1, 1, 1, 2, 7].length) (baseStart_339413 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339413 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339413 prefixEnd_339413 := by exact prefixLift 339413
  have htrace : WordTrace (prefixWord ++ tailWord_339413) baseStart_339413 baseEnd_339413 := by
    simpa [prefixWord, tailWord_339413, baseEnd_339413] using wordTrace_append hprefix tailTrace_339413
  have hstable : (prefixWord ++ tailWord_339413).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339413).length < 2 ^ (prefixWord ++ tailWord_339413).sum := by decide
  have hdescent : baseEnd_339413 < baseStart_339413 := by decide
  rcases family_descends (prefixWord ++ tailWord_339413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339579 : List Nat := [1, 1, 1, 1, 1, 4, 4, 2, 6]
def baseStart_339579 : Nat := 118140960795 + 339579 * 2 ^ 59
def prefixEnd_339579 : Nat := 4983230072969 + 3 ^ 40 * 339579 * 2
def baseEnd_339579 : Nat := 77496554299214279689249

theorem tailTrace_339579 : CollatzResearch.WordTrace tailWord_339579 prefixEnd_339579 77496554299214279689249 := by
  unfold tailWord_339579
  simp only [CollatzResearch.WordTrace]
  refine ⟨12385463636770753321053791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8256975757847168880702527 12385463636770753321053791)
  ·
    refine ⟨18578195455156129981580687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12385463636770753321053791 18578195455156129981580687)
    ·
      refine ⟨27867293182734194972371031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18578195455156129981580687 27867293182734194972371031)
      ·
        refine ⟨41800939774101292458556547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27867293182734194972371031 41800939774101292458556547)
        ·
          refine ⟨62701409661151938687834821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 41800939774101292458556547 62701409661151938687834821)
          ·
            refine ⟨11756514311465988503969029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 62701409661151938687834821 11756514311465988503969029)
            ·
              refine ⟨2204346433399872844494193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 11756514311465988503969029 2204346433399872844494193)
              ·
                refine ⟨1653259825049904633370645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2204346433399872844494193 1653259825049904633370645)
                ·
                  refine ⟨77496554299214279689249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1653259825049904633370645 77496554299214279689249)
                  ·
                    rfl

theorem cell21_339579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 4, 4, 2, 6].length) (baseStart_339579 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339579 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339579 prefixEnd_339579 := by exact prefixLift 339579
  have htrace : WordTrace (prefixWord ++ tailWord_339579) baseStart_339579 baseEnd_339579 := by
    simpa [prefixWord, tailWord_339579, baseEnd_339579] using wordTrace_append hprefix tailTrace_339579
  have hstable : (prefixWord ++ tailWord_339579).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339579).length < 2 ^ (prefixWord ++ tailWord_339579).sum := by decide
  have hdescent : baseEnd_339579 < baseStart_339579 := by decide
  rcases family_descends (prefixWord ++ tailWord_339579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339650 : List Nat := [3, 5, 1, 2, 2, 1, 1, 1, 5]
def baseStart_339650 : Nat := 118140960795 + 339650 * 2 ^ 59
def prefixEnd_339650 : Nat := 4983230072969 + 3 ^ 40 * 339650 * 2
def baseEnd_339650 : Nat := 77512757466533934005771

theorem tailTrace_339650 : CollatzResearch.WordTrace tailWord_339650 prefixEnd_339650 77512757466533934005771 := by
  unfold tailWord_339650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3097013304878383111722101, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8258702146342354964592269 3097013304878383111722101)
  ·
    refine ⟨290344997332348416723947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 3097013304878383111722101 290344997332348416723947)
    ·
      refine ⟨435517495998522625085921, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 290344997332348416723947 435517495998522625085921)
      ·
        refine ⟨326638121998891968814441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 435517495998522625085921 326638121998891968814441)
        ·
          refine ⟨244978591499168976610831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 326638121998891968814441 244978591499168976610831)
          ·
            refine ⟨367467887248753464916247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 244978591499168976610831 367467887248753464916247)
            ·
              refine ⟨551201830873130197374371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 367467887248753464916247 551201830873130197374371)
              ·
                refine ⟨826802746309695296061557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 551201830873130197374371 826802746309695296061557)
                ·
                  refine ⟨77512757466533934005771, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 826802746309695296061557 77512757466533934005771)
                  ·
                    rfl

theorem cell21_339650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 2, 1, 1, 1, 5].length) (baseStart_339650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339650 prefixEnd_339650 := by exact prefixLift 339650
  have htrace : WordTrace (prefixWord ++ tailWord_339650) baseStart_339650 baseEnd_339650 := by
    simpa [prefixWord, tailWord_339650, baseEnd_339650] using wordTrace_append hprefix tailTrace_339650
  have hstable : (prefixWord ++ tailWord_339650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339650).length < 2 ^ (prefixWord ++ tailWord_339650).sum := by decide
  have hdescent : baseEnd_339650 < baseStart_339650 := by decide
  rcases family_descends (prefixWord ++ tailWord_339650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339655 : List Nat := [1, 1, 4, 1, 1, 1, 3, 3, 6]
def baseStart_339655 : Nat := 118140960795 + 339655 * 2 ^ 59
def prefixEnd_339655 : Nat := 4983230072969 + 3 ^ 40 * 339655 * 2
def baseEnd_339655 : Nat := 77513898534655036422427

theorem tailTrace_339655 : CollatzResearch.WordTrace tailWord_339655 prefixEnd_339655 77513898534655036422427 := by
  unfold tailWord_339655
  simp only [CollatzResearch.WordTrace]
  refine ⟨12388235584495418300820419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8258823722996945533880279 12388235584495418300820419)
  ·
    refine ⟨18582353376743127451230629, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12388235584495418300820419 18582353376743127451230629)
    ·
      refine ⟨3484191258139336397105743, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18582353376743127451230629 3484191258139336397105743)
      ·
        refine ⟨5226286887209004595658615, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3484191258139336397105743 5226286887209004595658615)
        ·
          refine ⟨7839430330813506893487923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5226286887209004595658615 7839430330813506893487923)
          ·
            refine ⟨11759145496220260340231885, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7839430330813506893487923 11759145496220260340231885)
            ·
              refine ⟨4409679561082597627586957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 11759145496220260340231885 4409679561082597627586957)
              ·
                refine ⟨1653629835405974110345109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4409679561082597627586957 1653629835405974110345109)
                ·
                  refine ⟨77513898534655036422427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1653629835405974110345109 77513898534655036422427)
                  ·
                    rfl

theorem cell21_339655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 3, 3, 6].length) (baseStart_339655 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339655 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339655 prefixEnd_339655 := by exact prefixLift 339655
  have htrace : WordTrace (prefixWord ++ tailWord_339655) baseStart_339655 baseEnd_339655 := by
    simpa [prefixWord, tailWord_339655, baseEnd_339655] using wordTrace_append hprefix tailTrace_339655
  have hstable : (prefixWord ++ tailWord_339655).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339655).length < 2 ^ (prefixWord ++ tailWord_339655).sum := by decide
  have hdescent : baseEnd_339655 < baseStart_339655 := by decide
  rcases family_descends (prefixWord ++ tailWord_339655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339672 : List Nat := [2, 1, 2, 2, 3, 1, 3, 3, 4]
def baseStart_339672 : Nat := 118140960795 + 339672 * 2 ^ 59
def prefixEnd_339672 : Nat := 4983230072969 + 3 ^ 40 * 339672 * 2
def baseEnd_339672 : Nat := 77517778166266784639059

theorem tailTrace_339672 : CollatzResearch.WordTrace tailWord_339672 prefixEnd_339672 77517778166266784639059 := by
  unfold tailWord_339672
  simp only [CollatzResearch.WordTrace]
  refine ⟨6194427812716915102094635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8259237083622553469459513 6194427812716915102094635)
  ·
    refine ⟨9291641719075372653141953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6194427812716915102094635 9291641719075372653141953)
    ·
      refine ⟨6968731289306529489856465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9291641719075372653141953 6968731289306529489856465)
      ·
        refine ⟨5226548466979897117392349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6968731289306529489856465 5226548466979897117392349)
        ·
          refine ⟨1959955675117461419022131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5226548466979897117392349 1959955675117461419022131)
          ·
            refine ⟨2939933512676192128533197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1959955675117461419022131 2939933512676192128533197)
            ·
              refine ⟨1102475067253572048199949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2939933512676192128533197 1102475067253572048199949)
              ·
                refine ⟨413428150220089518074981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1102475067253572048199949 413428150220089518074981)
                ·
                  refine ⟨77517778166266784639059, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 413428150220089518074981 77517778166266784639059)
                  ·
                    rfl

theorem cell21_339672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 3, 1, 3, 3, 4].length) (baseStart_339672 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339672 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339672 prefixEnd_339672 := by exact prefixLift 339672
  have htrace : WordTrace (prefixWord ++ tailWord_339672) baseStart_339672 baseEnd_339672 := by
    simpa [prefixWord, tailWord_339672, baseEnd_339672] using wordTrace_append hprefix tailTrace_339672
  have hstable : (prefixWord ++ tailWord_339672).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339672).length < 2 ^ (prefixWord ++ tailWord_339672).sum := by decide
  have hdescent : baseEnd_339672 < baseStart_339672 := by decide
  rcases family_descends (prefixWord ++ tailWord_339672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339762 : List Nat := [3, 2, 1, 1, 3, 3, 8]
def baseStart_339762 : Nat := 118140960795 + 339762 * 2 ^ 59
def prefixEnd_339762 : Nat := 4983230072969 + 3 ^ 40 * 339762 * 2
def baseEnd_339762 : Nat := 8615368599160736459875

theorem tailTrace_339762 : CollatzResearch.WordTrace tailWord_339762 prefixEnd_339762 8615368599160736459875 := by
  unfold tailWord_339762
  simp only [CollatzResearch.WordTrace]
  refine ⟨3098034548776943893741385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8261425463405183716643693 3098034548776943893741385)
  ·
    refine ⟨2323525911582707920306039, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3098034548776943893741385 2323525911582707920306039)
    ·
      refine ⟨3485288867374061880459059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2323525911582707920306039 3485288867374061880459059)
      ·
        refine ⟨5227933301061092820688589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3485288867374061880459059 5227933301061092820688589)
        ·
          refine ⟨1960474987897909807758221, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5227933301061092820688589 1960474987897909807758221)
          ·
            refine ⟨735178120461716177909333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1960474987897909807758221 735178120461716177909333)
            ·
              refine ⟨8615368599160736459875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 735178120461716177909333 8615368599160736459875)
              ·
                rfl

theorem cell21_339762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 3, 8].length) (baseStart_339762 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339762 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339762 prefixEnd_339762 := by exact prefixLift 339762
  have htrace : WordTrace (prefixWord ++ tailWord_339762) baseStart_339762 baseEnd_339762 := by
    simpa [prefixWord, tailWord_339762, baseEnd_339762] using wordTrace_append hprefix tailTrace_339762
  have hstable : (prefixWord ++ tailWord_339762).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339762).length < 2 ^ (prefixWord ++ tailWord_339762).sum := by decide
  have hdescent : baseEnd_339762 < baseStart_339762 := by decide
  rcases family_descends (prefixWord ++ tailWord_339762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339793 : List Nat := [1, 2, 2, 1, 5, 1, 2, 2, 5]
def baseStart_339793 : Nat := 118140960795 + 339793 * 2 ^ 59
def prefixEnd_339793 : Nat := 4983230072969 + 3 ^ 40 * 339793 * 2
def baseEnd_339793 : Nat := 77545392014797463122145

theorem tailTrace_339793 : CollatzResearch.WordTrace tailWord_339793 prefixEnd_339793 77545392014797463122145 := by
  unfold tailWord_339793
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393268857995467869344033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8262179238663645246229355 12393268857995467869344033)
  ·
    refine ⟨9294951643496600902008025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12393268857995467869344033 9294951643496600902008025)
    ·
      refine ⟨6971213732622450676506019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9294951643496600902008025 6971213732622450676506019)
      ·
        refine ⟨10456820598933676014759029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6971213732622450676506019 10456820598933676014759029)
        ·
          refine ⟨980326931150032126383659, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10456820598933676014759029 980326931150032126383659)
          ·
            refine ⟨1470490396725048189575489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 980326931150032126383659 1470490396725048189575489)
            ·
              refine ⟨1102867797543786142181617, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1470490396725048189575489 1102867797543786142181617)
              ·
                refine ⟨827150848157839606636213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1102867797543786142181617 827150848157839606636213)
                ·
                  refine ⟨77545392014797463122145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 827150848157839606636213 77545392014797463122145)
                  ·
                    rfl

theorem cell21_339793_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 1, 2, 2, 5].length) (baseStart_339793 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339793 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339793 prefixEnd_339793 := by exact prefixLift 339793
  have htrace : WordTrace (prefixWord ++ tailWord_339793) baseStart_339793 baseEnd_339793 := by
    simpa [prefixWord, tailWord_339793, baseEnd_339793] using wordTrace_append hprefix tailTrace_339793
  have hstable : (prefixWord ++ tailWord_339793).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339793).length < 2 ^ (prefixWord ++ tailWord_339793).sum := by decide
  have hdescent : baseEnd_339793 < baseStart_339793 := by decide
  rcases family_descends (prefixWord ++ tailWord_339793) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339796 : List Nat := [2, 4, 1, 1, 3, 3, 2, 5]
def baseStart_339796 : Nat := 118140960795 + 339796 * 2 ^ 59
def prefixEnd_339796 : Nat := 4983230072969 + 3 ^ 40 * 339796 * 2
def baseEnd_339796 : Nat := 25848692218556708190713

theorem tailTrace_339796 : CollatzResearch.WordTrace tailWord_339796 prefixEnd_339796 25848692218556708190713 := by
  unfold tailWord_339796
  simp only [CollatzResearch.WordTrace]
  refine ⟨6196689138492299690851621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8262252184656399587802161 6196689138492299690851621)
  ·
    refine ⟨1161879213467306192034679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6196689138492299690851621 1161879213467306192034679)
    ·
      refine ⟨1742818820200959288052019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1161879213467306192034679 1742818820200959288052019)
      ·
        refine ⟨2614228230301438932078029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1742818820200959288052019 2614228230301438932078029)
        ·
          refine ⟨980335586363039599529261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2614228230301438932078029 980335586363039599529261)
          ·
            refine ⟨367625844886139849823473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980335586363039599529261 367625844886139849823473)
            ·
              refine ⟨275719383664604887367605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367625844886139849823473 275719383664604887367605)
              ·
                refine ⟨25848692218556708190713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 275719383664604887367605 25848692218556708190713)
                ·
                  rfl

theorem cell21_339796_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 3, 2, 5].length) (baseStart_339796 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339796 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339796 prefixEnd_339796 := by exact prefixLift 339796
  have htrace : WordTrace (prefixWord ++ tailWord_339796) baseStart_339796 baseEnd_339796 := by
    simpa [prefixWord, tailWord_339796, baseEnd_339796] using wordTrace_append hprefix tailTrace_339796
  have hstable : (prefixWord ++ tailWord_339796).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339796).length < 2 ^ (prefixWord ++ tailWord_339796).sum := by decide
  have hdescent : baseEnd_339796 < baseStart_339796 := by decide
  rcases family_descends (prefixWord ++ tailWord_339796) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339807 : List Nat := [1, 1, 2, 3, 1, 4, 1, 2, 6]
def baseStart_339807 : Nat := 118140960795 + 339807 * 2 ^ 59
def prefixEnd_339807 : Nat := 4983230072969 + 3 ^ 40 * 339807 * 2
def baseEnd_339807 : Nat := 77548587005536549888783

theorem tailTrace_339807 : CollatzResearch.WordTrace tailWord_339807 prefixEnd_339807 77548587005536549888783 := by
  unfold tailWord_339807
  simp only [CollatzResearch.WordTrace]
  refine ⟨12393779479944748260353675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8262519653296498840235783 12393779479944748260353675)
  ·
    refine ⟨18590669219917122390530513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12393779479944748260353675 18590669219917122390530513)
    ·
      refine ⟨13943001914937841792897885, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18590669219917122390530513 13943001914937841792897885)
      ·
        refine ⟨5228625718101690672336707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 13943001914937841792897885 5228625718101690672336707)
        ·
          refine ⟨7842938577152536008505061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5228625718101690672336707 7842938577152536008505061)
          ·
            refine ⟨1470550983216100501594699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7842938577152536008505061 1470550983216100501594699)
            ·
              refine ⟨2205826474824150752392049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1470550983216100501594699 2205826474824150752392049)
              ·
                refine ⟨1654369856118113064294037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2205826474824150752392049 1654369856118113064294037)
                ·
                  refine ⟨77548587005536549888783, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1654369856118113064294037 77548587005536549888783)
                  ·
                    rfl

theorem cell21_339807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 4, 1, 2, 6].length) (baseStart_339807 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339807 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339807 prefixEnd_339807 := by exact prefixLift 339807
  have htrace : WordTrace (prefixWord ++ tailWord_339807) baseStart_339807 baseEnd_339807 := by
    simpa [prefixWord, tailWord_339807, baseEnd_339807] using wordTrace_append hprefix tailTrace_339807
  have hstable : (prefixWord ++ tailWord_339807).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339807).length < 2 ^ (prefixWord ++ tailWord_339807).sum := by decide
  have hdescent : baseEnd_339807 < baseStart_339807 := by decide
  rcases family_descends (prefixWord ++ tailWord_339807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339852 : List Nat := [2, 2, 1, 2, 1, 2, 1, 3, 7]
def baseStart_339852 : Nat := 118140960795 + 339852 * 2 ^ 59
def prefixEnd_339852 : Nat := 4983230072969 + 3 ^ 40 * 339852 * 2
def baseEnd_339852 : Nat := 77558856618626471638691

theorem tailTrace_339852 : CollatzResearch.WordTrace tailWord_339852 prefixEnd_339852 77558856618626471638691 := by
  unfold tailWord_339852
  simp only [CollatzResearch.WordTrace]
  refine ⟨6197710382390860472870905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8263613843187813963827873 6197710382390860472870905)
  ·
    refine ⟨4648282786793145354653179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6197710382390860472870905 4648282786793145354653179)
    ·
      refine ⟨6972424180189718031979769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4648282786793145354653179 6972424180189718031979769)
      ·
        refine ⟨5229318135142288523984827, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6972424180189718031979769 5229318135142288523984827)
        ·
          refine ⟨7843977202713432785977241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5229318135142288523984827 7843977202713432785977241)
          ·
            refine ⟨5882982902035074589482931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7843977202713432785977241 5882982902035074589482931)
            ·
              refine ⟨8824474353052611884224397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5882982902035074589482931 8824474353052611884224397)
              ·
                refine ⟨3309177882394729456584149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 8824474353052611884224397 3309177882394729456584149)
                ·
                  refine ⟨77558856618626471638691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3309177882394729456584149 77558856618626471638691)
                  ·
                    rfl

theorem cell21_339852_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 3, 7].length) (baseStart_339852 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339852 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339852 prefixEnd_339852 := by exact prefixLift 339852
  have htrace : WordTrace (prefixWord ++ tailWord_339852) baseStart_339852 baseEnd_339852 := by
    simpa [prefixWord, tailWord_339852, baseEnd_339852] using wordTrace_append hprefix tailTrace_339852
  have hstable : (prefixWord ++ tailWord_339852).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339852).length < 2 ^ (prefixWord ++ tailWord_339852).sum := by decide
  have hdescent : baseEnd_339852 < baseStart_339852 := by decide
  rcases family_descends (prefixWord ++ tailWord_339852) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_339928 : List Nat := [2, 1, 2, 2, 2, 2, 1, 2, 7]
def baseStart_339928 : Nat := 118140960795 + 339928 * 2 ^ 59
def prefixEnd_339928 : Nat := 4983230072969 + 3 ^ 40 * 339928 * 2
def baseEnd_339928 : Nat := 77576200854067228371869

theorem tailTrace_339928 : CollatzResearch.WordTrace tailWord_339928 prefixEnd_339928 77576200854067228371869 := by
  unfold tailWord_339928
  simp only [CollatzResearch.WordTrace]
  refine ⟨6199096356253192962754219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8265461808337590617005625 6199096356253192962754219)
  ·
    refine ⟨9298644534379789444131329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6199096356253192962754219 9298644534379789444131329)
    ·
      refine ⟨6973983400784842083098497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9298644534379789444131329 6973983400784842083098497)
      ·
        refine ⟨5230487550588631562323873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6973983400784842083098497 5230487550588631562323873)
        ·
          refine ⟨3922865662941473671742905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5230487550588631562323873 3922865662941473671742905)
          ·
            refine ⟨2942149247206105253807179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3922865662941473671742905 2942149247206105253807179)
            ·
              refine ⟨4413223870809157880710769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2942149247206105253807179 4413223870809157880710769)
              ·
                refine ⟨3309917903106868410533077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4413223870809157880710769 3309917903106868410533077)
                ·
                  refine ⟨77576200854067228371869, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3309917903106868410533077 77576200854067228371869)
                  ·
                    rfl

theorem cell21_339928_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 2, 2, 1, 2, 7].length) (baseStart_339928 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_339928 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_339928 prefixEnd_339928 := by exact prefixLift 339928
  have htrace : WordTrace (prefixWord ++ tailWord_339928) baseStart_339928 baseEnd_339928 := by
    simpa [prefixWord, tailWord_339928, baseEnd_339928] using wordTrace_append hprefix tailTrace_339928
  have hstable : (prefixWord ++ tailWord_339928).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_339928).length < 2 ^ (prefixWord ++ tailWord_339928).sum := by decide
  have hdescent : baseEnd_339928 < baseStart_339928 := by decide
  rcases family_descends (prefixWord ++ tailWord_339928) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340010 : List Nat := [3, 1, 4, 1, 2, 3, 2, 1, 4]
def baseStart_340010 : Nat := 118140960795 + 340010 * 2 ^ 59
def prefixEnd_340010 : Nat := 4983230072969 + 3 ^ 40 * 340010 * 2
def baseEnd_340010 : Nat := 77594914371253308005035

theorem tailTrace_340010 : CollatzResearch.WordTrace tailWord_340010 prefixEnd_340010 77594914371253308005035 := by
  unfold tailWord_340010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3100295874552328482498371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8267455665472875953328989 3100295874552328482498371)
  ·
    refine ⟨4650443811828492723747557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3100295874552328482498371 4650443811828492723747557)
    ·
      refine ⟨871958214717842385702667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4650443811828492723747557 871958214717842385702667)
      ·
        refine ⟨1307937322076763578554001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 871958214717842385702667 1307937322076763578554001)
        ·
          refine ⟨980952991557572683915501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1307937322076763578554001 980952991557572683915501)
          ·
            refine ⟨367857371834089756468313, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 980952991557572683915501 367857371834089756468313)
            ·
              refine ⟨275893028875567317351235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 367857371834089756468313 275893028875567317351235)
              ·
                refine ⟨413839543313350976026853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 275893028875567317351235 413839543313350976026853)
                ·
                  refine ⟨77594914371253308005035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 413839543313350976026853 77594914371253308005035)
                  ·
                    rfl

theorem cell21_340010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 3, 2, 1, 4].length) (baseStart_340010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340010 prefixEnd_340010 := by exact prefixLift 340010
  have htrace : WordTrace (prefixWord ++ tailWord_340010) baseStart_340010 baseEnd_340010 := by
    simpa [prefixWord, tailWord_340010, baseEnd_340010] using wordTrace_append hprefix tailTrace_340010
  have hstable : (prefixWord ++ tailWord_340010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340010).length < 2 ^ (prefixWord ++ tailWord_340010).sum := by decide
  have hdescent : baseEnd_340010 < baseStart_340010 := by decide
  rcases family_descends (prefixWord ++ tailWord_340010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340080 : List Nat := [2, 1, 1, 1, 5, 2, 1, 1, 7]
def baseStart_340080 : Nat := 118140960795 + 340080 * 2 ^ 59
def prefixEnd_340080 : Nat := 4983230072969 + 3 ^ 40 * 340080 * 2
def baseEnd_340080 : Nat := 77610889324948741838225

theorem tailTrace_340080 : CollatzResearch.WordTrace tailWord_340080 prefixEnd_340080 77610889324948741838225 := by
  unfold tailWord_340080
  simp only [CollatzResearch.WordTrace]
  refine ⟨6201868303977857942520847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8269157738637143923361129 6201868303977857942520847)
  ·
    refine ⟨9302802455966786913781271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6201868303977857942520847 9302802455966786913781271)
    ·
      refine ⟨13954203683950180370671907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9302802455966786913781271 13954203683950180370671907)
      ·
        refine ⟨20931305525925270556007861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13954203683950180370671907 20931305525925270556007861)
        ·
          refine ⟨1962309893055494114625737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 20931305525925270556007861 1962309893055494114625737)
          ·
            refine ⟨1471732419791620585969303, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1962309893055494114625737 1471732419791620585969303)
            ·
              refine ⟨2207598629687430878953955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1471732419791620585969303 2207598629687430878953955)
              ·
                refine ⟨3311397944531146318430933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2207598629687430878953955 3311397944531146318430933)
                ·
                  refine ⟨77610889324948741838225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3311397944531146318430933 77610889324948741838225)
                  ·
                    rfl

theorem cell21_340080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 2, 1, 1, 7].length) (baseStart_340080 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340080 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340080 prefixEnd_340080 := by exact prefixLift 340080
  have htrace : WordTrace (prefixWord ++ tailWord_340080) baseStart_340080 baseEnd_340080 := by
    simpa [prefixWord, tailWord_340080, baseEnd_340080] using wordTrace_append hprefix tailTrace_340080
  have hstable : (prefixWord ++ tailWord_340080).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340080).length < 2 ^ (prefixWord ++ tailWord_340080).sum := by decide
  have hdescent : baseEnd_340080 < baseStart_340080 := by decide
  rcases family_descends (prefixWord ++ tailWord_340080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340114 : List Nat := [3, 2, 3, 1, 1, 1, 1, 6, 3]
def baseStart_340114 : Nat := 118140960795 + 340114 * 2 ^ 59
def prefixEnd_340114 : Nat := 4983230072969 + 3 ^ 40 * 340114 * 2
def baseEnd_340114 : Nat := 77618648588172238271489

theorem tailTrace_340114 : CollatzResearch.WordTrace tailWord_340114 prefixEnd_340114 77618648588172238271489 := by
  unfold tailWord_340114
  simp only [CollatzResearch.WordTrace]
  refine ⟨3101244172458134922944849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8269984459888359794519597 3101244172458134922944849)
  ·
    refine ⟨2325933129343601192208637, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3101244172458134922944849 2325933129343601192208637)
    ·
      refine ⟨872224923503850447078239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2325933129343601192208637 872224923503850447078239)
      ·
        refine ⟨1308337385255775670617359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 872224923503850447078239 1308337385255775670617359)
        ·
          refine ⟨1962506077883663505926039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1308337385255775670617359 1962506077883663505926039)
          ·
            refine ⟨2943759116825495258889059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1962506077883663505926039 2943759116825495258889059)
            ·
              refine ⟨4415638675238242888333589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2943759116825495258889059 4415638675238242888333589)
              ·
                refine ⟨206983062901792635390637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 4415638675238242888333589 206983062901792635390637)
                ·
                  refine ⟨77618648588172238271489, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 206983062901792635390637 77618648588172238271489)
                  ·
                    rfl

theorem cell21_340114_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 1, 1, 6, 3].length) (baseStart_340114 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340114 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340114 prefixEnd_340114 := by exact prefixLift 340114
  have htrace : WordTrace (prefixWord ++ tailWord_340114) baseStart_340114 baseEnd_340114 := by
    simpa [prefixWord, tailWord_340114, baseEnd_340114] using wordTrace_append hprefix tailTrace_340114
  have hstable : (prefixWord ++ tailWord_340114).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340114).length < 2 ^ (prefixWord ++ tailWord_340114).sum := by decide
  have hdescent : baseEnd_340114 < baseStart_340114 := by decide
  rcases family_descends (prefixWord ++ tailWord_340114) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340277 : List Nat := [1, 3, 3, 1, 2, 1, 10]
def baseStart_340277 : Nat := 118140960795 + 340277 * 2 ^ 59
def prefixEnd_340277 : Nat := 4983230072969 + 3 ^ 40 * 340277 * 2
def baseEnd_340277 : Nat := 8628427489880019672721

theorem tailTrace_340277 : CollatzResearch.WordTrace tailWord_340277 prefixEnd_340277 8628427489880019672721 := by
  unfold tailWord_340277
  simp only [CollatzResearch.WordTrace]
  refine ⟨12410921788242018529963085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8273947858828012353308723 12410921788242018529963085)
  ·
    refine ⟨4654095670590756948736157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12410921788242018529963085 4654095670590756948736157)
    ·
      refine ⟨1745285876471533855776059, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4654095670590756948736157 1745285876471533855776059)
      ·
        refine ⟨2617928814707300783664089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1745285876471533855776059 2617928814707300783664089)
        ·
          refine ⟨1963446611030475587748067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2617928814707300783664089 1963446611030475587748067)
          ·
            refine ⟨2945169916545713381622101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1963446611030475587748067 2945169916545713381622101)
            ·
              refine ⟨8628427489880019672721, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2945169916545713381622101 8628427489880019672721)
              ·
                rfl

theorem cell21_340277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 2, 1, 10].length) (baseStart_340277 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340277 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340277 prefixEnd_340277 := by exact prefixLift 340277
  have htrace : WordTrace (prefixWord ++ tailWord_340277) baseStart_340277 baseEnd_340277 := by
    simpa [prefixWord, tailWord_340277, baseEnd_340277] using wordTrace_append hprefix tailTrace_340277
  have hstable : (prefixWord ++ tailWord_340277).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340277).length < 2 ^ (prefixWord ++ tailWord_340277).sum := by decide
  have hdescent : baseEnd_340277 < baseStart_340277 := by decide
  rcases family_descends (prefixWord ++ tailWord_340277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340460 : List Nat := [2, 2, 1, 1, 2, 1, 6, 1, 5]
def baseStart_340460 : Nat := 118140960795 + 340460 * 2 ^ 59
def prefixEnd_340460 : Nat := 4983230072969 + 3 ^ 40 * 340460 * 2
def baseEnd_340460 : Nat := 77697610502152525504115

theorem tailTrace_340460 : CollatzResearch.WordTrace tailWord_340460 prefixEnd_340460 77697610502152525504115 := by
  unfold tailWord_340460
  simp only [CollatzResearch.WordTrace]
  refine ⟨6208798173289520391937417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8278397564386027189249889 6208798173289520391937417)
  ·
    refine ⟨4656598629967140293953063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6208798173289520391937417 4656598629967140293953063)
    ·
      refine ⟨6984897944950710440929595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4656598629967140293953063 6984897944950710440929595)
      ·
        refine ⟨10477346917426065661394393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6984897944950710440929595 10477346917426065661394393)
        ·
          refine ⟨7858010188069549246045795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10477346917426065661394393 7858010188069549246045795)
          ·
            refine ⟨11787015282104323869068693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7858010188069549246045795 11787015282104323869068693)
            ·
              refine ⟨552516341348640181362595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11787015282104323869068693 552516341348640181362595)
              ·
                refine ⟨828774512022960272043893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 552516341348640181362595 828774512022960272043893)
                ·
                  refine ⟨77697610502152525504115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 828774512022960272043893 77697610502152525504115)
                  ·
                    rfl

theorem cell21_340460_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 5].length) (baseStart_340460 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340460 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340460 prefixEnd_340460 := by exact prefixLift 340460
  have htrace : WordTrace (prefixWord ++ tailWord_340460) baseStart_340460 baseEnd_340460 := by
    simpa [prefixWord, tailWord_340460, baseEnd_340460] using wordTrace_append hprefix tailTrace_340460
  have hstable : (prefixWord ++ tailWord_340460).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340460).length < 2 ^ (prefixWord ++ tailWord_340460).sum := by decide
  have hdescent : baseEnd_340460 < baseStart_340460 := by decide
  rcases family_descends (prefixWord ++ tailWord_340460) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340494 : List Nat := [4, 1, 1, 2, 3, 1, 3, 3, 3]
def baseStart_340494 : Nat := 118140960795 + 340494 * 2 ^ 59
def prefixEnd_340494 : Nat := 4983230072969 + 3 ^ 40 * 340494 * 2
def baseEnd_340494 : Nat := 77705369765376021937379

theorem tailTrace_340494 : CollatzResearch.WordTrace tailWord_340494 prefixEnd_340494 77705369765376021937379 := by
  unfold tailWord_340494
  simp only [CollatzResearch.WordTrace]
  refine ⟨1552354553556983073826567, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8279224285637243060408357 1552354553556983073826567)
  ·
    refine ⟨2328531830335474610739851, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1552354553556983073826567 2328531830335474610739851)
    ·
      refine ⟨3492797745503211916109777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2328531830335474610739851 3492797745503211916109777)
      ·
        refine ⟨2619598309127408937082333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3492797745503211916109777 2619598309127408937082333)
        ·
          refine ⟨982349365922778351405875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2619598309127408937082333 982349365922778351405875)
          ·
            refine ⟨1473524048884167527108813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 982349365922778351405875 1473524048884167527108813)
            ·
              refine ⟨552571518331562822665805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1473524048884167527108813 552571518331562822665805)
              ·
                refine ⟨207214319374336058499677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552571518331562822665805 207214319374336058499677)
                ·
                  refine ⟨77705369765376021937379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207214319374336058499677 77705369765376021937379)
                  ·
                    rfl

theorem cell21_340494_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 1, 3, 3, 3].length) (baseStart_340494 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340494 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340494 prefixEnd_340494 := by exact prefixLift 340494
  have htrace : WordTrace (prefixWord ++ tailWord_340494) baseStart_340494 baseEnd_340494 := by
    simpa [prefixWord, tailWord_340494, baseEnd_340494] using wordTrace_append hprefix tailTrace_340494
  have hstable : (prefixWord ++ tailWord_340494).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340494).length < 2 ^ (prefixWord ++ tailWord_340494).sum := by decide
  have hdescent : baseEnd_340494 < baseStart_340494 := by decide
  rcases family_descends (prefixWord ++ tailWord_340494) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340522 : List Nat := [3, 1, 4, 1, 1, 3, 2, 6]
def baseStart_340522 : Nat := 118140960795 + 340522 * 2 ^ 59
def prefixEnd_340522 : Nat := 4983230072969 + 3 ^ 40 * 340522 * 2
def baseEnd_340522 : Nat := 25903919915618065156885

theorem tailTrace_340522 : CollatzResearch.WordTrace tailWord_340522 prefixEnd_340522 25903919915618065156885 := by
  unfold tailWord_340522
  simp only [CollatzResearch.WordTrace]
  refine ⟨3104964418088606343157955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8279905114902950248421213 3104964418088606343157955)
  ·
    refine ⟨4657446627132909514736933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3104964418088606343157955 4657446627132909514736933)
    ·
      refine ⟨873271242587420534013175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4657446627132909514736933 873271242587420534013175)
      ·
        refine ⟨1309906863881130801019763, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 873271242587420534013175 1309906863881130801019763)
        ·
          refine ⟨1964860295821696201529645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1309906863881130801019763 1964860295821696201529645)
          ·
            refine ⟨736822610933136075573617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1964860295821696201529645 736822610933136075573617)
            ·
              refine ⟨552616958199852056680213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 736822610933136075573617 552616958199852056680213)
              ·
                refine ⟨25903919915618065156885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 552616958199852056680213 25903919915618065156885)
                ·
                  rfl

theorem cell21_340522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 3, 2, 6].length) (baseStart_340522 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340522 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340522 prefixEnd_340522 := by exact prefixLift 340522
  have htrace : WordTrace (prefixWord ++ tailWord_340522) baseStart_340522 baseEnd_340522 := by
    simpa [prefixWord, tailWord_340522, baseEnd_340522] using wordTrace_append hprefix tailTrace_340522
  have hstable : (prefixWord ++ tailWord_340522).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340522).length < 2 ^ (prefixWord ++ tailWord_340522).sum := by decide
  have hdescent : baseEnd_340522 < baseStart_340522 := by decide
  rcases family_descends (prefixWord ++ tailWord_340522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340567 : List Nat := [1, 1, 3, 2, 2, 2, 4, 2, 4]
def baseStart_340567 : Nat := 118140960795 + 340567 * 2 ^ 59
def prefixEnd_340567 : Nat := 4983230072969 + 3 ^ 40 * 340567 * 2
def baseEnd_340567 : Nat := 77722029359944117220563

theorem tailTrace_340567 : CollatzResearch.WordTrace tailWord_340567 prefixEnd_340567 77722029359944117220563 := by
  unfold tailWord_340567
  simp only [CollatzResearch.WordTrace]
  refine ⟨12421498957191398058019955, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8280999304794265372013303 12421498957191398058019955)
  ·
    refine ⟨18632248435787097087029933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12421498957191398058019955 18632248435787097087029933)
    ·
      refine ⟨6987093163420161407636225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18632248435787097087029933 6987093163420161407636225)
      ·
        refine ⟨5240319872565121055727169, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6987093163420161407636225 5240319872565121055727169)
        ·
          refine ⟨3930239904423840791795377, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5240319872565121055727169 3930239904423840791795377)
          ·
            refine ⟨2947679928317880593846533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3930239904423840791795377 2947679928317880593846533)
            ·
              refine ⟨552689986559602611346225, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2947679928317880593846533 552689986559602611346225)
              ·
                refine ⟨414517489919701958509669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 552689986559602611346225 414517489919701958509669)
                ·
                  refine ⟨77722029359944117220563, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414517489919701958509669 77722029359944117220563)
                  ·
                    rfl

theorem cell21_340567_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 4, 2, 4].length) (baseStart_340567 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340567 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340567 prefixEnd_340567 := by exact prefixLift 340567
  have htrace : WordTrace (prefixWord ++ tailWord_340567) baseStart_340567 baseEnd_340567 := by
    simpa [prefixWord, tailWord_340567, baseEnd_340567] using wordTrace_append hprefix tailTrace_340567
  have hstable : (prefixWord ++ tailWord_340567).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340567).length < 2 ^ (prefixWord ++ tailWord_340567).sum := by decide
  have hdescent : baseEnd_340567 < baseStart_340567 := by decide
  rcases family_descends (prefixWord ++ tailWord_340567) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340663 : List Nat := [1, 1, 3, 1, 7, 1, 1, 3, 3]
def baseStart_340663 : Nat := 118140960795 + 340663 * 2 ^ 59
def prefixEnd_340663 : Nat := 4983230072969 + 3 ^ 40 * 340663 * 2
def baseEnd_340663 : Nat := 77743937867869283620367

theorem tailTrace_340663 : CollatzResearch.WordTrace tailWord_340663 prefixEnd_340663 77743937867869283620367 := by
  unfold tailWord_340663
  simp only [CollatzResearch.WordTrace]
  refine ⟨12425000364843606453514643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8283333576562404302343095 12425000364843606453514643)
  ·
    refine ⟨18637500547265409680271965, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12425000364843606453514643 18637500547265409680271965)
    ·
      refine ⟨6989062705224528630101987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18637500547265409680271965 6989062705224528630101987)
      ·
        refine ⟨10483594057836792945152981, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6989062705224528630101987 10483594057836792945152981)
        ·
          refine ⟨245709235730549834652023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10483594057836792945152981 245709235730549834652023)
          ·
            refine ⟨368563853595824751978035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 245709235730549834652023 368563853595824751978035)
            ·
              refine ⟨552845780393737127967053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 368563853595824751978035 552845780393737127967053)
              ·
                refine ⟨207317167647651422987645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 552845780393737127967053 207317167647651422987645)
                ·
                  refine ⟨77743937867869283620367, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207317167647651422987645 77743937867869283620367)
                  ·
                    rfl

theorem cell21_340663_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 7, 1, 1, 3, 3].length) (baseStart_340663 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340663 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340663 prefixEnd_340663 := by exact prefixLift 340663
  have htrace : WordTrace (prefixWord ++ tailWord_340663) baseStart_340663 baseEnd_340663 := by
    simpa [prefixWord, tailWord_340663, baseEnd_340663] using wordTrace_append hprefix tailTrace_340663
  have hstable : (prefixWord ++ tailWord_340663).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340663).length < 2 ^ (prefixWord ++ tailWord_340663).sum := by decide
  have hdescent : baseEnd_340663 < baseStart_340663 := by decide
  rcases family_descends (prefixWord ++ tailWord_340663) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340747 : List Nat := [1, 1, 1, 1, 5, 1, 1, 5, 5]
def baseStart_340747 : Nat := 118140960795 + 340747 * 2 ^ 59
def prefixEnd_340747 : Nat := 4983230072969 + 3 ^ 40 * 340747 * 2
def baseEnd_340747 : Nat := 77763107812303804220195

theorem tailTrace_340747 : CollatzResearch.WordTrace tailWord_340747 prefixEnd_340747 77763107812303804220195 := by
  unfold tailWord_340747
  simp only [CollatzResearch.WordTrace]
  refine ⟨12428064096539288799572495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8285376064359525866381663 12428064096539288799572495)
  ·
    refine ⟨18642096144808933199358743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12428064096539288799572495 18642096144808933199358743)
    ·
      refine ⟨27963144217213399799038115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18642096144808933199358743 27963144217213399799038115)
      ·
        refine ⟨41944716325820099698557173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 27963144217213399799038115 41944716325820099698557173)
        ·
          refine ⟨3932317155545634346739735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 41944716325820099698557173 3932317155545634346739735)
          ·
            refine ⟨5898475733318451520109603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3932317155545634346739735 5898475733318451520109603)
            ·
              refine ⟨8847713599977677280164405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5898475733318451520109603 8847713599977677280164405)
              ·
                refine ⟨829473149997907245015413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 8847713599977677280164405 829473149997907245015413)
                ·
                  refine ⟨77763107812303804220195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 829473149997907245015413 77763107812303804220195)
                  ·
                    rfl

theorem cell21_340747_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 5, 5].length) (baseStart_340747 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340747 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340747 prefixEnd_340747 := by exact prefixLift 340747
  have htrace : WordTrace (prefixWord ++ tailWord_340747) baseStart_340747 baseEnd_340747 := by
    simpa [prefixWord, tailWord_340747, baseEnd_340747] using wordTrace_append hprefix tailTrace_340747
  have hstable : (prefixWord ++ tailWord_340747).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340747).length < 2 ^ (prefixWord ++ tailWord_340747).sum := by decide
  have hdescent : baseEnd_340747 < baseStart_340747 := by decide
  rcases family_descends (prefixWord ++ tailWord_340747) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340764 : List Nat := [2, 2, 3, 1, 1, 4, 1, 2, 5]
def baseStart_340764 : Nat := 118140960795 + 340764 * 2 ^ 59
def prefixEnd_340764 : Nat := 4983230072969 + 3 ^ 40 * 340764 * 2
def baseEnd_340764 : Nat := 77766987443915552436827

theorem tailTrace_340764 : CollatzResearch.WordTrace tailWord_340764 prefixEnd_340764 77766987443915552436827 := by
  unfold tailWord_340764
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214342068738850351470673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8285789424985133801960897 6214342068738850351470673)
  ·
    refine ⟨4660756551554137763603005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6214342068738850351470673 4660756551554137763603005)
    ·
      refine ⟨1747783706832801661351127, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4660756551554137763603005 1747783706832801661351127)
      ·
        refine ⟨2621675560249202492026691, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1747783706832801661351127 2621675560249202492026691)
        ·
          refine ⟨3932513340373803738040037, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2621675560249202492026691 3932513340373803738040037)
          ·
            refine ⟨737346251320088200882507, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3932513340373803738040037 737346251320088200882507)
            ·
              refine ⟨1106019376980132301323761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737346251320088200882507 1106019376980132301323761)
              ·
                refine ⟨829514532735099225992821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1106019376980132301323761 829514532735099225992821)
                ·
                  refine ⟨77766987443915552436827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 829514532735099225992821 77766987443915552436827)
                  ·
                    rfl

theorem cell21_340764_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 4, 1, 2, 5].length) (baseStart_340764 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340764 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340764 prefixEnd_340764 := by exact prefixLift 340764
  have htrace : WordTrace (prefixWord ++ tailWord_340764) baseStart_340764 baseEnd_340764 := by
    simpa [prefixWord, tailWord_340764, baseEnd_340764] using wordTrace_append hprefix tailTrace_340764
  have hstable : (prefixWord ++ tailWord_340764).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340764).length < 2 ^ (prefixWord ++ tailWord_340764).sum := by decide
  have hdescent : baseEnd_340764 < baseStart_340764 := by decide
  rcases family_descends (prefixWord ++ tailWord_340764) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340792 : List Nat := [2, 1, 2, 1, 3, 2, 10]
def baseStart_340792 : Nat := 118140960795 + 340792 * 2 ^ 59
def prefixEnd_340792 : Nat := 4983230072969 + 3 ^ 40 * 340792 * 2
def baseEnd_340792 : Nat := 8641486380599302885567

theorem tailTrace_340792 : CollatzResearch.WordTrace tailWord_340792 prefixEnd_340792 8641486380599302885567 := by
  unfold tailWord_340792
  simp only [CollatzResearch.WordTrace]
  refine ⟨6214852690688130742480315, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8286470254250840989973753 6214852690688130742480315)
  ·
    refine ⟨9322279036032196113720473, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6214852690688130742480315 9322279036032196113720473)
    ·
      refine ⟨6991709277024147085290355, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9322279036032196113720473 6991709277024147085290355)
      ·
        refine ⟨10487563915536220627935533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 6991709277024147085290355 10487563915536220627935533)
        ·
          refine ⟨3932836468326082735475825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10487563915536220627935533 3932836468326082735475825)
          ·
            refine ⟨2949627351244562051606869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3932836468326082735475825 2949627351244562051606869)
            ·
              refine ⟨8641486380599302885567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2949627351244562051606869 8641486380599302885567)
              ·
                rfl

theorem cell21_340792_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 2, 10].length) (baseStart_340792 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340792 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340792 prefixEnd_340792 := by exact prefixLift 340792
  have htrace : WordTrace (prefixWord ++ tailWord_340792) baseStart_340792 baseEnd_340792 := by
    simpa [prefixWord, tailWord_340792, baseEnd_340792] using wordTrace_append hprefix tailTrace_340792
  have hstable : (prefixWord ++ tailWord_340792).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340792).length < 2 ^ (prefixWord ++ tailWord_340792).sum := by decide
  have hdescent : baseEnd_340792 < baseStart_340792 := by decide
  rcases family_descends (prefixWord ++ tailWord_340792) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340812 : List Nat := [2, 2, 1, 3, 3, 2, 3, 1, 4]
def baseStart_340812 : Nat := 118140960795 + 340812 * 2 ^ 59
def prefixEnd_340812 : Nat := 4983230072969 + 3 ^ 40 * 340812 * 2
def baseEnd_340812 : Nat := 77777941697878135636729

theorem tailTrace_340812 : CollatzResearch.WordTrace tailWord_340812 prefixEnd_340812 77777941697878135636729 := by
  unfold tailWord_340812
  simp only [CollatzResearch.WordTrace]
  refine ⟨6215217420651902450344345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8286956560869203267125793 6215217420651902450344345)
  ·
    refine ⟨4661413065488926837758259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6215217420651902450344345 4661413065488926837758259)
    ·
      refine ⟨6992119598233390256637389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661413065488926837758259 6992119598233390256637389)
      ·
        refine ⟨2622044849337521346239021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6992119598233390256637389 2622044849337521346239021)
        ·
          refine ⟨983266818501570504839633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2622044849337521346239021 983266818501570504839633)
          ·
            refine ⟨737450113876177878629725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983266818501570504839633 737450113876177878629725)
            ·
              refine ⟨276543792703566704486147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737450113876177878629725 276543792703566704486147)
              ·
                refine ⟨414815689055350056729221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 276543792703566704486147 414815689055350056729221)
                ·
                  refine ⟨77777941697878135636729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414815689055350056729221 77777941697878135636729)
                  ·
                    rfl

theorem cell21_340812_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 3, 2, 3, 1, 4].length) (baseStart_340812 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340812 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340812 prefixEnd_340812 := by exact prefixLift 340812
  have htrace : WordTrace (prefixWord ++ tailWord_340812) baseStart_340812 baseEnd_340812 := by
    simpa [prefixWord, tailWord_340812, baseEnd_340812] using wordTrace_append hprefix tailTrace_340812
  have hstable : (prefixWord ++ tailWord_340812).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340812).length < 2 ^ (prefixWord ++ tailWord_340812).sum := by decide
  have hdescent : baseEnd_340812 < baseStart_340812 := by decide
  rcases family_descends (prefixWord ++ tailWord_340812) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340826 : List Nat := [3, 1, 1, 2, 1, 6, 2, 5]
def baseStart_340826 : Nat := 118140960795 + 340826 * 2 ^ 59
def prefixEnd_340826 : Nat := 4983230072969 + 3 ^ 40 * 340826 * 2
def baseEnd_340826 : Nat := 25927045562872407467789

theorem tailTrace_340826 : CollatzResearch.WordTrace tailWord_340826 prefixEnd_340826 25927045562872407467789 := by
  unfold tailWord_340826
  simp only [CollatzResearch.WordTrace]
  refine ⟨3107736365813271322924583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8287296975502056861132221 3107736365813271322924583)
  ·
    refine ⟨4661604548719906984386875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3107736365813271322924583 4661604548719906984386875)
    ·
      refine ⟨6992406823079860476580313, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4661604548719906984386875 6992406823079860476580313)
      ·
        refine ⟨5244305117309895357435235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 6992406823079860476580313 5244305117309895357435235)
        ·
          refine ⟨7866457675964843036152853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5244305117309895357435235 7866457675964843036152853)
          ·
            refine ⟨368740203560852017319665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 7866457675964843036152853 368740203560852017319665)
            ·
              refine ⟨276555152670639012989749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 368740203560852017319665 276555152670639012989749)
              ·
                refine ⟨25927045562872407467789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276555152670639012989749 25927045562872407467789)
                ·
                  rfl

theorem cell21_340826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 6, 2, 5].length) (baseStart_340826 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340826 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340826 prefixEnd_340826 := by exact prefixLift 340826
  have htrace : WordTrace (prefixWord ++ tailWord_340826) baseStart_340826 baseEnd_340826 := by
    simpa [prefixWord, tailWord_340826, baseEnd_340826] using wordTrace_append hprefix tailTrace_340826
  have hstable : (prefixWord ++ tailWord_340826).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340826).length < 2 ^ (prefixWord ++ tailWord_340826).sum := by decide
  have hdescent : baseEnd_340826 < baseStart_340826 := by decide
  rcases family_descends (prefixWord ++ tailWord_340826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340871 : List Nat := [1, 1, 4, 2, 3, 2, 1, 3, 4]
def baseStart_340871 : Nat := 118140960795 + 340871 * 2 ^ 59
def prefixEnd_340871 : Nat := 4983230072969 + 3 ^ 40 * 340871 * 2
def baseEnd_340871 : Nat := 77791406301707144153275

theorem tailTrace_340871 : CollatzResearch.WordTrace tailWord_340871 prefixEnd_340871 77791406301707144153275 := by
  unfold tailWord_340871
  simp only [CollatzResearch.WordTrace]
  refine ⟨12432586748090057977086467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8288391165393371984724311 12432586748090057977086467)
  ·
    refine ⟨18648880122135086965629701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12432586748090057977086467 18648880122135086965629701)
    ·
      refine ⟨3496665022900328806055569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 18648880122135086965629701 3496665022900328806055569)
      ·
        refine ⟨2622498767175246604541677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3496665022900328806055569 2622498767175246604541677)
        ·
          refine ⟨983437037690717476703129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2622498767175246604541677 983437037690717476703129)
          ·
            refine ⟨737577778268038107527347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 983437037690717476703129 737577778268038107527347)
            ·
              refine ⟨1106366667402057161291021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 737577778268038107527347 1106366667402057161291021)
              ·
                refine ⟨414887500275771435484133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1106366667402057161291021 414887500275771435484133)
                ·
                  refine ⟨77791406301707144153275, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 414887500275771435484133 77791406301707144153275)
                  ·
                    rfl

theorem cell21_340871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 3, 2, 1, 3, 4].length) (baseStart_340871 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340871 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340871 prefixEnd_340871 := by exact prefixLift 340871
  have htrace : WordTrace (prefixWord ++ tailWord_340871) baseStart_340871 baseEnd_340871 := by
    simpa [prefixWord, tailWord_340871, baseEnd_340871] using wordTrace_append hprefix tailTrace_340871
  have hstable : (prefixWord ++ tailWord_340871).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340871).length < 2 ^ (prefixWord ++ tailWord_340871).sum := by decide
  have hdescent : baseEnd_340871 < baseStart_340871 := by decide
  rcases family_descends (prefixWord ++ tailWord_340871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340950 : List Nat := [5, 2, 1, 1, 2, 1, 1, 5, 3]
def baseStart_340950 : Nat := 118140960795 + 340950 * 2 ^ 59
def prefixEnd_340950 : Nat := 4983230072969 + 3 ^ 40 * 340950 * 2
def baseEnd_340950 : Nat := 77809435178020562336447

theorem tailTrace_340950 : CollatzResearch.WordTrace tailWord_340950 prefixEnd_340950 77809435178020562336447 := by
  unfold tailWord_340950
  simp only [CollatzResearch.WordTrace]
  refine ⟨777216757175240904325769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8290312076535902979474869 777216757175240904325769)
  ·
    refine ⟨582912567881430678244327, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 777216757175240904325769 582912567881430678244327)
    ·
      refine ⟨874368851822146017366491, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 582912567881430678244327 874368851822146017366491)
      ·
        refine ⟨1311553277733219026049737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 874368851822146017366491 1311553277733219026049737)
        ·
          refine ⟨983664958299914269537303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1311553277733219026049737 983664958299914269537303)
          ·
            refine ⟨1475497437449871404305955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 983664958299914269537303 1475497437449871404305955)
            ·
              refine ⟨2213246156174807106458933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475497437449871404305955 2213246156174807106458933)
              ·
                refine ⟨207491827141388166230525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2213246156174807106458933 207491827141388166230525)
                ·
                  refine ⟨77809435178020562336447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207491827141388166230525 77809435178020562336447)
                  ·
                    rfl

theorem cell21_340950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 2, 1, 1, 5, 3].length) (baseStart_340950 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340950 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340950 prefixEnd_340950 := by exact prefixLift 340950
  have htrace : WordTrace (prefixWord ++ tailWord_340950) baseStart_340950 baseEnd_340950 := by
    simpa [prefixWord, tailWord_340950, baseEnd_340950] using wordTrace_append hprefix tailTrace_340950
  have hstable : (prefixWord ++ tailWord_340950).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340950).length < 2 ^ (prefixWord ++ tailWord_340950).sum := by decide
  have hdescent : baseEnd_340950 < baseStart_340950 := by decide
  rcases family_descends (prefixWord ++ tailWord_340950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_340975 : List Nat := [1, 1, 2, 1, 4, 3, 1, 3, 5]
def baseStart_340975 : Nat := 118140960795 + 340975 * 2 ^ 59
def prefixEnd_340975 : Nat := 4983230072969 + 3 ^ 40 * 340975 * 2
def baseEnd_340975 : Nat := 77815140518626074419729

theorem tailTrace_340975 : CollatzResearch.WordTrace tailWord_340975 prefixEnd_340975 77815140518626074419729 := by
  unfold tailWord_340975
  simp only [CollatzResearch.WordTrace]
  refine ⟨12436379939713283738872379, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8290919959808855825914919 12436379939713283738872379)
  ·
    refine ⟨18654569909569925608308569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12436379939713283738872379 18654569909569925608308569)
    ·
      refine ⟨13990927432177444206231427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18654569909569925608308569 13990927432177444206231427)
      ·
        refine ⟨20986391148266166309347141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13990927432177444206231427 20986391148266166309347141)
        ·
          refine ⟨3934948340299906183002589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 20986391148266166309347141 3934948340299906183002589)
          ·
            refine ⟨1475605627612464818625971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3934948340299906183002589 1475605627612464818625971)
            ·
              refine ⟨2213408441418697227938957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475605627612464818625971 2213408441418697227938957)
              ·
                refine ⟨830028165532011460477109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2213408441418697227938957 830028165532011460477109)
                ·
                  refine ⟨77815140518626074419729, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830028165532011460477109 77815140518626074419729)
                  ·
                    rfl

theorem cell21_340975_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 3, 1, 3, 5].length) (baseStart_340975 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_340975 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_340975 prefixEnd_340975 := by exact prefixLift 340975
  have htrace : WordTrace (prefixWord ++ tailWord_340975) baseStart_340975 baseEnd_340975 := by
    simpa [prefixWord, tailWord_340975, baseEnd_340975] using wordTrace_append hprefix tailTrace_340975
  have hstable : (prefixWord ++ tailWord_340975).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_340975).length < 2 ^ (prefixWord ++ tailWord_340975).sum := by decide
  have hdescent : baseEnd_340975 < baseStart_340975 := by decide
  rcases family_descends (prefixWord ++ tailWord_340975) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341006 : List Nat := [4, 1, 1, 2, 2, 2, 1, 2, 6]
def baseStart_341006 : Nat := 118140960795 + 341006 * 2 ^ 59
def prefixEnd_341006 : Nat := 4983230072969 + 3 ^ 40 * 341006 * 2
def baseEnd_341006 : Nat := 77822215140976909402999

theorem tailTrace_341006 : CollatzResearch.WordTrace tailWord_341006 prefixEnd_341006 77822215140976909402999 := by
  unfold tailWord_341006
  simp only [CollatzResearch.WordTrace]
  refine ⟨1554688825325122004156359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8291673735067317355500581 1554688825325122004156359)
  ·
    refine ⟨2332033237987683006234539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1554688825325122004156359 2332033237987683006234539)
    ·
      refine ⟨3498049856981524509351809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2332033237987683006234539 3498049856981524509351809)
      ·
        refine ⟨2623537392736143382013857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3498049856981524509351809 2623537392736143382013857)
        ·
          refine ⟨1967653044552107536510393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2623537392736143382013857 1967653044552107536510393)
          ·
            refine ⟨1475739783414080652382795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1967653044552107536510393 1475739783414080652382795)
            ·
              refine ⟨2213609675121120978574193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1475739783414080652382795 2213609675121120978574193)
              ·
                refine ⟨1660207256340840733930645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2213609675121120978574193 1660207256340840733930645)
                ·
                  refine ⟨77822215140976909402999, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1660207256340840733930645 77822215140976909402999)
                  ·
                    rfl

theorem cell21_341006_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 2, 1, 2, 6].length) (baseStart_341006 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341006 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341006 prefixEnd_341006 := by exact prefixLift 341006
  have htrace : WordTrace (prefixWord ++ tailWord_341006) baseStart_341006 baseEnd_341006 := by
    simpa [prefixWord, tailWord_341006, baseEnd_341006] using wordTrace_append hprefix tailTrace_341006
  have hstable : (prefixWord ++ tailWord_341006).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341006).length < 2 ^ (prefixWord ++ tailWord_341006).sum := by decide
  have hdescent : baseEnd_341006 < baseStart_341006 := by decide
  rcases family_descends (prefixWord ++ tailWord_341006) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341026 : List Nat := [3, 3, 1, 1, 1, 4, 3, 2, 3]
def baseStart_341026 : Nat := 118140960795 + 341026 * 2 ^ 59
def prefixEnd_341026 : Nat := 4983230072969 + 3 ^ 40 * 341026 * 2
def baseEnd_341026 : Nat := 77826779413461319069625

theorem tailTrace_341026 : CollatzResearch.WordTrace tailWord_341026 prefixEnd_341026 77826779413461319069625 := by
  unfold tailWord_341026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3109560015632129862244733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8292160041685679632652621 3109560015632129862244733)
  ·
    refine ⟨1166085005862048698341775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3109560015632129862244733 1166085005862048698341775)
    ·
      refine ⟨1749127508793073047512663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166085005862048698341775 1749127508793073047512663)
      ·
        refine ⟨2623691263189609571268995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1749127508793073047512663 2623691263189609571268995)
        ·
          refine ⟨3935536894784414356903493, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2623691263189609571268995 3935536894784414356903493)
          ·
            refine ⟨737913167772077691919405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3935536894784414356903493 737913167772077691919405)
            ·
              refine ⟨276717437914529134469777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 737913167772077691919405 276717437914529134469777)
              ·
                refine ⟨207538078435896850852333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 276717437914529134469777 207538078435896850852333)
                ·
                  refine ⟨77826779413461319069625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207538078435896850852333 77826779413461319069625)
                  ·
                    rfl

theorem cell21_341026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 4, 3, 2, 3].length) (baseStart_341026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341026 prefixEnd_341026 := by exact prefixLift 341026
  have htrace : WordTrace (prefixWord ++ tailWord_341026) baseStart_341026 baseEnd_341026 := by
    simpa [prefixWord, tailWord_341026, baseEnd_341026] using wordTrace_append hprefix tailTrace_341026
  have hstable : (prefixWord ++ tailWord_341026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341026).length < 2 ^ (prefixWord ++ tailWord_341026).sum := by decide
  have hdescent : baseEnd_341026 < baseStart_341026 := by decide
  rcases family_descends (prefixWord ++ tailWord_341026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341065 : List Nat := [1, 2, 1, 1, 2, 2, 2, 4, 6]
def baseStart_341065 : Nat := 118140960795 + 341065 * 2 ^ 59
def prefixEnd_341065 : Nat := 4983230072969 + 3 ^ 40 * 341065 * 2
def baseEnd_341065 : Nat := 77835679744805917919545

theorem tailTrace_341065 : CollatzResearch.WordTrace tailWord_341065 prefixEnd_341065 77835679744805917919545 := by
  unfold tailWord_341065
  simp only [CollatzResearch.WordTrace]
  refine ⟨12439662509387229109648649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8293108339591486073099099 12439662509387229109648649)
  ·
    refine ⟨9329746882040421832236487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12439662509387229109648649 9329746882040421832236487)
    ·
      refine ⟨13994620323060632748354731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9329746882040421832236487 13994620323060632748354731)
      ·
        refine ⟨20991930484590949122532097, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 13994620323060632748354731 20991930484590949122532097)
        ·
          refine ⟨15743947863443211841899073, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 20991930484590949122532097 15743947863443211841899073)
          ·
            refine ⟨11807960897582408881424305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15743947863443211841899073 11807960897582408881424305)
            ·
              refine ⟨8855970673186806661068229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 11807960897582408881424305 8855970673186806661068229)
              ·
                refine ⟨1660494501222526248950293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 8855970673186806661068229 1660494501222526248950293)
                ·
                  refine ⟨77835679744805917919545, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1660494501222526248950293 77835679744805917919545)
                  ·
                    rfl

theorem cell21_341065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 2, 2, 4, 6].length) (baseStart_341065 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341065 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341065 prefixEnd_341065 := by exact prefixLift 341065
  have htrace : WordTrace (prefixWord ++ tailWord_341065) baseStart_341065 baseEnd_341065 := by
    simpa [prefixWord, tailWord_341065, baseEnd_341065] using wordTrace_append hprefix tailTrace_341065
  have hstable : (prefixWord ++ tailWord_341065).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341065).length < 2 ^ (prefixWord ++ tailWord_341065).sum := by decide
  have hdescent : baseEnd_341065 < baseStart_341065 := by decide
  rcases family_descends (prefixWord ++ tailWord_341065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341068 : List Nat := [2, 2, 1, 3, 1, 1, 1, 7, 3]
def baseStart_341068 : Nat := 118140960795 + 341068 * 2 ^ 59
def prefixEnd_341068 : Nat := 4983230072969 + 3 ^ 40 * 341068 * 2
def baseEnd_341068 : Nat := 77836364385678579369539

theorem tailTrace_341068 : CollatzResearch.WordTrace tailWord_341068 prefixEnd_341068 77836364385678579369539 := by
  unfold tailWord_341068
  simp only [CollatzResearch.WordTrace]
  refine ⟨6219885964188180311003929, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8293181285584240414671905 6219885964188180311003929)
  ·
    refine ⟨4664914473141135233252947, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6219885964188180311003929 4664914473141135233252947)
    ·
      refine ⟨6997371709711702849879421, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4664914473141135233252947 6997371709711702849879421)
      ·
        refine ⟨2624014391141888568704783, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 6997371709711702849879421 2624014391141888568704783)
        ·
          refine ⟨3936021586712832853057175, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2624014391141888568704783 3936021586712832853057175)
          ·
            refine ⟨5904032380069249279585763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3936021586712832853057175 5904032380069249279585763)
            ·
              refine ⟨8856048570103873919378645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5904032380069249279585763 8856048570103873919378645)
              ·
                refine ⟨207563638361809544985437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8856048570103873919378645 207563638361809544985437)
                ·
                  refine ⟨77836364385678579369539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207563638361809544985437 77836364385678579369539)
                  ·
                    rfl

theorem cell21_341068_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 1, 1, 7, 3].length) (baseStart_341068 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341068 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341068 prefixEnd_341068 := by exact prefixLift 341068
  have htrace : WordTrace (prefixWord ++ tailWord_341068) baseStart_341068 baseEnd_341068 := by
    simpa [prefixWord, tailWord_341068, baseEnd_341068] using wordTrace_append hprefix tailTrace_341068
  have hstable : (prefixWord ++ tailWord_341068).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341068).length < 2 ^ (prefixWord ++ tailWord_341068).sum := by decide
  have hdescent : baseEnd_341068 < baseStart_341068 := by decide
  rcases family_descends (prefixWord ++ tailWord_341068) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341144 : List Nat := [2, 1, 2, 4, 2, 2, 2, 1, 5]
def baseStart_341144 : Nat := 118140960795 + 341144 * 2 ^ 59
def prefixEnd_341144 : Nat := 4983230072969 + 3 ^ 40 * 341144 * 2
def baseEnd_341144 : Nat := 77853708621119336102717

theorem tailTrace_341144 : CollatzResearch.WordTrace tailWord_341144 prefixEnd_341144 77853708621119336102717 := by
  unfold tailWord_341144
  simp only [CollatzResearch.WordTrace]
  refine ⟨6221271938050512800887243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8295029250734017067849657 6221271938050512800887243)
  ·
    refine ⟨9331907907075769201330865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6221271938050512800887243 9331907907075769201330865)
    ·
      refine ⟨6998930930306826900998149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9331907907075769201330865 6998930930306826900998149)
      ·
        refine ⟨1312299549432530043937153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 6998930930306826900998149 1312299549432530043937153)
        ·
          refine ⟨984224662074397532952865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1312299549432530043937153 984224662074397532952865)
          ·
            refine ⟨738168496555798149714649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 984224662074397532952865 738168496555798149714649)
            ·
              refine ⟨553626372416848612285987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 738168496555798149714649 553626372416848612285987)
              ·
                refine ⟨830439558625272918428981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 553626372416848612285987 830439558625272918428981)
                ·
                  refine ⟨77853708621119336102717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 830439558625272918428981 77853708621119336102717)
                  ·
                    rfl

theorem cell21_341144_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 4, 2, 2, 2, 1, 5].length) (baseStart_341144 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341144 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341144 prefixEnd_341144 := by exact prefixLift 341144
  have htrace : WordTrace (prefixWord ++ tailWord_341144) baseStart_341144 baseEnd_341144 := by
    simpa [prefixWord, tailWord_341144, baseEnd_341144] using wordTrace_append hprefix tailTrace_341144
  have hstable : (prefixWord ++ tailWord_341144).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341144).length < 2 ^ (prefixWord ++ tailWord_341144).sum := by decide
  have hdescent : baseEnd_341144 < baseStart_341144 := by decide
  rcases family_descends (prefixWord ++ tailWord_341144) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341282 : List Nat := [3, 3, 1, 1, 4, 1, 3, 5]
def baseStart_341282 : Nat := 118140960795 + 341282 * 2 ^ 59
def prefixEnd_341282 : Nat := 4983230072969 + 3 ^ 40 * 341282 * 2
def baseEnd_341282 : Nat := 25961734033753920934145

theorem tailTrace_341282 : CollatzResearch.WordTrace tailWord_341282 prefixEnd_341282 25961734033753920934145 := by
  unfold tailWord_341282
  simp only [CollatzResearch.WordTrace]
  refine ⟨3111894287400268792574525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8298384766400716780198733 3111894287400268792574525)
  ·
    refine ⟨1166960357775100797215447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3111894287400268792574525 1166960357775100797215447)
    ·
      refine ⟨1750440536662651195823171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1166960357775100797215447 1750440536662651195823171)
      ·
        refine ⟨2625660804993976793734757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1750440536662651195823171 2625660804993976793734757)
        ·
          refine ⟨492311400936370648825267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2625660804993976793734757 492311400936370648825267)
          ·
            refine ⟨738467101404555973237901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 492311400936370648825267 738467101404555973237901)
            ·
              refine ⟨276925163026708489964213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 738467101404555973237901 276925163026708489964213)
              ·
                refine ⟨25961734033753920934145, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 276925163026708489964213 25961734033753920934145)
                ·
                  rfl

theorem cell21_341282_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 4, 1, 3, 5].length) (baseStart_341282 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341282 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341282 prefixEnd_341282 := by exact prefixLift 341282
  have htrace : WordTrace (prefixWord ++ tailWord_341282) baseStart_341282 baseEnd_341282 := by
    simpa [prefixWord, tailWord_341282, baseEnd_341282] using wordTrace_append hprefix tailTrace_341282
  have hstable : (prefixWord ++ tailWord_341282).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341282).length < 2 ^ (prefixWord ++ tailWord_341282).sum := by decide
  have hdescent : baseEnd_341282 < baseStart_341282 := by decide
  rcases family_descends (prefixWord ++ tailWord_341282) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341296 : List Nat := [2, 1, 1, 1, 2, 2, 6, 3, 3]
def baseStart_341296 : Nat := 118140960795 + 341296 * 2 ^ 59
def prefixEnd_341296 : Nat := 4983230072969 + 3 ^ 40 * 341296 * 2
def baseEnd_341296 : Nat := 77888397092000849569073

theorem tailTrace_341296 : CollatzResearch.WordTrace tailWord_341296 prefixEnd_341296 77888397092000849569073 := by
  unfold tailWord_341296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6224043885775177780653871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8298725181033570374205161 6224043885775177780653871)
  ·
    refine ⟨9336065828662766670980807, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6224043885775177780653871 9336065828662766670980807)
    ·
      refine ⟨14004098742994150006471211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9336065828662766670980807 14004098742994150006471211)
      ·
        refine ⟨21006148114491225009706817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14004098742994150006471211 21006148114491225009706817)
        ·
          refine ⟨15754611085868418757280113, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21006148114491225009706817 15754611085868418757280113)
          ·
            refine ⟨11815958314401314067960085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 15754611085868418757280113 11815958314401314067960085)
            ·
              refine ⟨553873045987561596935629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 11815958314401314067960085 553873045987561596935629)
              ·
                refine ⟨207702392245335598850861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 553873045987561596935629 207702392245335598850861)
                ·
                  refine ⟨77888397092000849569073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207702392245335598850861 77888397092000849569073)
                  ·
                    rfl

theorem cell21_341296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 6, 3, 3].length) (baseStart_341296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341296 prefixEnd_341296 := by exact prefixLift 341296
  have htrace : WordTrace (prefixWord ++ tailWord_341296) baseStart_341296 baseEnd_341296 := by
    simpa [prefixWord, tailWord_341296, baseEnd_341296] using wordTrace_append hprefix tailTrace_341296
  have hstable : (prefixWord ++ tailWord_341296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341296).length < 2 ^ (prefixWord ++ tailWord_341296).sum := by decide
  have hdescent : baseEnd_341296 < baseStart_341296 := by decide
  rcases family_descends (prefixWord ++ tailWord_341296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341302 : List Nat := [5, 1, 2, 3, 2, 1, 1, 2, 4]
def baseStart_341302 : Nat := 118140960795 + 341302 * 2 ^ 59
def prefixEnd_341302 : Nat := 4983230072969 + 3 ^ 40 * 341302 * 2
def baseEnd_341302 : Nat := 77889766373746172469061

theorem tailTrace_341302 : CollatzResearch.WordTrace tailWord_341302 prefixEnd_341302 77889766373746172469061 := by
  unfold tailWord_341302
  simp only [CollatzResearch.WordTrace]
  refine ⟨778019163095538661626635, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8298871073019079057350773 778019163095538661626635)
  ·
    refine ⟨1167028744643307992439953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 778019163095538661626635 1167028744643307992439953)
    ·
      refine ⟨875271558482480994329965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1167028744643307992439953 875271558482480994329965)
      ·
        refine ⟨328226834430930372873737, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 875271558482480994329965 328226834430930372873737)
        ·
          refine ⟨246170125823197779655303, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 328226834430930372873737 246170125823197779655303)
          ·
            refine ⟨369255188734796669482955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 246170125823197779655303 369255188734796669482955)
            ·
              refine ⟨553882783102195004224433, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369255188734796669482955 553882783102195004224433)
              ·
                refine ⟨415412087326646253168325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 553882783102195004224433 415412087326646253168325)
                ·
                  refine ⟨77889766373746172469061, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415412087326646253168325 77889766373746172469061)
                  ·
                    rfl

theorem cell21_341302_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 3, 2, 1, 1, 2, 4].length) (baseStart_341302 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341302 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341302 prefixEnd_341302 := by exact prefixLift 341302
  have htrace : WordTrace (prefixWord ++ tailWord_341302) baseStart_341302 baseEnd_341302 := by
    simpa [prefixWord, tailWord_341302, baseEnd_341302] using wordTrace_append hprefix tailTrace_341302
  have hstable : (prefixWord ++ tailWord_341302).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341302).length < 2 ^ (prefixWord ++ tailWord_341302).sum := by decide
  have hdescent : baseEnd_341302 < baseStart_341302 := by decide
  rcases family_descends (prefixWord ++ tailWord_341302) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341310 : List Nat := [4, 2, 1, 2, 1, 1, 3, 1, 6]
def baseStart_341310 : Nat := 118140960795 + 341310 * 2 ^ 59
def prefixEnd_341310 : Nat := 4983230072969 + 3 ^ 40 * 341310 * 2
def baseEnd_341310 : Nat := 77891592082739936335711

theorem tailTrace_341310 : CollatzResearch.WordTrace tailWord_341310 prefixEnd_341310 77891592082739936335711 := by
  unfold tailWord_341310
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556074799187454494039673, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8299065595666423968211589 1556074799187454494039673)
  ·
    refine ⟨1167056099390590870529755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1556074799187454494039673 1167056099390590870529755)
    ·
      refine ⟨1750584149085886305794633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1167056099390590870529755 1750584149085886305794633)
      ·
        refine ⟨1312938111814414729345975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1750584149085886305794633 1312938111814414729345975)
        ·
          refine ⟨1969407167721622094018963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1312938111814414729345975 1969407167721622094018963)
          ·
            refine ⟨2954110751582433141028445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1969407167721622094018963 2954110751582433141028445)
            ·
              refine ⟨1107791531843412427885667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2954110751582433141028445 1107791531843412427885667)
              ·
                refine ⟨1661687297765118641828501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107791531843412427885667 1661687297765118641828501)
                ·
                  refine ⟨77891592082739936335711, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1661687297765118641828501 77891592082739936335711)
                  ·
                    rfl

theorem cell21_341310_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 1, 1, 3, 1, 6].length) (baseStart_341310 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341310 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341310 prefixEnd_341310 := by exact prefixLift 341310
  have htrace : WordTrace (prefixWord ++ tailWord_341310) baseStart_341310 baseEnd_341310 := by
    simpa [prefixWord, tailWord_341310, baseEnd_341310] using wordTrace_append hprefix tailTrace_341310
  have hstable : (prefixWord ++ tailWord_341310).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341310).length < 2 ^ (prefixWord ++ tailWord_341310).sum := by decide
  have hdescent : baseEnd_341310 < baseStart_341310 := by decide
  rcases family_descends (prefixWord ++ tailWord_341310) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341313 : List Nat := [1, 2, 5, 2, 1, 1, 2, 4, 3]
def baseStart_341313 : Nat := 118140960795 + 341313 * 2 ^ 59
def prefixEnd_341313 : Nat := 4983230072969 + 3 ^ 40 * 341313 * 2
def baseEnd_341313 : Nat := 77892276723612597785705

theorem tailTrace_341313 : CollatzResearch.WordTrace tailWord_341313 prefixEnd_341313 77892276723612597785705 := by
  unfold tailWord_341313
  simp only [CollatzResearch.WordTrace]
  refine ⟨12448707812488767464676593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8299138541659178309784395 12448707812488767464676593)
  ·
    refine ⟨9336530859366575598507445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12448707812488767464676593 9336530859366575598507445)
    ·
      refine ⟨875299768065616462360073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9336530859366575598507445 875299768065616462360073)
      ·
        refine ⟨656474826049212346770055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 875299768065616462360073 656474826049212346770055)
        ·
          refine ⟨984712239073818520155083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 656474826049212346770055 984712239073818520155083)
          ·
            refine ⟨1477068358610727780232625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 984712239073818520155083 1477068358610727780232625)
            ·
              refine ⟨1107801268958045835174469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1477068358610727780232625 1107801268958045835174469)
              ·
                refine ⟨207712737929633594095213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1107801268958045835174469 207712737929633594095213)
                ·
                  refine ⟨77892276723612597785705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207712737929633594095213 77892276723612597785705)
                  ·
                    rfl

theorem cell21_341313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 2, 1, 1, 2, 4, 3].length) (baseStart_341313 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341313 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341313 prefixEnd_341313 := by exact prefixLift 341313
  have htrace : WordTrace (prefixWord ++ tailWord_341313) baseStart_341313 baseEnd_341313 := by
    simpa [prefixWord, tailWord_341313, baseEnd_341313] using wordTrace_append hprefix tailTrace_341313
  have hstable : (prefixWord ++ tailWord_341313).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341313).length < 2 ^ (prefixWord ++ tailWord_341313).sum := by decide
  have hdescent : baseEnd_341313 < baseStart_341313 := by decide
  rcases family_descends (prefixWord ++ tailWord_341313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341358 : List Nat := [4, 1, 2, 4, 1, 2, 7]
def baseStart_341358 : Nat := 118140960795 + 341358 * 2 ^ 59
def prefixEnd_341358 : Nat := 4983230072969 + 3 ^ 40 * 341358 * 2
def baseEnd_341358 : Nat := 8655838481855835503957

theorem tailTrace_341358 : CollatzResearch.WordTrace tailWord_341358 prefixEnd_341358 8655838481855835503957 := by
  unfold tailWord_341358
  simp only [CollatzResearch.WordTrace]
  refine ⟨1556293637165717518758091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8300232731550493433376485 1556293637165717518758091)
  ·
    refine ⟨2334440455748576278137137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1556293637165717518758091 2334440455748576278137137)
    ·
      refine ⟨1750830341811432208602853, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2334440455748576278137137 1750830341811432208602853)
      ·
        refine ⟨328280689089643539113035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1750830341811432208602853 328280689089643539113035)
        ·
          refine ⟨492421033634465308669553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 328280689089643539113035 492421033634465308669553)
          ·
            refine ⟨369315775225848981502165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 492421033634465308669553 369315775225848981502165)
            ·
              refine ⟨8655838481855835503957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 369315775225848981502165 8655838481855835503957)
              ·
                rfl

theorem cell21_341358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 2, 7].length) (baseStart_341358 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341358 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341358 prefixEnd_341358 := by exact prefixLift 341358
  have htrace : WordTrace (prefixWord ++ tailWord_341358) baseStart_341358 baseEnd_341358 := by
    simpa [prefixWord, tailWord_341358, baseEnd_341358] using wordTrace_append hprefix tailTrace_341358
  have hstable : (prefixWord ++ tailWord_341358).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341358).length < 2 ^ (prefixWord ++ tailWord_341358).sum := by decide
  have hdescent : baseEnd_341358 < baseStart_341358 := by decide
  rcases family_descends (prefixWord ++ tailWord_341358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341369 : List Nat := [1, 2, 1, 3, 2, 1, 4, 1, 6]
def baseStart_341369 : Nat := 118140960795 + 341369 * 2 ^ 59
def prefixEnd_341369 : Nat := 4983230072969 + 3 ^ 40 * 341369 * 2
def baseEnd_341369 : Nat := 77905056686568944852257

theorem tailTrace_341369 : CollatzResearch.WordTrace tailWord_341369 prefixEnd_341369 77905056686568944852257 := by
  unfold tailWord_341369
  simp only [CollatzResearch.WordTrace]
  refine ⟨12450750300285889028715161, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8300500200190592685810107 12450750300285889028715161)
  ·
    refine ⟨9338062725214416771536371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12450750300285889028715161 9338062725214416771536371)
    ·
      refine ⟨14007094087821625157304557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9338062725214416771536371 14007094087821625157304557)
      ·
        refine ⟨5252660282933109433989209, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14007094087821625157304557 5252660282933109433989209)
        ·
          refine ⟨3939495212199832075491907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5252660282933109433989209 3939495212199832075491907)
          ·
            refine ⟨5909242818299748113237861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3939495212199832075491907 5909242818299748113237861)
            ·
              refine ⟨1107983028431202771232099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5909242818299748113237861 1107983028431202771232099)
              ·
                refine ⟨1661974542646804156848149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1107983028431202771232099 1661974542646804156848149)
                ·
                  refine ⟨77905056686568944852257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1661974542646804156848149 77905056686568944852257)
                  ·
                    rfl

theorem cell21_341369_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 1, 4, 1, 6].length) (baseStart_341369 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341369 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341369 prefixEnd_341369 := by exact prefixLift 341369
  have htrace : WordTrace (prefixWord ++ tailWord_341369) baseStart_341369 baseEnd_341369 := by
    simpa [prefixWord, tailWord_341369, baseEnd_341369] using wordTrace_append hprefix tailTrace_341369
  have hstable : (prefixWord ++ tailWord_341369).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341369).length < 2 ^ (prefixWord ++ tailWord_341369).sum := by decide
  have hdescent : baseEnd_341369 < baseStart_341369 := by decide
  rcases family_descends (prefixWord ++ tailWord_341369) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341479 : List Nat := [1, 1, 5, 2, 1, 4, 1, 2, 4]
def baseStart_341479 : Nat := 118140960795 + 341479 * 2 ^ 59
def prefixEnd_341479 : Nat := 4983230072969 + 3 ^ 40 * 341479 * 2
def baseEnd_341479 : Nat := 77930160185233198018699

theorem tailTrace_341479 : CollatzResearch.WordTrace tailWord_341479 prefixEnd_341479 77930160185233198018699 := by
  unfold tailWord_341479
  simp only [CollatzResearch.WordTrace]
  refine ⟨12454762329887377815219491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8303174886591585210146327 12454762329887377815219491)
  ·
    refine ⟨18682143494831066722829237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12454762329887377815219491 18682143494831066722829237)
    ·
      refine ⟨1751450952640412505265241, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 18682143494831066722829237 1751450952640412505265241)
      ·
        refine ⟨1313588214480309378948931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1751450952640412505265241 1313588214480309378948931)
        ·
          refine ⟨1970382321720464068423397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1313588214480309378948931 1970382321720464068423397)
          ·
            refine ⟨369446685322587012829387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1970382321720464068423397 369446685322587012829387)
            ·
              refine ⟨554170027983880519244081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 369446685322587012829387 554170027983880519244081)
              ·
                refine ⟨415627520987910389433061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 554170027983880519244081 415627520987910389433061)
                ·
                  refine ⟨77930160185233198018699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415627520987910389433061 77930160185233198018699)
                  ·
                    rfl

theorem cell21_341479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 4, 1, 2, 4].length) (baseStart_341479 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341479 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341479 prefixEnd_341479 := by exact prefixLift 341479
  have htrace : WordTrace (prefixWord ++ tailWord_341479) baseStart_341479 baseEnd_341479 := by
    simpa [prefixWord, tailWord_341479, baseEnd_341479] using wordTrace_append hprefix tailTrace_341479
  have hstable : (prefixWord ++ tailWord_341479).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341479).length < 2 ^ (prefixWord ++ tailWord_341479).sum := by decide
  have hdescent : baseEnd_341479 < baseStart_341479 := by decide
  rcases family_descends (prefixWord ++ tailWord_341479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341535 : List Nat := [1, 1, 2, 4, 1, 1, 11]
def baseStart_341535 : Nat := 118140960795 + 341535 * 2 ^ 59
def prefixEnd_341535 : Nat := 4983230072969 + 3 ^ 40 * 341535 * 2
def baseEnd_341535 : Nat := 8660326683132171676139

theorem tailTrace_341535 : CollatzResearch.WordTrace tailWord_341535 prefixEnd_341535 8660326683132171676139 := by
  unfold tailWord_341535
  simp only [CollatzResearch.WordTrace]
  refine ⟨12456804817684499379258059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8304536545122999586172039 12456804817684499379258059)
  ·
    refine ⟨18685207226526749068887089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12456804817684499379258059 18685207226526749068887089)
    ·
      refine ⟨14013905419895061801665317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18685207226526749068887089 14013905419895061801665317)
      ·
        refine ⟨2627607266230324087812247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14013905419895061801665317 2627607266230324087812247)
        ·
          refine ⟨3941410899345486131718371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2627607266230324087812247 3941410899345486131718371)
          ·
            refine ⟨5912116349018229197577557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3941410899345486131718371 5912116349018229197577557)
            ·
              refine ⟨8660326683132171676139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 11 5912116349018229197577557 8660326683132171676139)
              ·
                rfl

theorem cell21_341535_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 11].length) (baseStart_341535 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341535 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341535 prefixEnd_341535 := by exact prefixLift 341535
  have htrace : WordTrace (prefixWord ++ tailWord_341535) baseStart_341535 baseEnd_341535 := by
    simpa [prefixWord, tailWord_341535, baseEnd_341535] using wordTrace_append hprefix tailTrace_341535
  have hstable : (prefixWord ++ tailWord_341535).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341535).length < 2 ^ (prefixWord ++ tailWord_341535).sum := by decide
  have hdescent : baseEnd_341535 < baseStart_341535 := by decide
  rcases family_descends (prefixWord ++ tailWord_341535) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341555 : List Nat := [1, 1, 1, 2, 4, 5, 2, 1, 4]
def baseStart_341555 : Nat := 118140960795 + 341555 * 2 ^ 59
def prefixEnd_341555 : Nat := 4983230072969 + 3 ^ 40 * 341555 * 2
def baseEnd_341555 : Nat := 77947504420673954751877

theorem tailTrace_341555 : CollatzResearch.WordTrace tailWord_341555 prefixEnd_341555 77947504420673954751877 := by
  unfold tailWord_341555
  simp only [CollatzResearch.WordTrace]
  refine ⟨12457534277612042794986119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8305022851741361863324079 12457534277612042794986119)
  ·
    refine ⟨18686301416418064192479179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12457534277612042794986119 18686301416418064192479179)
    ·
      refine ⟨28029452124627096288718769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18686301416418064192479179 28029452124627096288718769)
      ·
        refine ⟨21022089093470322216539077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28029452124627096288718769 21022089093470322216539077)
        ·
          refine ⟨3941641705025685415601077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21022089093470322216539077 3941641705025685415601077)
          ·
            refine ⟨369528909846158007712601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3941641705025685415601077 369528909846158007712601)
            ·
              refine ⟨277146682384618505784451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 369528909846158007712601 277146682384618505784451)
              ·
                refine ⟨415720023576927758676677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 277146682384618505784451 415720023576927758676677)
                ·
                  refine ⟨77947504420673954751877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 415720023576927758676677 77947504420673954751877)
                  ·
                    rfl

theorem cell21_341555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 5, 2, 1, 4].length) (baseStart_341555 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341555 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341555 prefixEnd_341555 := by exact prefixLift 341555
  have htrace : WordTrace (prefixWord ++ tailWord_341555) baseStart_341555 baseEnd_341555 := by
    simpa [prefixWord, tailWord_341555, baseEnd_341555] using wordTrace_append hprefix tailTrace_341555
  have hstable : (prefixWord ++ tailWord_341555).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341555).length < 2 ^ (prefixWord ++ tailWord_341555).sum := by decide
  have hdescent : baseEnd_341555 < baseStart_341555 := by decide
  rcases family_descends (prefixWord ++ tailWord_341555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341583 : List Nat := [1, 1, 2, 1, 1, 2, 3, 7, 3]
def baseStart_341583 : Nat := 118140960795 + 341583 * 2 ^ 59
def prefixEnd_341583 : Nat := 4983230072969 + 3 ^ 40 * 341583 * 2
def baseEnd_341583 : Nat := 77953894402152128285153

theorem tailTrace_341583 : CollatzResearch.WordTrace tailWord_341583 prefixEnd_341583 77953894402152128285153 := by
  unfold tailWord_341583
  simp only [CollatzResearch.WordTrace]
  refine ⟨12458555521510603577005403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8305703681007069051336935 12458555521510603577005403)
  ·
    refine ⟨18687833282265905365508105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12458555521510603577005403 18687833282265905365508105)
    ·
      refine ⟨14015874961699429024131079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18687833282265905365508105 14015874961699429024131079)
      ·
        refine ⟨21023812442549143536196619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14015874961699429024131079 21023812442549143536196619)
        ·
          refine ⟨31535718663823715304294929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21023812442549143536196619 31535718663823715304294929)
          ·
            refine ⟨23651788997867786478221197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 31535718663823715304294929 23651788997867786478221197)
            ·
              refine ⟨8869420874200419929332949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 23651788997867786478221197 8869420874200419929332949)
              ·
                refine ⟨207877051739072342093741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 8869420874200419929332949 207877051739072342093741)
                ·
                  refine ⟨77953894402152128285153, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 207877051739072342093741 77953894402152128285153)
                  ·
                    rfl

theorem cell21_341583_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 3, 7, 3].length) (baseStart_341583 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341583 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341583 prefixEnd_341583 := by exact prefixLift 341583
  have htrace : WordTrace (prefixWord ++ tailWord_341583) baseStart_341583 baseEnd_341583 := by
    simpa [prefixWord, tailWord_341583, baseEnd_341583] using wordTrace_append hprefix tailTrace_341583
  have hstable : (prefixWord ++ tailWord_341583).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341583).length < 2 ^ (prefixWord ++ tailWord_341583).sum := by decide
  have hdescent : baseEnd_341583 < baseStart_341583 := by decide
  rcases family_descends (prefixWord ++ tailWord_341583) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341856 : List Nat := [2, 1, 1, 3, 3, 2, 4, 5]
def baseStart_341856 : Nat := 118140960795 + 341856 * 2 ^ 59
def prefixEnd_341856 : Nat := 4983230072969 + 3 ^ 40 * 341856 * 2
def baseEnd_341856 : Nat := 26005398907188106744865

theorem tailTrace_341856 : CollatzResearch.WordTrace tailWord_341856 prefixEnd_341856 26005398907188106744865 := by
  unfold tailWord_341856
  simp only [CollatzResearch.WordTrace]
  refine ⟨6234256324760785600846711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8312341766347714134462281 6234256324760785600846711)
  ·
    refine ⟨9351384487141178401270067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6234256324760785600846711 9351384487141178401270067)
    ·
      refine ⟨14027076730711767601905101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9351384487141178401270067 14027076730711767601905101)
      ·
        refine ⟨5260153774016912850714413, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14027076730711767601905101 5260153774016912850714413)
        ·
          refine ⟨1972557665256342319017905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5260153774016912850714413 1972557665256342319017905)
          ·
            refine ⟨1479418248942256739263429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1972557665256342319017905 1479418248942256739263429)
            ·
              refine ⟨277390921676673138611893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1479418248942256739263429 277390921676673138611893)
              ·
                refine ⟨26005398907188106744865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 277390921676673138611893 26005398907188106744865)
                ·
                  rfl

theorem cell21_341856_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 2, 4, 5].length) (baseStart_341856 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341856 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341856 prefixEnd_341856 := by exact prefixLift 341856
  have htrace : WordTrace (prefixWord ++ tailWord_341856) baseStart_341856 baseEnd_341856 := by
    simpa [prefixWord, tailWord_341856, baseEnd_341856] using wordTrace_append hprefix tailTrace_341856
  have hstable : (prefixWord ++ tailWord_341856).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341856).length < 2 ^ (prefixWord ++ tailWord_341856).sum := by decide
  have hdescent : baseEnd_341856 < baseStart_341856 := by decide
  rcases family_descends (prefixWord ++ tailWord_341856) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_341929 : List Nat := [1, 2, 1, 1, 1, 1, 4, 1, 9]
def baseStart_341929 : Nat := 118140960795 + 341929 * 2 ^ 59
def prefixEnd_341929 : Nat := 4983230072969 + 3 ^ 40 * 341929 * 2
def baseEnd_341929 : Nat := 78032856316132415517779

theorem tailTrace_341929 : CollatzResearch.WordTrace tailWord_341929 prefixEnd_341929 78032856316132415517779 := by
  unfold tailWord_341929
  simp only [CollatzResearch.WordTrace]
  refine ⟨12471175178257104669100841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8314116785504736446067227 12471175178257104669100841)
  ·
    refine ⟨9353381383692828501825631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12471175178257104669100841 9353381383692828501825631)
    ·
      refine ⟨14030072075539242752738447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9353381383692828501825631 14030072075539242752738447)
      ·
        refine ⟨21045108113308864129107671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14030072075539242752738447 21045108113308864129107671)
        ·
          refine ⟨31567662169963296193661507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21045108113308864129107671 31567662169963296193661507)
          ·
            refine ⟨47351493254944944290492261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31567662169963296193661507 47351493254944944290492261)
            ·
              refine ⟨8878404985302177054467299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 47351493254944944290492261 8878404985302177054467299)
              ·
                refine ⟨13317607477953265581700949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 8878404985302177054467299 13317607477953265581700949)
                ·
                  refine ⟨78032856316132415517779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13317607477953265581700949 78032856316132415517779)
                  ·
                    rfl

theorem cell21_341929_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 4, 1, 9].length) (baseStart_341929 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_341929 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_341929 prefixEnd_341929 := by exact prefixLift 341929
  have htrace : WordTrace (prefixWord ++ tailWord_341929) baseStart_341929 baseEnd_341929 := by
    simpa [prefixWord, tailWord_341929, baseEnd_341929] using wordTrace_append hprefix tailTrace_341929
  have hstable : (prefixWord ++ tailWord_341929).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_341929).length < 2 ^ (prefixWord ++ tailWord_341929).sum := by decide
  have hdescent : baseEnd_341929 < baseStart_341929 := by decide
  rcases family_descends (prefixWord ++ tailWord_341929) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342070 : List Nat := [5, 1, 2, 1, 1, 1, 3, 3, 4]
def baseStart_342070 : Nat := 118140960795 + 342070 * 2 ^ 59
def prefixEnd_342070 : Nat := 4983230072969 + 3 ^ 40 * 342070 * 2
def baseEnd_342070 : Nat := 78065034437147503667491

theorem tailTrace_342070 : CollatzResearch.WordTrace tailWord_342070 prefixEnd_342070 78065034437147503667491 := by
  unfold tailWord_342070
  simp only [CollatzResearch.WordTrace]
  refine ⟨779769866921642859373979, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8317545247164190499989109 779769866921642859373979)
  ·
    refine ⟨1169654800382464289060969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 779769866921642859373979 1169654800382464289060969)
    ·
      refine ⟨877241100286848216795727, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1169654800382464289060969 877241100286848216795727)
      ·
        refine ⟨1315861650430272325193591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 877241100286848216795727 1315861650430272325193591)
        ·
          refine ⟨1973792475645408487790387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1315861650430272325193591 1973792475645408487790387)
          ·
            refine ⟨2960688713468112731685581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1973792475645408487790387 2960688713468112731685581)
            ·
              refine ⟨1110258267550542274382093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2960688713468112731685581 1110258267550542274382093)
              ·
                refine ⟨416346850331453352893285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1110258267550542274382093 416346850331453352893285)
                ·
                  refine ⟨78065034437147503667491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 416346850331453352893285 78065034437147503667491)
                  ·
                    rfl

theorem cell21_342070_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 1, 1, 3, 3, 4].length) (baseStart_342070 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342070 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342070 prefixEnd_342070 := by exact prefixLift 342070
  have htrace : WordTrace (prefixWord ++ tailWord_342070) baseStart_342070 baseEnd_342070 := by
    simpa [prefixWord, tailWord_342070, baseEnd_342070] using wordTrace_append hprefix tailTrace_342070
  have hstable : (prefixWord ++ tailWord_342070).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342070).length < 2 ^ (prefixWord ++ tailWord_342070).sum := by decide
  have hdescent : baseEnd_342070 < baseStart_342070 := by decide
  rcases family_descends (prefixWord ++ tailWord_342070) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342208 : List Nat := [2, 1, 1, 2, 5, 3, 1, 3, 3]
def baseStart_342208 : Nat := 118140960795 + 342208 * 2 ^ 59
def prefixEnd_342208 : Nat := 4983230072969 + 3 ^ 40 * 342208 * 2
def baseEnd_342208 : Nat := 78096527917289930367209

theorem tailTrace_342208 : CollatzResearch.WordTrace tailWord_342208 prefixEnd_342208 78096527917289930367209 := by
  unfold tailWord_342208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6240675572123167659253639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8320900762830890212338185 6240675572123167659253639)
  ·
    refine ⟨9361013358184751488880459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6240675572123167659253639 9361013358184751488880459)
    ·
      refine ⟨14041520037277127233320689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9361013358184751488880459 14041520037277127233320689)
      ·
        refine ⟨10531140027957845424990517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14041520037277127233320689 10531140027957845424990517)
        ·
          refine ⟨987294377621048008592861, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10531140027957845424990517 987294377621048008592861)
          ·
            refine ⟨370235391607893003222323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 987294377621048008592861 370235391607893003222323)
            ·
              refine ⟨555353087411839504833485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370235391607893003222323 555353087411839504833485)
              ·
                refine ⟨208257407779439814312557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555353087411839504833485 208257407779439814312557)
                ·
                  refine ⟨78096527917289930367209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208257407779439814312557 78096527917289930367209)
                  ·
                    rfl

theorem cell21_342208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 5, 3, 1, 3, 3].length) (baseStart_342208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342208 prefixEnd_342208 := by exact prefixLift 342208
  have htrace : WordTrace (prefixWord ++ tailWord_342208) baseStart_342208 baseEnd_342208 := by
    simpa [prefixWord, tailWord_342208, baseEnd_342208] using wordTrace_append hprefix tailTrace_342208
  have hstable : (prefixWord ++ tailWord_342208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342208).length < 2 ^ (prefixWord ++ tailWord_342208).sum := by decide
  have hdescent : baseEnd_342208 < baseStart_342208 := by decide
  rcases family_descends (prefixWord ++ tailWord_342208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342281 : List Nat := [1, 2, 1, 1, 3, 5, 2, 2, 4]
def baseStart_342281 : Nat := 118140960795 + 342281 * 2 ^ 59
def prefixEnd_342281 : Nat := 4983230072969 + 3 ^ 40 * 342281 * 2
def baseEnd_342281 : Nat := 78113187511858025650393

theorem tailTrace_342281 : CollatzResearch.WordTrace tailWord_342281 prefixEnd_342281 78113187511858025650393 := by
  unfold tailWord_342281
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484013672981868785914697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8322675781987912523943131 12484013672981868785914697)
  ·
    refine ⟨9363010254736401589436023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12484013672981868785914697 9363010254736401589436023)
    ·
      refine ⟨14044515382104602384154035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9363010254736401589436023 14044515382104602384154035)
      ·
        refine ⟨21066773073156903576231053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14044515382104602384154035 21066773073156903576231053)
        ·
          refine ⟨7900039902433838841086645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21066773073156903576231053 7900039902433838841086645)
          ·
            refine ⟨740628740853172391351873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7900039902433838841086645 740628740853172391351873)
            ·
              refine ⟨555471555639879293513905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 740628740853172391351873 555471555639879293513905)
              ·
                refine ⟨416603666729909470135429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 555471555639879293513905 416603666729909470135429)
                ·
                  refine ⟨78113187511858025650393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 416603666729909470135429 78113187511858025650393)
                  ·
                    rfl

theorem cell21_342281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 5, 2, 2, 4].length) (baseStart_342281 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342281 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342281 prefixEnd_342281 := by exact prefixLift 342281
  have htrace : WordTrace (prefixWord ++ tailWord_342281) baseStart_342281 baseEnd_342281 := by
    simpa [prefixWord, tailWord_342281, baseEnd_342281] using wordTrace_append hprefix tailTrace_342281
  have hstable : (prefixWord ++ tailWord_342281).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342281).length < 2 ^ (prefixWord ++ tailWord_342281).sum := by decide
  have hdescent : baseEnd_342281 < baseStart_342281 := by decide
  rcases family_descends (prefixWord ++ tailWord_342281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342295 : List Nat := [1, 1, 3, 4, 1, 2, 3, 6]
def baseStart_342295 : Nat := 118140960795 + 342295 * 2 ^ 59
def prefixEnd_342295 : Nat := 4983230072969 + 3 ^ 40 * 342295 * 2
def baseEnd_342295 : Nat := 26038794167532370805677

theorem tailTrace_342295 : CollatzResearch.WordTrace tailWord_342295 prefixEnd_342295 26038794167532370805677 := by
  unfold tailWord_342295
  simp only [CollatzResearch.WordTrace]
  refine ⟨12484524294931149176924339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8323016196620766117949559 12484524294931149176924339)
  ·
    refine ⟨18726786442396723765386509, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12484524294931149176924339 18726786442396723765386509)
    ·
      refine ⟨7022544915898771412019941, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18726786442396723765386509 7022544915898771412019941)
      ·
        refine ⟨1316727171731019639753739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7022544915898771412019941 1316727171731019639753739)
        ·
          refine ⟨1975090757596529459630609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1316727171731019639753739 1975090757596529459630609)
          ·
            refine ⟨1481318068197397094722957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1975090757596529459630609 1481318068197397094722957)
            ·
              refine ⟨555494275574023910521109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1481318068197397094722957 555494275574023910521109)
              ·
                refine ⟨26038794167532370805677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 555494275574023910521109 26038794167532370805677)
                ·
                  rfl

theorem cell21_342295_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 6].length) (baseStart_342295 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342295 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342295 prefixEnd_342295 := by exact prefixLift 342295
  have htrace : WordTrace (prefixWord ++ tailWord_342295) baseStart_342295 baseEnd_342295 := by
    simpa [prefixWord, tailWord_342295, baseEnd_342295] using wordTrace_append hprefix tailTrace_342295
  have hstable : (prefixWord ++ tailWord_342295).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342295).length < 2 ^ (prefixWord ++ tailWord_342295).sum := by decide
  have hdescent : baseEnd_342295 < baseStart_342295 := by decide
  rcases family_descends (prefixWord ++ tailWord_342295) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342453 : List Nat := [1, 3, 3, 2, 3, 2, 2, 2, 3]
def baseStart_342453 : Nat := 118140960795 + 342453 * 2 ^ 59
def prefixEnd_342453 : Nat := 4983230072969 + 3 ^ 40 * 342453 * 2
def baseEnd_342453 : Nat := 78152440255223948783375

theorem tailTrace_342453 : CollatzResearch.WordTrace tailWord_342453 prefixEnd_342453 78152440255223948783375 := by
  unfold tailWord_342453
  simp only [CollatzResearch.WordTrace]
  refine ⟨12490287028358742161176013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8326858018905828107450675 12490287028358742161176013)
  ·
    refine ⟨4683857635634528310441005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12490287028358742161176013 4683857635634528310441005)
    ·
      refine ⟨1756446613362948116415377, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4683857635634528310441005 1756446613362948116415377)
      ·
        refine ⟨1317334960022211087311533, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1756446613362948116415377 1317334960022211087311533)
        ·
          refine ⟨494000610008329157741825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1317334960022211087311533 494000610008329157741825)
          ·
            refine ⟨370500457506246868306369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 494000610008329157741825 370500457506246868306369)
            ·
              refine ⟨277875343129685151229777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370500457506246868306369 277875343129685151229777)
              ·
                refine ⟨208406507347263863422333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 277875343129685151229777 208406507347263863422333)
                ·
                  refine ⟨78152440255223948783375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208406507347263863422333 78152440255223948783375)
                  ·
                    rfl

theorem cell21_342453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 2, 2, 2, 3].length) (baseStart_342453 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342453 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342453 prefixEnd_342453 := by exact prefixLift 342453
  have htrace : WordTrace (prefixWord ++ tailWord_342453) baseStart_342453 baseEnd_342453 := by
    simpa [prefixWord, tailWord_342453, baseEnd_342453] using wordTrace_append hprefix tailTrace_342453
  have hstable : (prefixWord ++ tailWord_342453).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342453).length < 2 ^ (prefixWord ++ tailWord_342453).sum := by decide
  have hdescent : baseEnd_342453 < baseStart_342453 := by decide
  rcases family_descends (prefixWord ++ tailWord_342453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342475 : List Nat := [1, 1, 1, 1, 3, 3, 1, 2, 8]
def baseStart_342475 : Nat := 118140960795 + 342475 * 2 ^ 59
def prefixEnd_342475 : Nat := 4983230072969 + 3 ^ 40 * 342475 * 2
def baseEnd_342475 : Nat := 78157460954956799416663

theorem tailTrace_342475 : CollatzResearch.WordTrace tailWord_342475 prefixEnd_342475 78157460954956799416663 := by
  unfold tailWord_342475
  simp only [CollatzResearch.WordTrace]
  refine ⟨12491089434279039918476879, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8327392956186026612317919 12491089434279039918476879)
  ·
    refine ⟨18736634151418559877715319, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12491089434279039918476879 18736634151418559877715319)
    ·
      refine ⟨28104951227127839816572979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18736634151418559877715319 28104951227127839816572979)
      ·
        refine ⟨42157426840691759724859469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28104951227127839816572979 42157426840691759724859469)
        ·
          refine ⟨15809035065259409896822301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 42157426840691759724859469 15809035065259409896822301)
          ·
            refine ⟨5928388149472278711308363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15809035065259409896822301 5928388149472278711308363)
            ·
              refine ⟨8892582224208418066962545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 5928388149472278711308363 8892582224208418066962545)
              ·
                refine ⟨6669436668156313550221909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 8892582224208418066962545 6669436668156313550221909)
                ·
                  refine ⟨78157460954956799416663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6669436668156313550221909 78157460954956799416663)
                  ·
                    rfl

theorem cell21_342475_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 1, 2, 8].length) (baseStart_342475 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342475 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342475 prefixEnd_342475 := by exact prefixLift 342475
  have htrace : WordTrace (prefixWord ++ tailWord_342475) baseStart_342475 baseEnd_342475 := by
    simpa [prefixWord, tailWord_342475, baseEnd_342475] using wordTrace_append hprefix tailTrace_342475
  have hstable : (prefixWord ++ tailWord_342475).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342475).length < 2 ^ (prefixWord ++ tailWord_342475).sum := by decide
  have hdescent : baseEnd_342475 < baseStart_342475 := by decide
  rcases family_descends (prefixWord ++ tailWord_342475) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342495 : List Nat := [1, 1, 2, 3, 3, 3, 2, 3, 3]
def baseStart_342495 : Nat := 118140960795 + 342495 * 2 ^ 59
def prefixEnd_342495 : Nat := 4983230072969 + 3 ^ 40 * 342495 * 2
def baseEnd_342495 : Nat := 78162025227441209083289

theorem tailTrace_342495 : CollatzResearch.WordTrace tailWord_342495 prefixEnd_342495 78162025227441209083289 := by
  unfold tailWord_342495
  simp only [CollatzResearch.WordTrace]
  refine ⟨12491818894206583334204939, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8327879262804388889469959 12491818894206583334204939)
  ·
    refine ⟨18737728341309875001307409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12491818894206583334204939 18737728341309875001307409)
    ·
      refine ⟨14053296255982406250980557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18737728341309875001307409 14053296255982406250980557)
      ·
        refine ⟨5269986095993402344117709, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14053296255982406250980557 5269986095993402344117709)
        ·
          refine ⟨1976244785997525879044141, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5269986095993402344117709 1976244785997525879044141)
          ·
            refine ⟨741091794749072204641553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1976244785997525879044141 741091794749072204641553)
            ·
              refine ⟨555818846061804153481165, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 741091794749072204641553 555818846061804153481165)
              ·
                refine ⟨208432067273176557555437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 555818846061804153481165 208432067273176557555437)
                ·
                  refine ⟨78162025227441209083289, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208432067273176557555437 78162025227441209083289)
                  ·
                    rfl

theorem cell21_342495_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 3, 3, 2, 3, 3].length) (baseStart_342495 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342495 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342495 prefixEnd_342495 := by exact prefixLift 342495
  have htrace : WordTrace (prefixWord ++ tailWord_342495) baseStart_342495 baseEnd_342495 := by
    simpa [prefixWord, tailWord_342495, baseEnd_342495] using wordTrace_append hprefix tailTrace_342495
  have hstable : (prefixWord ++ tailWord_342495).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342495).length < 2 ^ (prefixWord ++ tailWord_342495).sum := by decide
  have hdescent : baseEnd_342495 < baseStart_342495 := by decide
  rcases family_descends (prefixWord ++ tailWord_342495) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342509 : List Nat := [1, 5, 1, 3, 1, 2, 1, 1, 6]
def baseStart_342509 : Nat := 118140960795 + 342509 * 2 ^ 59
def prefixEnd_342509 : Nat := 4983230072969 + 3 ^ 40 * 342509 * 2
def baseEnd_342509 : Nat := 78165220218180295849927

theorem tailTrace_342509 : CollatzResearch.WordTrace tailWord_342509 prefixEnd_342509 78165220218180295849927 := by
  unfold tailWord_342509
  simp only [CollatzResearch.WordTrace]
  refine ⟨12492329516155863725214581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8328219677437242483476387 12492329516155863725214581)
  ·
    refine ⟨1171155892139612224238867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12492329516155863725214581 1171155892139612224238867)
    ·
      refine ⟨1756733838209418336358301, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1171155892139612224238867 1756733838209418336358301)
      ·
        refine ⟨658775189328531876134363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1756733838209418336358301 658775189328531876134363)
        ·
          refine ⟨988162783992797814201545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 658775189328531876134363 988162783992797814201545)
          ·
            refine ⟨741122087994598360651159, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 988162783992797814201545 741122087994598360651159)
            ·
              refine ⟨1111683131991897540976739, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741122087994598360651159 1111683131991897540976739)
              ·
                refine ⟨1667524697987846311465109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1111683131991897540976739 1667524697987846311465109)
                ·
                  refine ⟨78165220218180295849927, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1667524697987846311465109 78165220218180295849927)
                  ·
                    rfl

theorem cell21_342509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 3, 1, 2, 1, 1, 6].length) (baseStart_342509 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342509 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342509 prefixEnd_342509 := by exact prefixLift 342509
  have htrace : WordTrace (prefixWord ++ tailWord_342509) baseStart_342509 baseEnd_342509 := by
    simpa [prefixWord, tailWord_342509, baseEnd_342509] using wordTrace_append hprefix tailTrace_342509
  have hstable : (prefixWord ++ tailWord_342509).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342509).length < 2 ^ (prefixWord ++ tailWord_342509).sum := by decide
  have hdescent : baseEnd_342509 < baseStart_342509 := by decide
  rcases family_descends (prefixWord ++ tailWord_342509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342540 : List Nat := [2, 2, 1, 2, 4, 3, 2, 5]
def baseStart_342540 : Nat := 118140960795 + 342540 * 2 ^ 59
def prefixEnd_342540 : Nat := 4983230072969 + 3 ^ 40 * 342540 * 2
def baseEnd_342540 : Nat := 26057431613510376944399

theorem tailTrace_342540 : CollatzResearch.WordTrace tailWord_342540 prefixEnd_342540 26057431613510376944399 := by
  unfold tailWord_342540
  simp only [CollatzResearch.WordTrace]
  refine ⟨6246730089521778009796537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8328973452695704013062049 6246730089521778009796537)
  ·
    refine ⟨4685047567141333507347403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6246730089521778009796537 4685047567141333507347403)
    ·
      refine ⟨7027571350712000261021105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4685047567141333507347403 7027571350712000261021105)
      ·
        refine ⟨5270678513034000195765829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7027571350712000261021105 5270678513034000195765829)
        ·
          refine ⟨988252221193875036706093, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5270678513034000195765829 988252221193875036706093)
          ·
            refine ⟨370594582947703138764785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 988252221193875036706093 370594582947703138764785)
            ·
              refine ⟨277945937210777354073589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 370594582947703138764785 277945937210777354073589)
              ·
                refine ⟨26057431613510376944399, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 277945937210777354073589 26057431613510376944399)
                ·
                  rfl

theorem cell21_342540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 3, 2, 5].length) (baseStart_342540 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342540 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342540 prefixEnd_342540 := by exact prefixLift 342540
  have htrace : WordTrace (prefixWord ++ tailWord_342540) baseStart_342540 baseEnd_342540 := by
    simpa [prefixWord, tailWord_342540, baseEnd_342540] using wordTrace_append hprefix tailTrace_342540
  have hstable : (prefixWord ++ tailWord_342540).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342540).length < 2 ^ (prefixWord ++ tailWord_342540).sum := by decide
  have hdescent : baseEnd_342540 < baseStart_342540 := by decide
  rcases family_descends (prefixWord ++ tailWord_342540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342622 : List Nat := [4, 4, 1, 2, 1, 1, 1, 4, 3]
def baseStart_342622 : Nat := 118140960795 + 342622 * 2 ^ 59
def prefixEnd_342622 : Nat := 4983230072969 + 3 ^ 40 * 342622 * 2
def baseEnd_342622 : Nat := 78191008357717210466363

theorem tailTrace_342622 : CollatzResearch.WordTrace tailWord_342622 prefixEnd_342622 78191008357717210466363 := by
  unfold tailWord_342622
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562056370593310503009765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8330967309830989349385413 1562056370593310503009765)
  ·
    refine ⟨292885569486245719314331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1562056370593310503009765 292885569486245719314331)
    ·
      refine ⟨439328354229368578971497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 292885569486245719314331 439328354229368578971497)
      ·
        refine ⟨329496265672026434228623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 439328354229368578971497 329496265672026434228623)
        ·
          refine ⟨494244398508039651342935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329496265672026434228623 494244398508039651342935)
          ·
            refine ⟨741366597762059477014403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494244398508039651342935 741366597762059477014403)
            ·
              refine ⟨1112049896643089215521605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 741366597762059477014403 1112049896643089215521605)
              ·
                refine ⟨208509355620579227910301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1112049896643089215521605 208509355620579227910301)
                ·
                  refine ⟨78191008357717210466363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 208509355620579227910301 78191008357717210466363)
                  ·
                    rfl

theorem cell21_342622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 2, 1, 1, 1, 4, 3].length) (baseStart_342622 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342622 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342622 prefixEnd_342622 := by exact prefixLift 342622
  have htrace : WordTrace (prefixWord ++ tailWord_342622) baseStart_342622 baseEnd_342622 := by
    simpa [prefixWord, tailWord_342622, baseEnd_342622] using wordTrace_append hprefix tailTrace_342622
  have hstable : (prefixWord ++ tailWord_342622).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342622).length < 2 ^ (prefixWord ++ tailWord_342622).sum := by decide
  have hdescent : baseEnd_342622 < baseStart_342622 := by decide
  rcases family_descends (prefixWord ++ tailWord_342622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342695 : List Nat := [1, 1, 6, 3, 1, 1, 3, 1, 4]
def baseStart_342695 : Nat := 118140960795 + 342695 * 2 ^ 59
def prefixEnd_342695 : Nat := 4983230072969 + 3 ^ 40 * 342695 * 2
def baseEnd_342695 : Nat := 78207667952285305749547

theorem tailTrace_342695 : CollatzResearch.WordTrace tailWord_342695 prefixEnd_342695 78207667952285305749547 := by
  unfold tailWord_342695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12499113493482017491485539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8332742328988011660990359 12499113493482017491485539)
  ·
    refine ⟨18748670240223026237228309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12499113493482017491485539 18748670240223026237228309)
    ·
      refine ⟨878843917510454354870077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 18748670240223026237228309 878843917510454354870077)
      ·
        refine ⟨329566469066420383076279, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 878843917510454354870077 329566469066420383076279)
        ·
          refine ⟨494349703599630574614419, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 329566469066420383076279 494349703599630574614419)
          ·
            refine ⟨741524555399445861921629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 494349703599630574614419 741524555399445861921629)
            ·
              refine ⟨278071708274792198220611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 741524555399445861921629 278071708274792198220611)
              ·
                refine ⟨417107562412188297330917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278071708274792198220611 417107562412188297330917)
                ·
                  refine ⟨78207667952285305749547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417107562412188297330917 78207667952285305749547)
                  ·
                    rfl

theorem cell21_342695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 3, 1, 1, 3, 1, 4].length) (baseStart_342695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342695 prefixEnd_342695 := by exact prefixLift 342695
  have htrace : WordTrace (prefixWord ++ tailWord_342695) baseStart_342695 baseEnd_342695 := by
    simpa [prefixWord, tailWord_342695, baseEnd_342695] using wordTrace_append hprefix tailTrace_342695
  have hstable : (prefixWord ++ tailWord_342695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342695).length < 2 ^ (prefixWord ++ tailWord_342695).sum := by decide
  have hdescent : baseEnd_342695 < baseStart_342695 := by decide
  rcases family_descends (prefixWord ++ tailWord_342695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342726 : List Nat := [6, 1, 2, 1, 3, 1, 7]
def baseStart_342726 : Nat := 118140960795 + 342726 * 2 ^ 59
def prefixEnd_342726 : Nat := 4983230072969 + 3 ^ 40 * 342726 * 2
def baseEnd_342726 : Nat := 8690526952737348970313

theorem tailTrace_342726 : CollatzResearch.WordTrace tailWord_342726 prefixEnd_342726 8690526952737348970313 := by
  unfold tailWord_342726
  simp only [CollatzResearch.WordTrace]
  refine ⟨390632629886553430808251, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8333496104246473190576021 390632629886553430808251)
  ·
    refine ⟨585948944829830146212377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 390632629886553430808251 585948944829830146212377)
    ·
      refine ⟨439461708622372609659283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 585948944829830146212377 439461708622372609659283)
      ·
        refine ⟨659192562933558914488925, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439461708622372609659283 659192562933558914488925)
        ·
          refine ⟨247197211100084592933347, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 659192562933558914488925 247197211100084592933347)
          ·
            refine ⟨370795816650126889400021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247197211100084592933347 370795816650126889400021)
            ·
              refine ⟨8690526952737348970313, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 370795816650126889400021 8690526952737348970313)
              ·
                rfl

theorem cell21_342726_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 3, 1, 7].length) (baseStart_342726 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342726 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342726 prefixEnd_342726 := by exact prefixLift 342726
  have htrace : WordTrace (prefixWord ++ tailWord_342726) baseStart_342726 baseEnd_342726 := by
    simpa [prefixWord, tailWord_342726, baseEnd_342726] using wordTrace_append hprefix tailTrace_342726
  have hstable : (prefixWord ++ tailWord_342726).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342726).length < 2 ^ (prefixWord ++ tailWord_342726).sum := by decide
  have hdescent : baseEnd_342726 < baseStart_342726 := by decide
  rcases family_descends (prefixWord ++ tailWord_342726) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342734 : List Nat := [4, 1, 1, 1, 3, 2, 9]
def baseStart_342734 : Nat := 118140960795 + 342734 * 2 ^ 59
def prefixEnd_342734 : Nat := 4983230072969 + 3 ^ 40 * 342734 * 2
def baseEnd_342734 : Nat := 8690729809292211622163

theorem tailTrace_342734 : CollatzResearch.WordTrace tailWord_342734 prefixEnd_342734 8690729809292211622163 := by
  unfold tailWord_342734
  simp only [CollatzResearch.WordTrace]
  refine ⟨1562566992542590894019407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8333690626893818101436837 1562566992542590894019407)
  ·
    refine ⟨2343850488813886341029111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1562566992542590894019407 2343850488813886341029111)
    ·
      refine ⟨3515775733220829511543667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2343850488813886341029111 3515775733220829511543667)
      ·
        refine ⟨5273663599831244267315501, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3515775733220829511543667 5273663599831244267315501)
        ·
          refine ⟨1977623849936716600243313, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5273663599831244267315501 1977623849936716600243313)
          ·
            refine ⟨1483217887452537450182485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1977623849936716600243313 1483217887452537450182485)
            ·
              refine ⟨8690729809292211622163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1483217887452537450182485 8690729809292211622163)
              ·
                rfl

theorem cell21_342734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 3, 2, 9].length) (baseStart_342734 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342734 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342734 prefixEnd_342734 := by exact prefixLift 342734
  have htrace : WordTrace (prefixWord ++ tailWord_342734) baseStart_342734 baseEnd_342734 := by
    simpa [prefixWord, tailWord_342734, baseEnd_342734] using wordTrace_append hprefix tailTrace_342734
  have hstable : (prefixWord ++ tailWord_342734).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342734).length < 2 ^ (prefixWord ++ tailWord_342734).sum := by decide
  have hdescent : baseEnd_342734 < baseStart_342734 := by decide
  rcases family_descends (prefixWord ++ tailWord_342734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342740 : List Nat := [2, 4, 1, 3, 3, 1, 1, 1, 5]
def baseStart_342740 : Nat := 118140960795 + 342740 * 2 ^ 59
def prefixEnd_342740 : Nat := 4983230072969 + 3 ^ 40 * 342740 * 2
def baseEnd_342740 : Nat := 78217937565375227499455

theorem tailTrace_342740 : CollatzResearch.WordTrace tailWord_342740 prefixEnd_342740 78217937565375227499455 := by
  unfold tailWord_342740
  simp only [CollatzResearch.WordTrace]
  refine ⟨6250377389159495088436837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8333836518879326784582449 6250377389159495088436837)
  ·
    refine ⟨1171945760467405329081907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6250377389159495088436837 1171945760467405329081907)
    ·
      refine ⟨1757918640701107993622861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1171945760467405329081907 1757918640701107993622861)
      ·
        refine ⟨659219490262915497608573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1757918640701107993622861 659219490262915497608573)
        ·
          refine ⟨247207308848593311603215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 659219490262915497608573 247207308848593311603215)
          ·
            refine ⟨370810963272889967404823, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247207308848593311603215 370810963272889967404823)
            ·
              refine ⟨556216444909334951107235, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 370810963272889967404823 556216444909334951107235)
              ·
                refine ⟨834324667364002426660853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556216444909334951107235 834324667364002426660853)
                ·
                  refine ⟨78217937565375227499455, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834324667364002426660853 78217937565375227499455)
                  ·
                    rfl

theorem cell21_342740_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 3, 3, 1, 1, 1, 5].length) (baseStart_342740 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342740 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342740 prefixEnd_342740 := by exact prefixLift 342740
  have htrace : WordTrace (prefixWord ++ tailWord_342740) baseStart_342740 baseEnd_342740 := by
    simpa [prefixWord, tailWord_342740, baseEnd_342740] using wordTrace_append hprefix tailTrace_342740
  have hstable : (prefixWord ++ tailWord_342740).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342740).length < 2 ^ (prefixWord ++ tailWord_342740).sum := by decide
  have hdescent : baseEnd_342740 < baseStart_342740 := by decide
  rcases family_descends (prefixWord ++ tailWord_342740) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342765 : List Nat := [1, 5, 1, 2, 1, 1, 2, 1, 7]
def baseStart_342765 : Nat := 118140960795 + 342765 * 2 ^ 59
def prefixEnd_342765 : Nat := 4983230072969 + 3 ^ 40 * 342765 * 2
def baseEnd_342765 : Nat := 78223642905980739582737

theorem tailTrace_342765 : CollatzResearch.WordTrace tailWord_342765 prefixEnd_342765 78223642905980739582737 := by
  unfold tailWord_342765
  simp only [CollatzResearch.WordTrace]
  refine ⟨12501666603228419446533749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8334444402152279631022499 12501666603228419446533749)
  ·
    refine ⟨1172031244052664323112539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12501666603228419446533749 1172031244052664323112539)
    ·
      refine ⟨1758046866078996484668809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1172031244052664323112539 1758046866078996484668809)
      ·
        refine ⟨1318535149559247363501607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1758046866078996484668809 1318535149559247363501607)
        ·
          refine ⟨1977802724338871045252411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1318535149559247363501607 1977802724338871045252411)
          ·
            refine ⟨2966704086508306567878617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1977802724338871045252411 2966704086508306567878617)
            ·
              refine ⟨2225028064881229925908963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2966704086508306567878617 2225028064881229925908963)
              ·
                refine ⟨3337542097321844888863445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2225028064881229925908963 3337542097321844888863445)
                ·
                  refine ⟨78223642905980739582737, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3337542097321844888863445 78223642905980739582737)
                  ·
                    rfl

theorem cell21_342765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_342765 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342765 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342765 prefixEnd_342765 := by exact prefixLift 342765
  have htrace : WordTrace (prefixWord ++ tailWord_342765) baseStart_342765 baseEnd_342765 := by
    simpa [prefixWord, tailWord_342765, baseEnd_342765] using wordTrace_append hprefix tailTrace_342765
  have hstable : (prefixWord ++ tailWord_342765).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342765).length < 2 ^ (prefixWord ++ tailWord_342765).sum := by decide
  have hdescent : baseEnd_342765 < baseStart_342765 := by decide
  rcases family_descends (prefixWord ++ tailWord_342765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_342917 : List Nat := [1, 3, 1, 1, 3, 3, 3, 1, 5]
def baseStart_342917 : Nat := 118140960795 + 342917 * 2 ^ 59
def prefixEnd_342917 : Nat := 4983230072969 + 3 ^ 40 * 342917 * 2
def baseEnd_342917 : Nat := 78258331376862253049093

theorem tailTrace_342917 : CollatzResearch.WordTrace tailWord_342917 prefixEnd_342917 78258331376862253049093 := by
  unfold tailWord_342917
  simp only [CollatzResearch.WordTrace]
  refine ⟨12507210498677749406067005, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8338140332451832937378003 12507210498677749406067005)
  ·
    refine ⟨4690203937004156027275127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12507210498677749406067005 4690203937004156027275127)
    ·
      refine ⟨7035305905506234040912691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4690203937004156027275127 7035305905506234040912691)
      ·
        refine ⟨10552958858259351061369037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7035305905506234040912691 10552958858259351061369037)
        ·
          refine ⟨3957359571847256648013389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10552958858259351061369037 3957359571847256648013389)
          ·
            refine ⟨1484009839442721243005021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3957359571847256648013389 1484009839442721243005021)
            ·
              refine ⟨556503689791020466126883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1484009839442721243005021 556503689791020466126883)
              ·
                refine ⟨834755534686530699190325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 556503689791020466126883 834755534686530699190325)
                ·
                  refine ⟨78258331376862253049093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 834755534686530699190325 78258331376862253049093)
                  ·
                    rfl

theorem cell21_342917_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 3, 3, 1, 5].length) (baseStart_342917 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_342917 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_342917 prefixEnd_342917 := by exact prefixLift 342917
  have htrace : WordTrace (prefixWord ++ tailWord_342917) baseStart_342917 baseEnd_342917 := by
    simpa [prefixWord, tailWord_342917, baseEnd_342917] using wordTrace_append hprefix tailTrace_342917
  have hstable : (prefixWord ++ tailWord_342917).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_342917).length < 2 ^ (prefixWord ++ tailWord_342917).sum := by decide
  have hdescent : baseEnd_342917 < baseStart_342917 := by decide
  rcases family_descends (prefixWord ++ tailWord_342917) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343041 : List Nat := [1, 2, 4, 1, 2, 3, 3, 1, 4]
def baseStart_343041 : Nat := 118140960795 + 343041 * 2 ^ 59
def prefixEnd_343041 : Nat := 4983230072969 + 3 ^ 40 * 343041 * 2
def baseEnd_343041 : Nat := 78286629866265592982173

theorem tailTrace_343041 : CollatzResearch.WordTrace tailWord_343041 prefixEnd_343041 78286629866265592982173 := by
  unfold tailWord_343041
  simp only [CollatzResearch.WordTrace]
  refine ⟨12511733150228518583580977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8341155433485679055720651 12511733150228518583580977)
  ·
    refine ⟨9383799862671388937685733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12511733150228518583580977 9383799862671388937685733)
    ·
      refine ⟨1759462474250885425816075, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9383799862671388937685733 1759462474250885425816075)
      ·
        refine ⟨2639193711376328138724113, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1759462474250885425816075 2639193711376328138724113)
        ·
          refine ⟨1979395283532246104043085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639193711376328138724113 1979395283532246104043085)
          ·
            refine ⟨742273231324592289016157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1979395283532246104043085 742273231324592289016157)
            ·
              refine ⟨278352461746722108381059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742273231324592289016157 278352461746722108381059)
              ·
                refine ⟨417528692620083162571589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278352461746722108381059 417528692620083162571589)
                ·
                  refine ⟨78286629866265592982173, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417528692620083162571589 78286629866265592982173)
                  ·
                    rfl

theorem cell21_343041_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 3, 3, 1, 4].length) (baseStart_343041 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343041 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343041 prefixEnd_343041 := by exact prefixLift 343041
  have htrace : WordTrace (prefixWord ++ tailWord_343041) baseStart_343041 baseEnd_343041 := by
    simpa [prefixWord, tailWord_343041, baseEnd_343041] using wordTrace_append hprefix tailTrace_343041
  have hstable : (prefixWord ++ tailWord_343041).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343041).length < 2 ^ (prefixWord ++ tailWord_343041).sum := by decide
  have hdescent : baseEnd_343041 < baseStart_343041 := by decide
  rcases family_descends (prefixWord ++ tailWord_343041) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343072 : List Nat := [2, 1, 1, 7, 2, 1, 7]
def baseStart_343072 : Nat := 118140960795 + 343072 * 2 ^ 59
def prefixEnd_343072 : Nat := 4983230072969 + 3 ^ 40 * 343072 * 2
def baseEnd_343072 : Nat := 8699300498735158662827

theorem tailTrace_343072 : CollatzResearch.WordTrace tailWord_343072 prefixEnd_343072 8699300498735158662827 := by
  unfold tailWord_343072
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256431906558105438979735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8341909208744140585306313 6256431906558105438979735)
  ·
    refine ⟨9384647859837158158469603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6256431906558105438979735 9384647859837158158469603)
    ·
      refine ⟨14076971789755737237704405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9384647859837158158469603 14076971789755737237704405)
      ·
        refine ⟨329929026322400091508697, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 14076971789755737237704405 329929026322400091508697)
        ·
          refine ⟨247446769741800068631523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 329929026322400091508697 247446769741800068631523)
          ·
            refine ⟨371170154612700102947285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 247446769741800068631523 371170154612700102947285)
            ·
              refine ⟨8699300498735158662827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 371170154612700102947285 8699300498735158662827)
              ·
                rfl

theorem cell21_343072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 7, 2, 1, 7].length) (baseStart_343072 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343072 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343072 prefixEnd_343072 := by exact prefixLift 343072
  have htrace : WordTrace (prefixWord ++ tailWord_343072) baseStart_343072 baseEnd_343072 := by
    simpa [prefixWord, tailWord_343072, baseEnd_343072] using wordTrace_append hprefix tailTrace_343072
  have hstable : (prefixWord ++ tailWord_343072).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343072).length < 2 ^ (prefixWord ++ tailWord_343072).sum := by decide
  have hdescent : baseEnd_343072 < baseStart_343072 := by decide
  rcases family_descends (prefixWord ++ tailWord_343072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343083 : List Nat := [1, 1, 1, 1, 2, 1, 6, 4, 4]
def baseStart_343083 : Nat := 118140960795 + 343083 * 2 ^ 59
def prefixEnd_343083 : Nat := 4983230072969 + 3 ^ 40 * 343083 * 2
def baseEnd_343083 : Nat := 78296214838482853282087

theorem tailTrace_343083 : CollatzResearch.WordTrace tailWord_343083 prefixEnd_343083 78296214838482853282087 := by
  unfold tailWord_343083
  simp only [CollatzResearch.WordTrace]
  refine ⟨12513265016076359756609903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8342176677384239837739935 12513265016076359756609903)
  ·
    refine ⟨18769897524114539634914855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12513265016076359756609903 18769897524114539634914855)
    ·
      refine ⟨28154846286171809452372283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18769897524114539634914855 28154846286171809452372283)
      ·
        refine ⟨42232269429257714178558425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28154846286171809452372283 42232269429257714178558425)
        ·
          refine ⟨31674202071943285633918819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 42232269429257714178558425 31674202071943285633918819)
          ·
            refine ⟨47511303107914928450878229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 31674202071943285633918819 47511303107914928450878229)
            ·
              refine ⟨2227092333183512271134917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 47511303107914928450878229 2227092333183512271134917)
              ·
                refine ⟨417579812471908550837797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2227092333183512271134917 417579812471908550837797)
                ·
                  refine ⟨78296214838482853282087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417579812471908550837797 78296214838482853282087)
                  ·
                    rfl

theorem cell21_343083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 6, 4, 4].length) (baseStart_343083 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343083 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343083 prefixEnd_343083 := by exact prefixLift 343083
  have htrace : WordTrace (prefixWord ++ tailWord_343083) baseStart_343083 baseEnd_343083 := by
    simpa [prefixWord, tailWord_343083, baseEnd_343083] using wordTrace_append hprefix tailTrace_343083
  have hstable : (prefixWord ++ tailWord_343083).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343083).length < 2 ^ (prefixWord ++ tailWord_343083).sum := by decide
  have hdescent : baseEnd_343083 < baseStart_343083 := by decide
  rcases family_descends (prefixWord ++ tailWord_343083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343100 : List Nat := [2, 2, 2, 2, 2, 3, 1, 3, 4]
def baseStart_343100 : Nat := 118140960795 + 343100 * 2 ^ 59
def prefixEnd_343100 : Nat := 4983230072969 + 3 ^ 40 * 343100 * 2
def baseEnd_343100 : Nat := 78300094470094601498719

theorem tailTrace_343100 : CollatzResearch.WordTrace tailWord_343100 prefixEnd_343100 78300094470094601498719 := by
  unfold tailWord_343100
  simp only [CollatzResearch.WordTrace]
  refine ⟨6256942528507385829989377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8342590038009847773319169 6256942528507385829989377)
  ·
    refine ⟨4692706896380539372492033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6256942528507385829989377 4692706896380539372492033)
    ·
      refine ⟨3519530172285404529369025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4692706896380539372492033 3519530172285404529369025)
      ·
        refine ⟨2639647629214053397026769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3519530172285404529369025 2639647629214053397026769)
        ·
          refine ⟨1979735721910540047770077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2639647629214053397026769 1979735721910540047770077)
          ·
            refine ⟨742400895716452517913779, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1979735721910540047770077 742400895716452517913779)
            ·
              refine ⟨1113601343574678776870669, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 742400895716452517913779 1113601343574678776870669)
              ·
                refine ⟨417600503840504541326501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1113601343574678776870669 417600503840504541326501)
                ·
                  refine ⟨78300094470094601498719, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417600503840504541326501 78300094470094601498719)
                  ·
                    rfl

theorem cell21_343100_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 3, 1, 3, 4].length) (baseStart_343100 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343100 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343100 prefixEnd_343100 := by exact prefixLift 343100
  have htrace : WordTrace (prefixWord ++ tailWord_343100) baseStart_343100 baseEnd_343100 := by
    simpa [prefixWord, tailWord_343100, baseEnd_343100] using wordTrace_append hprefix tailTrace_343100
  have hstable : (prefixWord ++ tailWord_343100).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343100).length < 2 ^ (prefixWord ++ tailWord_343100).sum := by decide
  have hdescent : baseEnd_343100 < baseStart_343100 := by decide
  rcases family_descends (prefixWord ++ tailWord_343100) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343134 : List Nat := [4, 4, 1, 1, 1, 1, 1, 4, 4]
def baseStart_343134 : Nat := 118140960795 + 343134 * 2 ^ 59
def prefixEnd_343134 : Nat := 4983230072969 + 3 ^ 40 * 343134 * 2
def baseEnd_343134 : Nat := 78307853733318097931983

theorem tailTrace_343134 : CollatzResearch.WordTrace tailWord_343134 prefixEnd_343134 78307853733318097931983 := by
  unfold tailWord_343134
  simp only [CollatzResearch.WordTrace]
  refine ⟨1564390642361449433339557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8343416759261063644477637 1564390642361449433339557)
  ·
    refine ⟨293323245442771768751167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1564390642361449433339557 293323245442771768751167)
    ·
      refine ⟨439984868164157653126751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293323245442771768751167 439984868164157653126751)
      ·
        refine ⟨659977302246236479690127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 439984868164157653126751 659977302246236479690127)
        ·
          refine ⟨989965953369354719535191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 659977302246236479690127 989965953369354719535191)
          ·
            refine ⟨1484948930054032079302787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 989965953369354719535191 1484948930054032079302787)
            ·
              refine ⟨2227423395081048118954181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1484948930054032079302787 2227423395081048118954181)
              ·
                refine ⟨417641886577696522303909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2227423395081048118954181 417641886577696522303909)
                ·
                  refine ⟨78307853733318097931983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417641886577696522303909 78307853733318097931983)
                  ·
                    rfl

theorem cell21_343134_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 1, 1, 1, 1, 4, 4].length) (baseStart_343134 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343134 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343134 prefixEnd_343134 := by exact prefixLift 343134
  have htrace : WordTrace (prefixWord ++ tailWord_343134) baseStart_343134 baseEnd_343134 := by
    simpa [prefixWord, tailWord_343134, baseEnd_343134] using wordTrace_append hprefix tailTrace_343134
  have hstable : (prefixWord ++ tailWord_343134).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343134).length < 2 ^ (prefixWord ++ tailWord_343134).sum := by decide
  have hdescent : baseEnd_343134 < baseStart_343134 := by decide
  rcases family_descends (prefixWord ++ tailWord_343134) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343159 : List Nat := [1, 1, 3, 1, 1, 4, 1, 5, 4]
def baseStart_343159 : Nat := 118140960795 + 343159 * 2 ^ 59
def prefixEnd_343159 : Nat := 4983230072969 + 3 ^ 40 * 343159 * 2
def baseEnd_343159 : Nat := 78313559073923610015265

theorem tailTrace_343159 : CollatzResearch.WordTrace tailWord_343159 prefixEnd_343159 78313559073923610015265 := by
  unfold tailWord_343159
  simp only [CollatzResearch.WordTrace]
  refine ⟨12516036963801024736376531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8344024642534016490917687 12516036963801024736376531)
  ·
    refine ⟨18774055445701537104564797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12516036963801024736376531 18774055445701537104564797)
    ·
      refine ⟨7040270792138076414211799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18774055445701537104564797 7040270792138076414211799)
      ·
        refine ⟨10560406188207114621317699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7040270792138076414211799 10560406188207114621317699)
        ·
          refine ⟨15840609282310671931976549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10560406188207114621317699 15840609282310671931976549)
          ·
            refine ⟨2970114240433250987245603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 15840609282310671931976549 2970114240433250987245603)
            ·
              refine ⟨4455171360649876480868405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 2970114240433250987245603 4455171360649876480868405)
              ·
                refine ⟨417672315060925920081413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4455171360649876480868405 417672315060925920081413)
                ·
                  refine ⟨78313559073923610015265, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417672315060925920081413 78313559073923610015265)
                  ·
                    rfl

theorem cell21_343159_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 4, 1, 5, 4].length) (baseStart_343159 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343159 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343159 prefixEnd_343159 := by exact prefixLift 343159
  have htrace : WordTrace (prefixWord ++ tailWord_343159) baseStart_343159 baseEnd_343159 := by
    simpa [prefixWord, tailWord_343159, baseEnd_343159] using wordTrace_append hprefix tailTrace_343159
  have hstable : (prefixWord ++ tailWord_343159).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343159).length < 2 ^ (prefixWord ++ tailWord_343159).sum := by decide
  have hdescent : baseEnd_343159 < baseStart_343159 := by decide
  rcases family_descends (prefixWord ++ tailWord_343159) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343210 : List Nat := [3, 1, 5, 1, 1, 2, 3, 1, 4]
def baseStart_343210 : Nat := 118140960795 + 343210 * 2 ^ 59
def prefixEnd_343210 : Nat := 4983230072969 + 3 ^ 40 * 343210 * 2
def baseEnd_343210 : Nat := 78325197968758854665161

theorem tailTrace_343210 : CollatzResearch.WordTrace tailWord_343210 prefixEnd_343210 78325197968758854665161 := by
  unfold tailWord_343210
  simp only [CollatzResearch.WordTrace]
  refine ⟨3129474271654065111620771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8345264724410840297655389 3129474271654065111620771)
  ·
    refine ⟨4694211407481097667431157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3129474271654065111620771 4694211407481097667431157)
    ·
      refine ⟨440082319451352906321671, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4694211407481097667431157 440082319451352906321671)
      ·
        refine ⟨660123479177029359482507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 440082319451352906321671 660123479177029359482507)
        ·
          refine ⟨990185218765544039223761, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 660123479177029359482507 990185218765544039223761)
          ·
            refine ⟨742638914074158029417821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 990185218765544039223761 742638914074158029417821)
            ·
              refine ⟨278489592777809261031683, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 742638914074158029417821 278489592777809261031683)
              ·
                refine ⟨417734389166713891547525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278489592777809261031683 417734389166713891547525)
                ·
                  refine ⟨78325197968758854665161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 417734389166713891547525 78325197968758854665161)
                  ·
                    rfl

theorem cell21_343210_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 1, 1, 2, 3, 1, 4].length) (baseStart_343210 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343210 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343210 prefixEnd_343210 := by exact prefixLift 343210
  have htrace : WordTrace (prefixWord ++ tailWord_343210) baseStart_343210 baseEnd_343210 := by
    simpa [prefixWord, tailWord_343210, baseEnd_343210] using wordTrace_append hprefix tailTrace_343210
  have hstable : (prefixWord ++ tailWord_343210).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343210).length < 2 ^ (prefixWord ++ tailWord_343210).sum := by decide
  have hdescent : baseEnd_343210 < baseStart_343210 := by decide
  rcases family_descends (prefixWord ++ tailWord_343210) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343438 : List Nat := [4, 1, 1, 4, 2, 2, 2, 1, 4]
def baseStart_343438 : Nat := 118140960795 + 343438 * 2 ^ 59
def prefixEnd_343438 : Nat := 4983230072969 + 3 ^ 40 * 343438 * 2
def baseEnd_343438 : Nat := 78377230675081124864695

theorem tailTrace_343438 : CollatzResearch.WordTrace tailWord_343438 prefixEnd_343438 78377230675081124864695 := by
  unfold tailWord_343438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1565776616223781923222871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8350808619860170257188645 1565776616223781923222871)
  ·
    refine ⟨2348664924335672884834307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1565776616223781923222871 2348664924335672884834307)
    ·
      refine ⟨3522997386503509327251461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2348664924335672884834307 3522997386503509327251461)
      ·
        refine ⟨660562009969407998859649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3522997386503509327251461 660562009969407998859649)
        ·
          refine ⟨495421507477055999144737, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 660562009969407998859649 495421507477055999144737)
          ·
            refine ⟨371566130607791999358553, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 495421507477055999144737 371566130607791999358553)
            ·
              refine ⟨278674597955843999518915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 371566130607791999358553 278674597955843999518915)
              ·
                refine ⟨418011896933765999278373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278674597955843999518915 418011896933765999278373)
                ·
                  refine ⟨78377230675081124864695, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418011896933765999278373 78377230675081124864695)
                  ·
                    rfl

theorem cell21_343438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 2, 2, 2, 1, 4].length) (baseStart_343438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343438 prefixEnd_343438 := by exact prefixLift 343438
  have htrace : WordTrace (prefixWord ++ tailWord_343438) baseStart_343438 baseEnd_343438 := by
    simpa [prefixWord, tailWord_343438, baseEnd_343438] using wordTrace_append hprefix tailTrace_343438
  have hstable : (prefixWord ++ tailWord_343438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343438).length < 2 ^ (prefixWord ++ tailWord_343438).sum := by decide
  have hdescent : baseEnd_343438 < baseStart_343438 := by decide
  rcases family_descends (prefixWord ++ tailWord_343438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343477 : List Nat := [1, 3, 3, 2, 2, 10]
def baseStart_343477 : Nat := 118140960795 + 343477 * 2 ^ 59
def prefixEnd_343477 : Nat := 4983230072969 + 3 ^ 40 * 343477 * 2
def baseEnd_343477 : Nat := 2903190037275026804245

theorem tailTrace_343477 : CollatzResearch.WordTrace tailWord_343477 prefixEnd_343477 2903190037275026804245 := by
  unfold tailWord_343477
  simp only [CollatzResearch.WordTrace]
  refine ⟨12527635376648965046452685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8351756917765976697635123 12527635376648965046452685)
  ·
    refine ⟨4697863266243361892419757, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12527635376648965046452685 4697863266243361892419757)
    ·
      refine ⟨1761698724841260709657409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4697863266243361892419757 1761698724841260709657409)
      ·
        refine ⟨1321274043630945532243057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1761698724841260709657409 1321274043630945532243057)
        ·
          refine ⟨990955532723209149182293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1321274043630945532243057 990955532723209149182293)
          ·
            refine ⟨2903190037275026804245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 10 990955532723209149182293 2903190037275026804245)
            ·
              rfl

theorem cell21_343477_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 2, 10].length) (baseStart_343477 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343477 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343477 prefixEnd_343477 := by exact prefixLift 343477
  have htrace : WordTrace (prefixWord ++ tailWord_343477) baseStart_343477 baseEnd_343477 := by
    simpa [prefixWord, tailWord_343477, baseEnd_343477] using wordTrace_append hprefix tailTrace_343477
  have hstable : (prefixWord ++ tailWord_343477).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343477).length < 2 ^ (prefixWord ++ tailWord_343477).sum := by decide
  have hdescent : baseEnd_343477 < baseStart_343477 := by decide
  rcases family_descends (prefixWord ++ tailWord_343477) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343542 : List Nat := [5, 1, 1, 1, 2, 2, 2, 4, 3]
def baseStart_343542 : Nat := 118140960795 + 343542 * 2 ^ 59
def prefixEnd_343542 : Nat := 4983230072969 + 3 ^ 40 * 343542 * 2
def baseEnd_343542 : Nat := 78400964892000055131149

theorem tailTrace_343542 : CollatzResearch.WordTrace tailWord_343542 prefixEnd_343542 78400964892000055131149 := by
  unfold tailWord_343542
  simp only [CollatzResearch.WordTrace]
  refine ⟨783125382588342571723055, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8353337414275654098379253 783125382588342571723055)
  ·
    refine ⟨1174688073882513857584583, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 783125382588342571723055 1174688073882513857584583)
    ·
      refine ⟨1762032110823770786376875, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1174688073882513857584583 1762032110823770786376875)
      ·
        refine ⟨2643048166235656179565313, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1762032110823770786376875 2643048166235656179565313)
        ·
          refine ⟨1982286124676742134673985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2643048166235656179565313 1982286124676742134673985)
          ·
            refine ⟨1486714593507556601005489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1982286124676742134673985 1486714593507556601005489)
            ·
              refine ⟨1115035945130667450754117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1486714593507556601005489 1115035945130667450754117)
              ·
                refine ⟨209069239712000147016397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1115035945130667450754117 209069239712000147016397)
                ·
                  refine ⟨78400964892000055131149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209069239712000147016397 78400964892000055131149)
                  ·
                    rfl

theorem cell21_343542_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 2, 2, 2, 4, 3].length) (baseStart_343542 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343542 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343542 prefixEnd_343542 := by exact prefixLift 343542
  have htrace : WordTrace (prefixWord ++ tailWord_343542) baseStart_343542 baseEnd_343542 := by
    simpa [prefixWord, tailWord_343542, baseEnd_343542] using wordTrace_append hprefix tailTrace_343542
  have hstable : (prefixWord ++ tailWord_343542).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343542).length < 2 ^ (prefixWord ++ tailWord_343542).sum := by decide
  have hdescent : baseEnd_343542 < baseStart_343542 := by decide
  rcases family_descends (prefixWord ++ tailWord_343542) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343615 : List Nat := [1, 1, 2, 2, 3, 4, 1, 3, 4]
def baseStart_343615 : Nat := 118140960795 + 343615 * 2 ^ 59
def prefixEnd_343615 : Nat := 4983230072969 + 3 ^ 40 * 343615 * 2
def baseEnd_343615 : Nat := 78417624486568150414333

theorem tailTrace_343615 : CollatzResearch.WordTrace tailWord_343615 prefixEnd_343615 78417624486568150414333 := by
  unfold tailWord_343615
  simp only [CollatzResearch.WordTrace]
  refine ⟨12532668650149014614976299, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8355112433432676409984199 12532668650149014614976299)
  ·
    refine ⟨18799002975223521922464449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12532668650149014614976299 18799002975223521922464449)
    ·
      refine ⟨14099252231417641441848337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18799002975223521922464449 14099252231417641441848337)
      ·
        refine ⟨10574439173563231081386253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14099252231417641441848337 10574439173563231081386253)
        ·
          refine ⟨3965414690086211655519845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10574439173563231081386253 3965414690086211655519845)
          ·
            refine ⟨743515254391164685409971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3965414690086211655519845 743515254391164685409971)
            ·
              refine ⟨1115272881586747028114957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743515254391164685409971 1115272881586747028114957)
              ·
                refine ⟨418227330595030135543109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1115272881586747028114957 418227330595030135543109)
                ·
                  refine ⟨78417624486568150414333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418227330595030135543109 78417624486568150414333)
                  ·
                    rfl

theorem cell21_343615_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 4, 1, 3, 4].length) (baseStart_343615 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343615 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343615 prefixEnd_343615 := by exact prefixLift 343615
  have htrace : WordTrace (prefixWord ++ tailWord_343615) baseStart_343615 baseEnd_343615 := by
    simpa [prefixWord, tailWord_343615, baseEnd_343615] using wordTrace_append hprefix tailTrace_343615
  have hstable : (prefixWord ++ tailWord_343615).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343615).length < 2 ^ (prefixWord ++ tailWord_343615).sum := by decide
  have hdescent : baseEnd_343615 < baseStart_343615 := by decide
  rcases family_descends (prefixWord ++ tailWord_343615) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343646 : List Nat := [4, 4, 1, 12]
def baseStart_343646 : Nat := 118140960795 + 343646 * 2 ^ 59
def prefixEnd_343646 : Nat := 4983230072969 + 3 ^ 40 * 343646 * 2
def baseEnd_343646 : Nat := 322735387279501997521

theorem tailTrace_343646 : CollatzResearch.WordTrace tailWord_343646 prefixEnd_343646 322735387279501997521 := by
  unfold tailWord_343646
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566724914129588363669349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8355866208691137939569861 1566724914129588363669349)
  ·
    refine ⟨293760921399297818188003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 1566724914129588363669349 293760921399297818188003)
    ·
      refine ⟨440641382098946727282005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 293760921399297818188003 440641382098946727282005)
      ·
        refine ⟨322735387279501997521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 12 440641382098946727282005 322735387279501997521)
        ·
          rfl

theorem cell21_343646_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 4, 1, 12].length) (baseStart_343646 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343646 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343646 prefixEnd_343646 := by exact prefixLift 343646
  have htrace : WordTrace (prefixWord ++ tailWord_343646) baseStart_343646 baseEnd_343646 := by
    simpa [prefixWord, tailWord_343646, baseEnd_343646] using wordTrace_append hprefix tailTrace_343646
  have hstable : (prefixWord ++ tailWord_343646).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343646).length < 2 ^ (prefixWord ++ tailWord_343646).sum := by decide
  have hdescent : baseEnd_343646 < baseStart_343646 := by decide
  rcases family_descends (prefixWord ++ tailWord_343646) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343694 : List Nat := [4, 1, 1, 3, 1, 3, 2, 3, 3]
def baseStart_343694 : Nat := 118140960795 + 343694 * 2 ^ 59
def prefixEnd_343694 : Nat := 4983230072969 + 3 ^ 40 * 343694 * 2
def baseEnd_343694 : Nat := 78435653362881568597505

theorem tailTrace_343694 : CollatzResearch.WordTrace tailWord_343694 prefixEnd_343694 78435653362881568597505 := by
  unfold tailWord_343694
  simp only [CollatzResearch.WordTrace]
  refine ⟨1566943752107851388387767, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8357033344575207404734757 1566943752107851388387767)
  ·
    refine ⟨2350415628161777082581651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1566943752107851388387767 2350415628161777082581651)
    ·
      refine ⟨3525623442242665623872477, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2350415628161777082581651 3525623442242665623872477)
      ·
        refine ⟨1322108790840999608952179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3525623442242665623872477 1322108790840999608952179)
        ·
          refine ⟨1983163186261499413428269, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322108790840999608952179 1983163186261499413428269)
          ·
            refine ⟨743686194848062280035601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1983163186261499413428269 743686194848062280035601)
            ·
              refine ⟨557764646136046710026701, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 743686194848062280035601 557764646136046710026701)
              ·
                refine ⟨209161742301017516260013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 557764646136046710026701 209161742301017516260013)
                ·
                  refine ⟨78435653362881568597505, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209161742301017516260013 78435653362881568597505)
                  ·
                    rfl

theorem cell21_343694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 1, 3, 2, 3, 3].length) (baseStart_343694 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343694 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343694 prefixEnd_343694 := by exact prefixLift 343694
  have htrace : WordTrace (prefixWord ++ tailWord_343694) baseStart_343694 baseEnd_343694 := by
    simpa [prefixWord, tailWord_343694, baseEnd_343694] using wordTrace_append hprefix tailTrace_343694
  have hstable : (prefixWord ++ tailWord_343694).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343694).length < 2 ^ (prefixWord ++ tailWord_343694).sum := by decide
  have hdescent : baseEnd_343694 < baseStart_343694 := by decide
  rcases family_descends (prefixWord ++ tailWord_343694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343770 : List Nat := [3, 1, 1, 2, 2, 4, 3, 2, 3]
def baseStart_343770 : Nat := 118140960795 + 343770 * 2 ^ 59
def prefixEnd_343770 : Nat := 4983230072969 + 3 ^ 40 * 343770 * 2
def baseEnd_343770 : Nat := 78452997598322325330683

theorem tailTrace_343770 : CollatzResearch.WordTrace tailWord_343770 prefixEnd_343770 78452997598322325330683 := by
  unfold tailWord_343770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3134580491146869021717191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8358881309724984057912509 3134580491146869021717191)
  ·
    refine ⟨4701870736720303532575787, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3134580491146869021717191 4701870736720303532575787)
    ·
      refine ⟨7052806105080455298863681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4701870736720303532575787 7052806105080455298863681)
      ·
        refine ⟨5289604578810341474147761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7052806105080455298863681 5289604578810341474147761)
        ·
          refine ⟨3967203434107756105610821, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5289604578810341474147761 3967203434107756105610821)
          ·
            refine ⟨743850643895204269802029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3967203434107756105610821 743850643895204269802029)
            ·
              refine ⟨278943991460701601175761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 743850643895204269802029 278943991460701601175761)
              ·
                refine ⟨209207993595526200881821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 278943991460701601175761 209207993595526200881821)
                ·
                  refine ⟨78452997598322325330683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209207993595526200881821 78452997598322325330683)
                  ·
                    rfl

theorem cell21_343770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 4, 3, 2, 3].length) (baseStart_343770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343770 prefixEnd_343770 := by exact prefixLift 343770
  have htrace : WordTrace (prefixWord ++ tailWord_343770) baseStart_343770 baseEnd_343770 := by
    simpa [prefixWord, tailWord_343770, baseEnd_343770] using wordTrace_append hprefix tailTrace_343770
  have hstable : (prefixWord ++ tailWord_343770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343770).length < 2 ^ (prefixWord ++ tailWord_343770).sum := by decide
  have hdescent : baseEnd_343770 < baseStart_343770 := by decide
  rcases family_descends (prefixWord ++ tailWord_343770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343781 : List Nat := [1, 3, 1, 4, 1, 1, 4, 6]
def baseStart_343781 : Nat := 118140960795 + 343781 * 2 ^ 59
def prefixEnd_343781 : Nat := 4983230072969 + 3 ^ 40 * 343781 * 2
def baseEnd_343781 : Nat := 26151835982729583549109

theorem tailTrace_343781 : CollatzResearch.WordTrace tailWord_343781 prefixEnd_343781 26151835982729583549109 := by
  unfold tailWord_343781
  simp only [CollatzResearch.WordTrace]
  refine ⟨12538723167547624965519197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8359148778365083310346131 12538723167547624965519197)
  ·
    refine ⟨4702021187830359362069699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12538723167547624965519197 4702021187830359362069699)
    ·
      refine ⟨7053031781745539043104549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4702021187830359362069699 7053031781745539043104549)
      ·
        refine ⟨1322443459077288570582103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7053031781745539043104549 1322443459077288570582103)
        ·
          refine ⟨1983665188615932855873155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1322443459077288570582103 1983665188615932855873155)
          ·
            refine ⟨2975497782923899283809733, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1983665188615932855873155 2975497782923899283809733)
            ·
              refine ⟨557905834298231115714325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2975497782923899283809733 557905834298231115714325)
              ·
                refine ⟨26151835982729583549109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 557905834298231115714325 26151835982729583549109)
                ·
                  rfl

theorem cell21_343781_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 6].length) (baseStart_343781 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343781 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343781 prefixEnd_343781 := by exact prefixLift 343781
  have htrace : WordTrace (prefixWord ++ tailWord_343781) baseStart_343781 baseEnd_343781 := by
    simpa [prefixWord, tailWord_343781, baseEnd_343781] using wordTrace_append hprefix tailTrace_343781
  have hstable : (prefixWord ++ tailWord_343781).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343781).length < 2 ^ (prefixWord ++ tailWord_343781).sum := by decide
  have hdescent : baseEnd_343781 < baseStart_343781 := by decide
  rcases family_descends (prefixWord ++ tailWord_343781) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343784 : List Nat := [2, 1, 4, 1, 3, 1, 4, 1, 4]
def baseStart_343784 : Nat := 118140960795 + 343784 * 2 ^ 59
def prefixEnd_343784 : Nat := 4983230072969 + 3 ^ 40 * 343784 * 2
def baseEnd_343784 : Nat := 78456192589061412097321

theorem tailTrace_343784 : CollatzResearch.WordTrace tailWord_343784 prefixEnd_343784 78456192589061412097321 := by
  unfold tailWord_343784
  simp only [CollatzResearch.WordTrace]
  refine ⟨6269416293268378238939203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8359221724357837651918937 6269416293268378238939203)
  ·
    refine ⟨9404124439902567358408805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6269416293268378238939203 9404124439902567358408805)
    ·
      refine ⟨1763273332481731379701651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9404124439902567358408805 1763273332481731379701651)
      ·
        refine ⟨2644909998722597069552477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1763273332481731379701651 2644909998722597069552477)
        ·
          refine ⟨991841249520973901082179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2644909998722597069552477 991841249520973901082179)
          ·
            refine ⟨1487761874281460851623269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 991841249520973901082179 1487761874281460851623269)
            ·
              refine ⟨278955351427773909679363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1487761874281460851623269 278955351427773909679363)
              ·
                refine ⟨418433027141660864519045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 278955351427773909679363 418433027141660864519045)
                ·
                  refine ⟨78456192589061412097321, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418433027141660864519045 78456192589061412097321)
                  ·
                    rfl

theorem cell21_343784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 3, 1, 4, 1, 4].length) (baseStart_343784 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343784 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343784 prefixEnd_343784 := by exact prefixLift 343784
  have htrace : WordTrace (prefixWord ++ tailWord_343784) baseStart_343784 baseEnd_343784 := by
    simpa [prefixWord, tailWord_343784, baseEnd_343784] using wordTrace_append hprefix tailTrace_343784
  have hstable : (prefixWord ++ tailWord_343784).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343784).length < 2 ^ (prefixWord ++ tailWord_343784).sum := by decide
  have hdescent : baseEnd_343784 < baseStart_343784 := by decide
  rcases family_descends (prefixWord ++ tailWord_343784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343795 : List Nat := [1, 1, 1, 2, 2, 3, 2, 4, 5]
def baseStart_343795 : Nat := 118140960795 + 343795 * 2 ^ 59
def prefixEnd_343795 : Nat := 4983230072969 + 3 ^ 40 * 343795 * 2
def baseEnd_343795 : Nat := 78458702938927837413965

theorem tailTrace_343795 : CollatzResearch.WordTrace tailWord_343795 prefixEnd_343795 78458702938927837413965 := by
  unfold tailWord_343795
  simp only [CollatzResearch.WordTrace]
  refine ⟨12539233789496905356528839, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8359489192997936904352559 12539233789496905356528839)
  ·
    refine ⟨18808850684245358034793259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12539233789496905356528839 18808850684245358034793259)
    ·
      refine ⟨28213276026368037052189889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18808850684245358034793259 28213276026368037052189889)
      ·
        refine ⟨21159957019776027789142417, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28213276026368037052189889 21159957019776027789142417)
        ·
          refine ⟨15869967764832020841856813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21159957019776027789142417 15869967764832020841856813)
          ·
            refine ⟨5951237911812007815696305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 15869967764832020841856813 5951237911812007815696305)
            ·
              refine ⟨4463428433859005861772229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5951237911812007815696305 4463428433859005861772229)
              ·
                refine ⟨836892831348563599082293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4463428433859005861772229 836892831348563599082293)
                ·
                  refine ⟨78458702938927837413965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 836892831348563599082293 78458702938927837413965)
                  ·
                    rfl

theorem cell21_343795_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 3, 2, 4, 5].length) (baseStart_343795 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343795 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343795 prefixEnd_343795 := by exact prefixLift 343795
  have htrace : WordTrace (prefixWord ++ tailWord_343795) baseStart_343795 baseEnd_343795 := by
    simpa [prefixWord, tailWord_343795, baseEnd_343795] using wordTrace_append hprefix tailTrace_343795
  have hstable : (prefixWord ++ tailWord_343795).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343795).length < 2 ^ (prefixWord ++ tailWord_343795).sum := by decide
  have hdescent : baseEnd_343795 < baseStart_343795 := by decide
  rcases family_descends (prefixWord ++ tailWord_343795) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343821 : List Nat := [1, 7, 2, 1, 1, 1, 1, 4, 3]
def baseStart_343821 : Nat := 118140960795 + 343821 * 2 ^ 59
def prefixEnd_343821 : Nat := 4983230072969 + 3 ^ 40 * 343821 * 2
def baseEnd_343821 : Nat := 78464636493157569980579

theorem tailTrace_343821 : CollatzResearch.WordTrace tailWord_343821 prefixEnd_343821 78464636493157569980579 := by
  unfold tailWord_343821
  simp only [CollatzResearch.WordTrace]
  refine ⟨12540182087402711796975317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8360121391601807864650211 12540182087402711796975317)
  ·
    refine ⟨293910517673501057741609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12540182087402711796975317 293910517673501057741609)
    ·
      refine ⟨220432888255125793306207, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 293910517673501057741609 220432888255125793306207)
      ·
        refine ⟨330649332382688689959311, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 220432888255125793306207 330649332382688689959311)
        ·
          refine ⟨495973998574033034938967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330649332382688689959311 495973998574033034938967)
          ·
            refine ⟨743960997861049552408451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 495973998574033034938967 743960997861049552408451)
            ·
              refine ⟨1115941496791574328612677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743960997861049552408451 1115941496791574328612677)
              ·
                refine ⟨209239030648420186614877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1115941496791574328612677 209239030648420186614877)
                ·
                  refine ⟨78464636493157569980579, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209239030648420186614877 78464636493157569980579)
                  ·
                    rfl

theorem cell21_343821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 1, 1, 1, 1, 4, 3].length) (baseStart_343821 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343821 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343821 prefixEnd_343821 := by exact prefixLift 343821
  have htrace : WordTrace (prefixWord ++ tailWord_343821) baseStart_343821 baseEnd_343821 := by
    simpa [prefixWord, tailWord_343821, baseEnd_343821] using wordTrace_append hprefix tailTrace_343821
  have hstable : (prefixWord ++ tailWord_343821).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343821).length < 2 ^ (prefixWord ++ tailWord_343821).sum := by decide
  have hdescent : baseEnd_343821 < baseStart_343821 := by decide
  rcases family_descends (prefixWord ++ tailWord_343821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343829 : List Nat := [1, 3, 2, 1, 2, 4, 1, 4, 3]
def baseStart_343829 : Nat := 118140960795 + 343829 * 2 ^ 59
def prefixEnd_343829 : Nat := 4983230072969 + 3 ^ 40 * 343829 * 2
def baseEnd_343829 : Nat := 78466462202151333847229

theorem tailTrace_343829 : CollatzResearch.WordTrace tailWord_343829 prefixEnd_343829 78466462202151333847229 := by
  unfold tailWord_343829
  simp only [CollatzResearch.WordTrace]
  refine ⟨12540473871373729163266541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8360315914249152775511027 12540473871373729163266541)
  ·
    refine ⟨4702677701765148436224953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12540473871373729163266541 4702677701765148436224953)
    ·
      refine ⟨3527008276323861327168715, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4702677701765148436224953 3527008276323861327168715)
      ·
        refine ⟨5290512414485791990753073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3527008276323861327168715 5290512414485791990753073)
        ·
          refine ⟨3967884310864343993064805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5290512414485791990753073 3967884310864343993064805)
          ·
            refine ⟨743978308287064498699651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3967884310864343993064805 743978308287064498699651)
            ·
              refine ⟨1115967462430596748049477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 743978308287064498699651 1115967462430596748049477)
              ·
                refine ⟨209243899205736890259277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1115967462430596748049477 209243899205736890259277)
                ·
                  refine ⟨78466462202151333847229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209243899205736890259277 78466462202151333847229)
                  ·
                    rfl

theorem cell21_343829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 4, 1, 4, 3].length) (baseStart_343829 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343829 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343829 prefixEnd_343829 := by exact prefixLift 343829
  have htrace : WordTrace (prefixWord ++ tailWord_343829) baseStart_343829 baseEnd_343829 := by
    simpa [prefixWord, tailWord_343829, baseEnd_343829] using wordTrace_append hprefix tailTrace_343829
  have hstable : (prefixWord ++ tailWord_343829).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343829).length < 2 ^ (prefixWord ++ tailWord_343829).sum := by decide
  have hdescent : baseEnd_343829 < baseStart_343829 := by decide
  rcases family_descends (prefixWord ++ tailWord_343829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_343998 : List Nat := [4, 2, 1, 1, 1, 3, 4, 2, 3]
def baseStart_343998 : Nat := 118140960795 + 343998 * 2 ^ 59
def prefixEnd_343998 : Nat := 4983230072969 + 3 ^ 40 * 343998 * 2
def baseEnd_343998 : Nat := 78505030304644595530217

theorem tailTrace_343998 : CollatzResearch.WordTrace tailWord_343998 prefixEnd_343998 78505030304644595530217 := by
  unfold tailWord_343998
  simp only [CollatzResearch.WordTrace]
  refine ⟨1568329725970183878271081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8364425205174314017445765 1568329725970183878271081)
  ·
    refine ⟨1176247294477637908703311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1568329725970183878271081 1176247294477637908703311)
    ·
      refine ⟨1764370941716456863054967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1176247294477637908703311 1764370941716456863054967)
      ·
        refine ⟨2646556412574685294582451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1764370941716456863054967 2646556412574685294582451)
        ·
          refine ⟨3969834618862027941873677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2646556412574685294582451 3969834618862027941873677)
          ·
            refine ⟨1488687982073260478202629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3969834618862027941873677 1488687982073260478202629)
            ·
              refine ⟨279128996638736339662993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1488687982073260478202629 279128996638736339662993)
              ·
                refine ⟨209346747479052254747245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 279128996638736339662993 209346747479052254747245)
                ·
                  refine ⟨78505030304644595530217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209346747479052254747245 78505030304644595530217)
                  ·
                    rfl

theorem cell21_343998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 3, 4, 2, 3].length) (baseStart_343998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_343998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_343998 prefixEnd_343998 := by exact prefixLift 343998
  have htrace : WordTrace (prefixWord ++ tailWord_343998) baseStart_343998 baseEnd_343998 := by
    simpa [prefixWord, tailWord_343998, baseEnd_343998] using wordTrace_append hprefix tailTrace_343998
  have hstable : (prefixWord ++ tailWord_343998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_343998).length < 2 ^ (prefixWord ++ tailWord_343998).sum := by decide
  have hdescent : baseEnd_343998 < baseStart_343998 := by decide
  rcases family_descends (prefixWord ++ tailWord_343998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344023 : List Nat := [1, 1, 3, 2, 1, 1, 5, 2, 5]
def baseStart_344023 : Nat := 118140960795 + 344023 * 2 ^ 59
def prefixEnd_344023 : Nat := 4983230072969 + 3 ^ 40 * 344023 * 2
def baseEnd_344023 : Nat := 78510735645250107613499

theorem tailTrace_344023 : CollatzResearch.WordTrace tailWord_344023 prefixEnd_344023 78510735645250107613499 := by
  unfold tailWord_344023
  simp only [CollatzResearch.WordTrace]
  refine ⟨12547549632670900295828723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8365033088447266863885815 12547549632670900295828723)
  ·
    refine ⟨18821324449006350443743085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12547549632670900295828723 18821324449006350443743085)
    ·
      refine ⟨7057996668377381416403657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18821324449006350443743085 7057996668377381416403657)
      ·
        refine ⟨5293497501283036062302743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7057996668377381416403657 5293497501283036062302743)
        ·
          refine ⟨7940246251924554093454115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5293497501283036062302743 7940246251924554093454115)
          ·
            refine ⟨11910369377886831140181173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7940246251924554093454115 11910369377886831140181173)
            ·
              refine ⟨1116597129176890419391985, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 11910369377886831140181173 1116597129176890419391985)
              ·
                refine ⟨837447846882667814543989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1116597129176890419391985 837447846882667814543989)
                ·
                  refine ⟨78510735645250107613499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 837447846882667814543989 78510735645250107613499)
                  ·
                    rfl

theorem cell21_344023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 1, 1, 5, 2, 5].length) (baseStart_344023 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344023 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344023 prefixEnd_344023 := by exact prefixLift 344023
  have htrace : WordTrace (prefixWord ++ tailWord_344023) baseStart_344023 baseEnd_344023 := by
    simpa [prefixWord, tailWord_344023, baseEnd_344023] using wordTrace_append hprefix tailTrace_344023
  have hstable : (prefixWord ++ tailWord_344023).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344023).length < 2 ^ (prefixWord ++ tailWord_344023).sum := by decide
  have hdescent : baseEnd_344023 < baseStart_344023 := by decide
  rcases family_descends (prefixWord ++ tailWord_344023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344026 : List Nat := [3, 1, 1, 2, 5, 1, 3, 5]
def baseStart_344026 : Nat := 118140960795 + 344026 * 2 ^ 59
def prefixEnd_344026 : Nat := 4983230072969 + 3 ^ 40 * 344026 * 2
def baseEnd_344026 : Nat := 26170473428707589687831

theorem tailTrace_344026 : CollatzResearch.WordTrace tailWord_344026 prefixEnd_344026 26170473428707589687831 := by
  unfold tailWord_344026
  simp only [CollatzResearch.WordTrace]
  refine ⟨3136914762915007952046983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8365106034440021205458621 3136914762915007952046983)
  ·
    refine ⟨4705372144372511928070475, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3136914762915007952046983 4705372144372511928070475)
    ·
      refine ⟨7058058216558767892105713, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4705372144372511928070475 7058058216558767892105713)
      ·
        refine ⟨5293543662419075919079285, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7058058216558767892105713 5293543662419075919079285)
        ·
          refine ⟨496269718351788367413683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5293543662419075919079285 496269718351788367413683)
          ·
            refine ⟨744404577527682551120525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496269718351788367413683 744404577527682551120525)
            ·
              refine ⟨279151716572880956670197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 744404577527682551120525 279151716572880956670197)
              ·
                refine ⟨26170473428707589687831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279151716572880956670197 26170473428707589687831)
                ·
                  rfl

theorem cell21_344026_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 5, 1, 3, 5].length) (baseStart_344026 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344026 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344026 prefixEnd_344026 := by exact prefixLift 344026
  have htrace : WordTrace (prefixWord ++ tailWord_344026) baseStart_344026 baseEnd_344026 := by
    simpa [prefixWord, tailWord_344026, baseEnd_344026] using wordTrace_append hprefix tailTrace_344026
  have hstable : (prefixWord ++ tailWord_344026).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344026).length < 2 ^ (prefixWord ++ tailWord_344026).sum := by decide
  have hdescent : baseEnd_344026 < baseStart_344026 := by decide
  rcases family_descends (prefixWord ++ tailWord_344026) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344077 : List Nat := [1, 7, 1, 2, 1, 2, 2, 5]
def baseStart_344077 : Nat := 118140960795 + 344077 * 2 ^ 59
def prefixEnd_344077 : Nat := 4983230072969 + 3 ^ 40 * 344077 * 2
def baseEnd_344077 : Nat := 26174353060319337904463

theorem tailTrace_344077 : CollatzResearch.WordTrace tailWord_344077 prefixEnd_344077 26174353060319337904463 := by
  unfold tailWord_344077
  simp only [CollatzResearch.WordTrace]
  refine ⟨12549519174475267518294485, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8366346116316845012196323 12549519174475267518294485)
  ·
    refine ⟨294129355651764082460027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12549519174475267518294485 294129355651764082460027)
    ·
      refine ⟨441194033477646123690041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294129355651764082460027 441194033477646123690041)
      ·
        refine ⟨330895525108234592767531, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 441194033477646123690041 330895525108234592767531)
        ·
          refine ⟨496343287662351889151297, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 330895525108234592767531 496343287662351889151297)
          ·
            refine ⟨372257465746763916863473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 496343287662351889151297 372257465746763916863473)
            ·
              refine ⟨279193099310072937647605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 372257465746763916863473 279193099310072937647605)
              ·
                refine ⟨26174353060319337904463, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279193099310072937647605 26174353060319337904463)
                ·
                  rfl

theorem cell21_344077_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 2, 1, 2, 2, 5].length) (baseStart_344077 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344077 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344077 prefixEnd_344077 := by exact prefixLift 344077
  have htrace : WordTrace (prefixWord ++ tailWord_344077) baseStart_344077 baseEnd_344077 := by
    simpa [prefixWord, tailWord_344077, baseEnd_344077] using wordTrace_append hprefix tailTrace_344077
  have hstable : (prefixWord ++ tailWord_344077).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344077).length < 2 ^ (prefixWord ++ tailWord_344077).sum := by decide
  have hdescent : baseEnd_344077 < baseStart_344077 := by decide
  rcases family_descends (prefixWord ++ tailWord_344077) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344085 : List Nat := [1, 3, 2, 1, 5, 1, 1, 7]
def baseStart_344085 : Nat := 118140960795 + 344085 * 2 ^ 59
def prefixEnd_344085 : Nat := 4983230072969 + 3 ^ 40 * 344085 * 2
def baseEnd_344085 : Nat := 26174961629983925860013

theorem tailTrace_344085 : CollatzResearch.WordTrace tailWord_344085 prefixEnd_344085 26174961629983925860013 := by
  unfold tailWord_344085
  simp only [CollatzResearch.WordTrace]
  refine ⟨12549810958446284884585709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8366540638964189923057139 12549810958446284884585709)
  ·
    refine ⟨4706179109417356831719641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12549810958446284884585709 4706179109417356831719641)
    ·
      refine ⟨3529634332063017623789731, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4706179109417356831719641 3529634332063017623789731)
      ·
        refine ⟨5294451498094526435684597, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3529634332063017623789731 5294451498094526435684597)
        ·
          refine ⟨496354827946361853345431, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5294451498094526435684597 496354827946361853345431)
          ·
            refine ⟨744532241919542780018147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 496354827946361853345431 744532241919542780018147)
            ·
              refine ⟨1116798362879314170027221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 744532241919542780018147 1116798362879314170027221)
              ·
                refine ⟨26174961629983925860013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1116798362879314170027221 26174961629983925860013)
                ·
                  rfl

theorem cell21_344085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 7].length) (baseStart_344085 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344085 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344085 prefixEnd_344085 := by exact prefixLift 344085
  have htrace : WordTrace (prefixWord ++ tailWord_344085) baseStart_344085 baseEnd_344085 := by
    simpa [prefixWord, tailWord_344085, baseEnd_344085] using wordTrace_append hprefix tailTrace_344085
  have hstable : (prefixWord ++ tailWord_344085).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344085).length < 2 ^ (prefixWord ++ tailWord_344085).sum := by decide
  have hdescent : baseEnd_344085 < baseStart_344085 := by decide
  rcases family_descends (prefixWord ++ tailWord_344085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344220 : List Nat := [2, 2, 3, 2, 1, 1, 10]
def baseStart_344220 : Nat := 118140960795 + 344220 * 2 ^ 59
def prefixEnd_344220 : Nat := 4983230072969 + 3 ^ 40 * 344220 * 2
def baseEnd_344220 : Nat := 8728410414357949203307

theorem tailTrace_344220 : CollatzResearch.WordTrace tailWord_344220 prefixEnd_344220 8728410414357949203307 := by
  unfold tailWord_344220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6277367406478601470375057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8369823208638135293833409 6277367406478601470375057)
  ·
    refine ⟨4708025554858951102781293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6277367406478601470375057 4708025554858951102781293)
    ·
      refine ⟨1765509583072106663542985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4708025554858951102781293 1765509583072106663542985)
      ·
        refine ⟨1324132187304079997657239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1765509583072106663542985 1324132187304079997657239)
        ·
          refine ⟨1986198280956119996485859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1324132187304079997657239 1986198280956119996485859)
          ·
            refine ⟨2979297421434179994728789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1986198280956119996485859 2979297421434179994728789)
            ·
              refine ⟨8728410414357949203307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 2979297421434179994728789 8728410414357949203307)
              ·
                rfl

theorem cell21_344220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 10].length) (baseStart_344220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344220 prefixEnd_344220 := by exact prefixLift 344220
  have htrace : WordTrace (prefixWord ++ tailWord_344220) baseStart_344220 baseEnd_344220 := by
    simpa [prefixWord, tailWord_344220, baseEnd_344220] using wordTrace_append hprefix tailTrace_344220
  have hstable : (prefixWord ++ tailWord_344220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344220).length < 2 ^ (prefixWord ++ tailWord_344220).sum := by decide
  have hdescent : baseEnd_344220 < baseStart_344220 := by decide
  rcases family_descends (prefixWord ++ tailWord_344220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344223 : List Nat := [1, 1, 2, 6, 1, 1, 3, 2, 4]
def baseStart_344223 : Nat := 118140960795 + 344223 * 2 ^ 59
def prefixEnd_344223 : Nat := 4983230072969 + 3 ^ 40 * 344223 * 2
def baseEnd_344223 : Nat := 78556378370094204279757

theorem tailTrace_344223 : CollatzResearch.WordTrace tailWord_344223 prefixEnd_344223 78556378370094204279757 := by
  unfold tailWord_344223
  simp only [CollatzResearch.WordTrace]
  refine ⟨12554844231946334453109323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8369896154630889635406215 12554844231946334453109323)
  ·
    refine ⟨18832266347919501679663985, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12554844231946334453109323 18832266347919501679663985)
    ·
      refine ⟨14124199760939626259747989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18832266347919501679663985 14124199760939626259747989)
      ·
        refine ⟨662071863794044980925687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 14124199760939626259747989 662071863794044980925687)
        ·
          refine ⟨993107795691067471388531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662071863794044980925687 993107795691067471388531)
          ·
            refine ⟨1489661693536601207082797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993107795691067471388531 1489661693536601207082797)
            ·
              refine ⟨558623135076225452656049, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1489661693536601207082797 558623135076225452656049)
              ·
                refine ⟨418967351307169089492037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 558623135076225452656049 418967351307169089492037)
                ·
                  refine ⟨78556378370094204279757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 418967351307169089492037 78556378370094204279757)
                  ·
                    rfl

theorem cell21_344223_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 1, 1, 3, 2, 4].length) (baseStart_344223 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344223 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344223 prefixEnd_344223 := by exact prefixLift 344223
  have htrace : WordTrace (prefixWord ++ tailWord_344223) baseStart_344223 baseEnd_344223 := by
    simpa [prefixWord, tailWord_344223, baseEnd_344223] using wordTrace_append hprefix tailTrace_344223
  have hstable : (prefixWord ++ tailWord_344223).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344223).length < 2 ^ (prefixWord ++ tailWord_344223).sum := by decide
  have hdescent : baseEnd_344223 < baseStart_344223 := by decide
  rcases family_descends (prefixWord ++ tailWord_344223) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344285 : List Nat := [1, 4, 3, 2, 1, 3, 1, 1, 5]
def baseStart_344285 : Nat := 118140960795 + 344285 * 2 ^ 59
def prefixEnd_344285 : Nat := 4983230072969 + 3 ^ 40 * 344285 * 2
def baseEnd_344285 : Nat := 78570527614795874246297

theorem tailTrace_344285 : CollatzResearch.WordTrace tailWord_344285 prefixEnd_344285 78570527614795874246297 := by
  unfold tailWord_344285
  simp only [CollatzResearch.WordTrace]
  refine ⟨12557105557721719041866309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8371403705147812694577539 12557105557721719041866309)
  ·
    refine ⟨2354457292072822320349933, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12557105557721719041866309 2354457292072822320349933)
    ·
      refine ⟨882921484527308370131225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2354457292072822320349933 882921484527308370131225)
      ·
        refine ⟨662191113395481277598419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 882921484527308370131225 662191113395481277598419)
        ·
          refine ⟨993286670093221916397629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662191113395481277598419 993286670093221916397629)
          ·
            refine ⟨372482501284958218649111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 993286670093221916397629 372482501284958218649111)
            ·
              refine ⟨558723751927437327973667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 372482501284958218649111 558723751927437327973667)
              ·
                refine ⟨838085627891155991960501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 558723751927437327973667 838085627891155991960501)
                ·
                  refine ⟨78570527614795874246297, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838085627891155991960501 78570527614795874246297)
                  ·
                    rfl

theorem cell21_344285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 2, 1, 3, 1, 1, 5].length) (baseStart_344285 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344285 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344285 prefixEnd_344285 := by exact prefixLift 344285
  have htrace : WordTrace (prefixWord ++ tailWord_344285) baseStart_344285 baseEnd_344285 := by
    simpa [prefixWord, tailWord_344285, baseEnd_344285] using wordTrace_append hprefix tailTrace_344285
  have hstable : (prefixWord ++ tailWord_344285).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344285).length < 2 ^ (prefixWord ++ tailWord_344285).sum := by decide
  have hdescent : baseEnd_344285 < baseStart_344285 := by decide
  rcases family_descends (prefixWord ++ tailWord_344285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344296 : List Nat := [2, 1, 4, 1, 2, 2, 1, 8]
def baseStart_344296 : Nat := 118140960795 + 344296 * 2 ^ 59
def prefixEnd_344296 : Nat := 4983230072969 + 3 ^ 40 * 344296 * 2
def baseEnd_344296 : Nat := 26191012654887433187647

theorem tailTrace_344296 : CollatzResearch.WordTrace tailWord_344296 prefixEnd_344296 26191012654887433187647 := by
  unfold tailWord_344296
  simp only [CollatzResearch.WordTrace]
  refine ⟨6278753380340933960258371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8371671173787911947011161 6278753380340933960258371)
  ·
    refine ⟨9418130070511400940387557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6278753380340933960258371 9418130070511400940387557)
    ·
      refine ⟨1765899388220887676322667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9418130070511400940387557 1765899388220887676322667)
      ·
        refine ⟨2648849082331331514484001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1765899388220887676322667 2648849082331331514484001)
        ·
          refine ⟨1986636811748498635863001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2648849082331331514484001 1986636811748498635863001)
          ·
            refine ⟨1489977608811373976897251, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1986636811748498635863001 1489977608811373976897251)
            ·
              refine ⟨2234966413217060965345877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1489977608811373976897251 2234966413217060965345877)
              ·
                refine ⟨26191012654887433187647, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2234966413217060965345877 26191012654887433187647)
                ·
                  rfl

theorem cell21_344296_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 2, 1, 8].length) (baseStart_344296 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344296 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344296 prefixEnd_344296 := by exact prefixLift 344296
  have htrace : WordTrace (prefixWord ++ tailWord_344296) baseStart_344296 baseEnd_344296 := by
    simpa [prefixWord, tailWord_344296, baseEnd_344296] using wordTrace_append hprefix tailTrace_344296
  have hstable : (prefixWord ++ tailWord_344296).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344296).length < 2 ^ (prefixWord ++ tailWord_344296).sum := by decide
  have hdescent : baseEnd_344296 < baseStart_344296 := by decide
  rcases family_descends (prefixWord ++ tailWord_344296) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344341 : List Nat := [1, 3, 2, 1, 2, 1, 2, 3, 6]
def baseStart_344341 : Nat := 118140960795 + 344341 * 2 ^ 59
def prefixEnd_344341 : Nat := 4983230072969 + 3 ^ 40 * 344341 * 2
def baseEnd_344341 : Nat := 78583307577752221312849

theorem tailTrace_344341 : CollatzResearch.WordTrace tailWord_344341 prefixEnd_344341 78583307577752221312849 := by
  unfold tailWord_344341
  simp only [CollatzResearch.WordTrace]
  refine ⟨12559148045518840605904877, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8372765363679227070603251 12559148045518840605904877)
  ·
    refine ⟨4709680517069565227214329, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12559148045518840605904877 4709680517069565227214329)
    ·
      refine ⟨3532260387802173920410747, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4709680517069565227214329 3532260387802173920410747)
      ·
        refine ⟨5298390581703260880616121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3532260387802173920410747 5298390581703260880616121)
        ·
          refine ⟨3973792936277445660462091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5298390581703260880616121 3973792936277445660462091)
          ·
            refine ⟨5960689404416168490693137, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3973792936277445660462091 5960689404416168490693137)
            ·
              refine ⟨4470517053312126368019853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5960689404416168490693137 4470517053312126368019853)
              ·
                refine ⟨1676443894992047388007445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4470517053312126368019853 1676443894992047388007445)
                ·
                  refine ⟨78583307577752221312849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1676443894992047388007445 78583307577752221312849)
                  ·
                    rfl

theorem cell21_344341_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 2, 3, 6].length) (baseStart_344341 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344341 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344341 prefixEnd_344341 := by exact prefixLift 344341
  have htrace : WordTrace (prefixWord ++ tailWord_344341) baseStart_344341 baseEnd_344341 := by
    simpa [prefixWord, tailWord_344341, baseEnd_344341] using wordTrace_append hprefix tailTrace_344341
  have hstable : (prefixWord ++ tailWord_344341).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344341).length < 2 ^ (prefixWord ++ tailWord_344341).sum := by decide
  have hdescent : baseEnd_344341 < baseStart_344341 := by decide
  rcases family_descends (prefixWord ++ tailWord_344341) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344344 : List Nat := [2, 1, 2, 3, 1, 2, 3, 4, 3]
def baseStart_344344 : Nat := 118140960795 + 344344 * 2 ^ 59
def prefixEnd_344344 : Nat := 4983230072969 + 3 ^ 40 * 344344 * 2
def baseEnd_344344 : Nat := 78583992218624882762843

theorem tailTrace_344344 : CollatzResearch.WordTrace tailWord_344344 prefixEnd_344344 78583992218624882762843 := by
  unfold tailWord_344344
  simp only [CollatzResearch.WordTrace]
  refine ⟨6279628732253986059132043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8372838309671981412176057 6279628732253986059132043)
  ·
    refine ⟨9419443098380979088698065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6279628732253986059132043 9419443098380979088698065)
    ·
      refine ⟨7064582323785734316523549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9419443098380979088698065 7064582323785734316523549)
      ·
        refine ⟨2649218371419650368696331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7064582323785734316523549 2649218371419650368696331)
        ·
          refine ⟨3973827557129475553044497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2649218371419650368696331 3973827557129475553044497)
          ·
            refine ⟨2980370667847106664783373, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3973827557129475553044497 2980370667847106664783373)
            ·
              refine ⟨1117639000442664999293765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 2980370667847106664783373 1117639000442664999293765)
              ·
                refine ⟨209557312582999687367581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1117639000442664999293765 209557312582999687367581)
                ·
                  refine ⟨78583992218624882762843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209557312582999687367581 78583992218624882762843)
                  ·
                    rfl

theorem cell21_344344_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 1, 2, 3, 4, 3].length) (baseStart_344344 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344344 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344344 prefixEnd_344344 := by exact prefixLift 344344
  have htrace : WordTrace (prefixWord ++ tailWord_344344) baseStart_344344 baseEnd_344344 := by
    simpa [prefixWord, tailWord_344344, baseEnd_344344] using wordTrace_append hprefix tailTrace_344344
  have hstable : (prefixWord ++ tailWord_344344).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344344).length < 2 ^ (prefixWord ++ tailWord_344344).sum := by decide
  have hdescent : baseEnd_344344 < baseStart_344344 := by decide
  rcases family_descends (prefixWord ++ tailWord_344344) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344437 : List Nat := [1, 3, 4, 1, 2, 1, 3, 3, 3]
def baseStart_344437 : Nat := 118140960795 + 344437 * 2 ^ 59
def prefixEnd_344437 : Nat := 4983230072969 + 3 ^ 40 * 344437 * 2
def baseEnd_344437 : Nat := 78605216085677387712653

theorem tailTrace_344437 : CollatzResearch.WordTrace tailWord_344437 prefixEnd_344437 78605216085677387712653 := by
  unfold tailWord_344437
  simp only [CollatzResearch.WordTrace]
  refine ⟨12562649453171049001399565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8375099635447366000933043 12562649453171049001399565)
  ·
    refine ⟨4710993544939143375524837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12562649453171049001399565 4710993544939143375524837)
    ·
      refine ⟨883311289676089382910907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4710993544939143375524837 883311289676089382910907)
      ·
        refine ⟨1324966934514134074366361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883311289676089382910907 1324966934514134074366361)
        ·
          refine ⟨993725200885600555774771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1324966934514134074366361 993725200885600555774771)
          ·
            refine ⟨1490587801328400833662157, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 993725200885600555774771 1490587801328400833662157)
            ·
              refine ⟨558970425498150312623309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1490587801328400833662157 558970425498150312623309)
              ·
                refine ⟨209613909561806367233741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 558970425498150312623309 209613909561806367233741)
                ·
                  refine ⟨78605216085677387712653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209613909561806367233741 78605216085677387712653)
                  ·
                    rfl

theorem cell21_344437_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 2, 1, 3, 3, 3].length) (baseStart_344437 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344437 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344437 prefixEnd_344437 := by exact prefixLift 344437
  have htrace : WordTrace (prefixWord ++ tailWord_344437) baseStart_344437 baseEnd_344437 := by
    simpa [prefixWord, tailWord_344437, baseEnd_344437] using wordTrace_append hprefix tailTrace_344437
  have hstable : (prefixWord ++ tailWord_344437).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344437).length < 2 ^ (prefixWord ++ tailWord_344437).sum := by decide
  have hdescent : baseEnd_344437 < baseStart_344437 := by decide
  rcases family_descends (prefixWord ++ tailWord_344437) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344510 : List Nat := [4, 2, 1, 1, 1, 1, 3, 4, 4]
def baseStart_344510 : Nat := 118140960795 + 344510 * 2 ^ 59
def prefixEnd_344510 : Nat := 4983230072969 + 3 ^ 40 * 344510 * 2
def baseEnd_344510 : Nat := 78621875680245482995837

theorem tailTrace_344510 : CollatzResearch.WordTrace tailWord_344510 prefixEnd_344510 78621875680245482995837 := by
  unfold tailWord_344510
  simp only [CollatzResearch.WordTrace]
  refine ⟨1570663997738322808600873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8376874654604388312537989 1570663997738322808600873)
  ·
    refine ⟨1177997998303742106450655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1570663997738322808600873 1177997998303742106450655)
    ·
      refine ⟨1766996997455613159675983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1177997998303742106450655 1766996997455613159675983)
      ·
        refine ⟨2650495496183419739513975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1766996997455613159675983 2650495496183419739513975)
        ·
          refine ⟨3975743244275129609270963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2650495496183419739513975 3975743244275129609270963)
          ·
            refine ⟨5963614866412694413906445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3975743244275129609270963 5963614866412694413906445)
            ·
              refine ⟨2236355574904760405214917, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5963614866412694413906445 2236355574904760405214917)
              ·
                refine ⟨419316670294642575977797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 2236355574904760405214917 419316670294642575977797)
                ·
                  refine ⟨78621875680245482995837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419316670294642575977797 78621875680245482995837)
                  ·
                    rfl

theorem cell21_344510_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 1, 3, 4, 4].length) (baseStart_344510 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344510 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344510 prefixEnd_344510 := by exact prefixLift 344510
  have htrace : WordTrace (prefixWord ++ tailWord_344510) baseStart_344510 baseEnd_344510 := by
    simpa [prefixWord, tailWord_344510, baseEnd_344510] using wordTrace_append hprefix tailTrace_344510
  have hstable : (prefixWord ++ tailWord_344510).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344510).length < 2 ^ (prefixWord ++ tailWord_344510).sum := by decide
  have hdescent : baseEnd_344510 < baseStart_344510 := by decide
  rcases family_descends (prefixWord ++ tailWord_344510) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344541 : List Nat := [1, 4, 3, 1, 1, 1, 5, 5]
def baseStart_344541 : Nat := 118140960795 + 344541 * 2 ^ 59
def prefixEnd_344541 : Nat := 4983230072969 + 3 ^ 40 * 344541 * 2
def baseEnd_344541 : Nat := 26209650100865439326369

theorem tailTrace_344541 : CollatzResearch.WordTrace tailWord_344541 prefixEnd_344541 26209650100865439326369 := by
  unfold tailWord_344541
  simp only [CollatzResearch.WordTrace]
  refine ⟨12566442644794274763185477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8377628429862849842123651 12566442644794274763185477)
  ·
    refine ⟨2356207995898926518097277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12566442644794274763185477 2356207995898926518097277)
    ·
      refine ⟨883577998462097444286479, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2356207995898926518097277 883577998462097444286479)
      ·
        refine ⟨1325366997693146166429719, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 883577998462097444286479 1325366997693146166429719)
        ·
          refine ⟨1988050496539719249644579, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1325366997693146166429719 1988050496539719249644579)
          ·
            refine ⟨2982075744809578874466869, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1988050496539719249644579 2982075744809578874466869)
            ·
              refine ⟨279569601075898019481269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 2982075744809578874466869 279569601075898019481269)
              ·
                refine ⟨26209650100865439326369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 279569601075898019481269 26209650100865439326369)
                ·
                  rfl

theorem cell21_344541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 3, 1, 1, 1, 5, 5].length) (baseStart_344541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344541 prefixEnd_344541 := by exact prefixLift 344541
  have htrace : WordTrace (prefixWord ++ tailWord_344541) baseStart_344541 baseEnd_344541 := by
    simpa [prefixWord, tailWord_344541, baseEnd_344541] using wordTrace_append hprefix tailTrace_344541
  have hstable : (prefixWord ++ tailWord_344541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344541).length < 2 ^ (prefixWord ++ tailWord_344541).sum := by decide
  have hdescent : baseEnd_344541 < baseStart_344541 := by decide
  rcases family_descends (prefixWord ++ tailWord_344541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344589 : List Nat := [1, 7, 1, 1, 1, 1, 2, 2, 5]
def baseStart_344589 : Nat := 118140960795 + 344589 * 2 ^ 59
def prefixEnd_344589 : Nat := 4983230072969 + 3 ^ 40 * 344589 * 2
def baseEnd_344589 : Nat := 78639904556558901179009

theorem tailTrace_344589 : CollatzResearch.WordTrace tailWord_344589 prefixEnd_344589 78639904556558901179009 := by
  unfold tailWord_344589
  simp only [CollatzResearch.WordTrace]
  refine ⟨12568193348620378960932821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8378795565746919307288547 12568193348620378960932821)
  ·
    refine ⟨294567031608290131896863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12568193348620378960932821 294567031608290131896863)
    ·
      refine ⟨441850547412435197845295, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 294567031608290131896863 441850547412435197845295)
      ·
        refine ⟨662775821118652796767943, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 441850547412435197845295 662775821118652796767943)
        ·
          refine ⟨994163731677979195151915, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 662775821118652796767943 994163731677979195151915)
          ·
            refine ⟨1491245597516968792727873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 994163731677979195151915 1491245597516968792727873)
            ·
              refine ⟨1118434198137726594545905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1491245597516968792727873 1118434198137726594545905)
              ·
                refine ⟨838825648603294945909429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1118434198137726594545905 838825648603294945909429)
                ·
                  refine ⟨78639904556558901179009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 838825648603294945909429 78639904556558901179009)
                  ·
                    rfl

theorem cell21_344589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 1, 2, 2, 5].length) (baseStart_344589 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344589 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344589 prefixEnd_344589 := by exact prefixLift 344589
  have htrace : WordTrace (prefixWord ++ tailWord_344589) baseStart_344589 baseEnd_344589 := by
    simpa [prefixWord, tailWord_344589, baseEnd_344589] using wordTrace_append hprefix tailTrace_344589
  have hstable : (prefixWord ++ tailWord_344589).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344589).length < 2 ^ (prefixWord ++ tailWord_344589).sum := by decide
  have hdescent : baseEnd_344589 < baseStart_344589 := by decide
  rcases family_descends (prefixWord ++ tailWord_344589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344600 : List Nat := [2, 1, 2, 3, 3, 2, 1, 7]
def baseStart_344600 : Nat := 118140960795 + 344600 * 2 ^ 59
def prefixEnd_344600 : Nat := 4983230072969 + 3 ^ 40 * 344600 * 2
def baseEnd_344600 : Nat := 26214138302141775498551

theorem tailTrace_344600 : CollatzResearch.WordTrace tailWord_344600 prefixEnd_344600 26214138302141775498551 := by
  unfold tailWord_344600
  simp only [CollatzResearch.WordTrace]
  refine ⟨6284297275790263919791627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8379063034387018559722169 6284297275790263919791627)
  ·
    refine ⟨9426445913685395879687441, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6284297275790263919791627 9426445913685395879687441)
    ·
      refine ⟨7069834435264046909765581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9426445913685395879687441 7069834435264046909765581)
      ·
        refine ⟨2651187913224017591162093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7069834435264046909765581 2651187913224017591162093)
        ·
          refine ⟨994195467459006596685785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2651187913224017591162093 994195467459006596685785)
          ·
            refine ⟨745646600594254947514339, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 994195467459006596685785 745646600594254947514339)
            ·
              refine ⟨1118469900891382421271509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 745646600594254947514339 1118469900891382421271509)
              ·
                refine ⟨26214138302141775498551, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1118469900891382421271509 26214138302141775498551)
                ·
                  rfl

theorem cell21_344600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 2, 1, 7].length) (baseStart_344600 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344600 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344600 prefixEnd_344600 := by exact prefixLift 344600
  have htrace : WordTrace (prefixWord ++ tailWord_344600) baseStart_344600 baseEnd_344600 := by
    simpa [prefixWord, tailWord_344600, baseEnd_344600] using wordTrace_append hprefix tailTrace_344600
  have hstable : (prefixWord ++ tailWord_344600).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344600).length < 2 ^ (prefixWord ++ tailWord_344600).sum := by decide
  have hdescent : baseEnd_344600 < baseStart_344600 := by decide
  rcases family_descends (prefixWord ++ tailWord_344600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344814 : List Nat := [4, 1, 2, 1, 1, 4, 1, 3, 4]
def baseStart_344814 : Nat := 118140960795 + 344814 * 2 ^ 59
def prefixEnd_344814 : Nat := 4983230072969 + 3 ^ 40 * 344814 * 2
def baseEnd_344814 : Nat := 78691252622008509928549

theorem tailTrace_344814 : CollatzResearch.WordTrace tailWord_344814 prefixEnd_344814 78691252622008509928549 := by
  unfold tailWord_344814
  simp only [CollatzResearch.WordTrace]
  refine ⟨1572049971600655298484187, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8384266515203494925248997 1572049971600655298484187)
  ·
    refine ⟨2358074957400982947726281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1572049971600655298484187 2358074957400982947726281)
    ·
      refine ⟨1768556218050737210794711, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2358074957400982947726281 1768556218050737210794711)
      ·
        refine ⟨2652834327076105816192067, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1768556218050737210794711 2652834327076105816192067)
        ·
          refine ⟨3979251490614158724288101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2652834327076105816192067 3979251490614158724288101)
          ·
            refine ⟨746109654490154760804019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 3979251490614158724288101 746109654490154760804019)
            ·
              refine ⟨1119164481735232141206029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 746109654490154760804019 1119164481735232141206029)
              ·
                refine ⟨419686680650712052952261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119164481735232141206029 419686680650712052952261)
                ·
                  refine ⟨78691252622008509928549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419686680650712052952261 78691252622008509928549)
                  ·
                    rfl

theorem cell21_344814_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 4, 1, 3, 4].length) (baseStart_344814 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344814 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344814 prefixEnd_344814 := by exact prefixLift 344814
  have htrace : WordTrace (prefixWord ++ tailWord_344814) baseStart_344814 baseEnd_344814 := by
    simpa [prefixWord, tailWord_344814, baseEnd_344814] using wordTrace_append hprefix tailTrace_344814
  have hstable : (prefixWord ++ tailWord_344814).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344814).length < 2 ^ (prefixWord ++ tailWord_344814).sum := by decide
  have hdescent : baseEnd_344814 < baseStart_344814 := by decide
  rcases family_descends (prefixWord ++ tailWord_344814) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344845 : List Nat := [1, 7, 2, 11]
def baseStart_344845 : Nat := 118140960795 + 344845 * 2 ^ 59
def prefixEnd_344845 : Nat := 4983230072969 + 3 ^ 40 * 344845 * 2
def baseEnd_344845 : Nat := 323861428989133106633

theorem tailTrace_344845 : CollatzResearch.WordTrace tailWord_344845 prefixEnd_344845 323861428989133106633 := by
  unfold tailWord_344845
  simp only [CollatzResearch.WordTrace]
  refine ⟨12577530435692934682251989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8385020290461956454834659 12577530435692934682251989)
  ·
    refine ⟨294785869586553156615281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12577530435692934682251989 294785869586553156615281)
    ·
      refine ⟨221089402189914867461461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 294785869586553156615281 221089402189914867461461)
      ·
        refine ⟨323861428989133106633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 11 221089402189914867461461 323861428989133106633)
        ·
          rfl

theorem cell21_344845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 2, 11].length) (baseStart_344845 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344845 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344845 prefixEnd_344845 := by exact prefixLift 344845
  have htrace : WordTrace (prefixWord ++ tailWord_344845) baseStart_344845 baseEnd_344845 := by
    simpa [prefixWord, tailWord_344845, baseEnd_344845] using wordTrace_append hprefix tailTrace_344845
  have hstable : (prefixWord ++ tailWord_344845).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344845).length < 2 ^ (prefixWord ++ tailWord_344845).sum := by decide
  have hdescent : baseEnd_344845 < baseStart_344845 := by decide
  rcases family_descends (prefixWord ++ tailWord_344845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344893 : List Nat := [1, 4, 1, 4, 2, 1, 2, 3, 3]
def baseStart_344893 : Nat := 118140960795 + 344893 * 2 ^ 59
def prefixEnd_344893 : Nat := 4983230072969 + 3 ^ 40 * 344893 * 2
def baseEnd_344893 : Nat := 78709281498321928111721

theorem tailTrace_344893 : CollatzResearch.WordTrace tailWord_344893 prefixEnd_344893 78709281498321928111721 := by
  unfold tailWord_344893
  simp only [CollatzResearch.WordTrace]
  refine ⟨12579281139519038879999333, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8386187426346025919999555 12579281139519038879999333)
  ·
    refine ⟨2358615213659819789999875, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12579281139519038879999333 2358615213659819789999875)
    ·
      refine ⟨3537922820489729684999813, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2358615213659819789999875 3537922820489729684999813)
      ·
        refine ⟨663360528841824315937465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3537922820489729684999813 663360528841824315937465)
        ·
          refine ⟨497520396631368236953099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 663360528841824315937465 497520396631368236953099)
          ·
            refine ⟨746280594947052355429649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 497520396631368236953099 746280594947052355429649)
            ·
              refine ⟨559710446210289266572237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746280594947052355429649 559710446210289266572237)
              ·
                refine ⟨209891417328858474964589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 559710446210289266572237 209891417328858474964589)
                ·
                  refine ⟨78709281498321928111721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 209891417328858474964589 78709281498321928111721)
                  ·
                    rfl

theorem cell21_344893_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 4, 2, 1, 2, 3, 3].length) (baseStart_344893 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344893 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344893 prefixEnd_344893 := by exact prefixLift 344893
  have htrace : WordTrace (prefixWord ++ tailWord_344893) baseStart_344893 baseEnd_344893 := by
    simpa [prefixWord, tailWord_344893, baseEnd_344893] using wordTrace_append hprefix tailTrace_344893
  have hstable : (prefixWord ++ tailWord_344893).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344893).length < 2 ^ (prefixWord ++ tailWord_344893).sum := by decide
  have hdescent : baseEnd_344893 < baseStart_344893 := by decide
  rcases family_descends (prefixWord ++ tailWord_344893) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344949 : List Nat := [1, 3, 4, 1, 1, 2, 1, 2, 6]
def baseStart_344949 : Nat := 118140960795 + 344949 * 2 ^ 59
def prefixEnd_344949 : Nat := 4983230072969 + 3 ^ 40 * 344949 * 2
def baseEnd_344949 : Nat := 78722061461278275178273

theorem tailTrace_344949 : CollatzResearch.WordTrace tailWord_344949 prefixEnd_344949 78722061461278275178273 := by
  unfold tailWord_344949
  simp only [CollatzResearch.WordTrace]
  refine ⟨12581323627316160444037901, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8387549084877440296025267 12581323627316160444037901)
  ·
    refine ⟨4717996360243560166514213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12581323627316160444037901 4717996360243560166514213)
    ·
      refine ⟨884624317545667531221415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4717996360243560166514213 884624317545667531221415)
      ·
        refine ⟨1326936476318501296832123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884624317545667531221415 1326936476318501296832123)
        ·
          refine ⟨1990404714477751945248185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1326936476318501296832123 1990404714477751945248185)
          ·
            refine ⟨1492803535858313958936139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1990404714477751945248185 1492803535858313958936139)
            ·
              refine ⟨2239205303787470938404209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1492803535858313958936139 2239205303787470938404209)
              ·
                refine ⟨1679403977840603203803157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2239205303787470938404209 1679403977840603203803157)
                ·
                  refine ⟨78722061461278275178273, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1679403977840603203803157 78722061461278275178273)
                  ·
                    rfl

theorem cell21_344949_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 2, 1, 2, 6].length) (baseStart_344949 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344949 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344949 prefixEnd_344949 := by exact prefixLift 344949
  have htrace : WordTrace (prefixWord ++ tailWord_344949) baseStart_344949 baseEnd_344949 := by
    simpa [prefixWord, tailWord_344949, baseEnd_344949] using wordTrace_append hprefix tailTrace_344949
  have hstable : (prefixWord ++ tailWord_344949).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344949).length < 2 ^ (prefixWord ++ tailWord_344949).sum := by decide
  have hdescent : baseEnd_344949 < baseStart_344949 := by decide
  rcases family_descends (prefixWord ++ tailWord_344949) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_344980 : List Nat := [2, 4, 2, 1, 1, 1, 4, 6]
def baseStart_344980 : Nat := 118140960795 + 344980 * 2 ^ 59
def prefixEnd_344980 : Nat := 4983230072969 + 3 ^ 40 * 344980 * 2
def baseEnd_344980 : Nat := 26243045361209703387181

theorem tailTrace_344980 : CollatzResearch.WordTrace tailWord_344980 prefixEnd_344980 26243045361209703387181 := by
  unfold tailWord_344980
  simp only [CollatzResearch.WordTrace]
  refine ⟨6291227145101926369208197, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8388302860135901825610929 6291227145101926369208197)
  ·
    refine ⟨1179605089706611194226537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6291227145101926369208197 1179605089706611194226537)
    ·
      refine ⟨884703817279958395669903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1179605089706611194226537 884703817279958395669903)
      ·
        refine ⟨1327055725919937593504855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 884703817279958395669903 1327055725919937593504855)
        ·
          refine ⟨1990583588879906390257283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1327055725919937593504855 1990583588879906390257283)
          ·
            refine ⟨2985875383319859585385925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1990583588879906390257283 2985875383319859585385925)
            ·
              refine ⟨559851634372473672259861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 2985875383319859585385925 559851634372473672259861)
              ·
                refine ⟨26243045361209703387181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 559851634372473672259861 26243045361209703387181)
                ·
                  rfl

theorem cell21_344980_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 6].length) (baseStart_344980 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_344980 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_344980 prefixEnd_344980 := by exact prefixLift 344980
  have htrace : WordTrace (prefixWord ++ tailWord_344980) baseStart_344980 baseEnd_344980 := by
    simpa [prefixWord, tailWord_344980, baseEnd_344980] using wordTrace_append hprefix tailTrace_344980
  have hstable : (prefixWord ++ tailWord_344980).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_344980).length < 2 ^ (prefixWord ++ tailWord_344980).sum := by decide
  have hdescent : baseEnd_344980 < baseStart_344980 := by decide
  rcases family_descends (prefixWord ++ tailWord_344980) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345014 : List Nat := [5, 1, 4, 1, 1, 9]
def baseStart_345014 : Nat := 118140960795 + 345014 * 2 ^ 59
def prefixEnd_345014 : Nat := 4983230072969 + 3 ^ 40 * 345014 * 2
def baseEnd_345014 : Nat := 2916181309142689133141

theorem tailTrace_345014 : CollatzResearch.WordTrace tailWord_345014 prefixEnd_345014 2916181309142689133141 := by
  unfold tailWord_345014
  simp only [CollatzResearch.WordTrace]
  refine ⟨786480898255042284072131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8389129581387117696769397 786480898255042284072131)
  ·
    refine ⟨1179721347382563426108197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 786480898255042284072131 1179721347382563426108197)
    ·
      refine ⟨221197752634230642395287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1179721347382563426108197 221197752634230642395287)
      ·
        refine ⟨331796628951345963592931, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 221197752634230642395287 331796628951345963592931)
        ·
          refine ⟨497694943427018945389397, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 331796628951345963592931 497694943427018945389397)
          ·
            refine ⟨2916181309142689133141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 9 497694943427018945389397 2916181309142689133141)
            ·
              rfl

theorem cell21_345014_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 4, 1, 1, 9].length) (baseStart_345014 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345014 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345014 prefixEnd_345014 := by exact prefixLift 345014
  have htrace : WordTrace (prefixWord ++ tailWord_345014) baseStart_345014 baseEnd_345014 := by
    simpa [prefixWord, tailWord_345014, baseEnd_345014] using wordTrace_append hprefix tailTrace_345014
  have hstable : (prefixWord ++ tailWord_345014).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345014).length < 2 ^ (prefixWord ++ tailWord_345014).sum := by decide
  have hdescent : baseEnd_345014 < baseStart_345014 := by decide
  rcases family_descends (prefixWord ++ tailWord_345014) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345039 : List Nat := [1, 1, 2, 1, 1, 6, 3, 6]
def baseStart_345039 : Nat := 118140960795 + 345039 * 2 ^ 59
def prefixEnd_345039 : Nat := 4983230072969 + 3 ^ 40 * 345039 * 2
def baseEnd_345039 : Nat := 26247533562486039559363

theorem tailTrace_345039 : CollatzResearch.WordTrace tailWord_345039 prefixEnd_345039 26247533562486039559363 := by
  unfold tailWord_345039
  simp only [CollatzResearch.WordTrace]
  refine ⟨12584606196990105814814171, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8389737464660070543209447 12584606196990105814814171)
  ·
    refine ⟨18876909295485158722221257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12584606196990105814814171 18876909295485158722221257)
    ·
      refine ⟨14157681971613869041665943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18876909295485158722221257 14157681971613869041665943)
      ·
        refine ⟨21236522957420803562498915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14157681971613869041665943 21236522957420803562498915)
        ·
          refine ⟨31854784436131205343748373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21236522957420803562498915 31854784436131205343748373)
          ·
            refine ⟨1493193020443650250488205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 31854784436131205343748373 1493193020443650250488205)
            ·
              refine ⟨559947382666368843933077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1493193020443650250488205 559947382666368843933077)
              ·
                refine ⟨26247533562486039559363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 559947382666368843933077 26247533562486039559363)
                ·
                  rfl

theorem cell21_345039_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 6, 3, 6].length) (baseStart_345039 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345039 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345039 prefixEnd_345039 := by exact prefixLift 345039
  have htrace : WordTrace (prefixWord ++ tailWord_345039) baseStart_345039 baseEnd_345039 := by
    simpa [prefixWord, tailWord_345039, baseEnd_345039] using wordTrace_append hprefix tailTrace_345039
  have hstable : (prefixWord ++ tailWord_345039).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345039).length < 2 ^ (prefixWord ++ tailWord_345039).sum := by decide
  have hdescent : baseEnd_345039 < baseStart_345039 := by decide
  rcases family_descends (prefixWord ++ tailWord_345039) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345042 : List Nat := [3, 2, 2, 3, 1, 1, 2, 3, 4]
def baseStart_345042 : Nat := 118140960795 + 345042 * 2 ^ 59
def prefixEnd_345042 : Nat := 4983230072969 + 3 ^ 40 * 345042 * 2
def baseEnd_345042 : Nat := 78743285328330780128083

theorem tailTrace_345042 : CollatzResearch.WordTrace tailWord_345042 prefixEnd_345042 78743285328330780128083 := by
  unfold tailWord_345042
  simp only [CollatzResearch.WordTrace]
  refine ⟨3146178903994809331793345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8389810410652824884782253 3146178903994809331793345)
  ·
    refine ⟨2359634177996106998845009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3146178903994809331793345 2359634177996106998845009)
    ·
      refine ⟨1769725633497080249133757, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2359634177996106998845009 1769725633497080249133757)
      ·
        refine ⟨663647112561405093425159, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1769725633497080249133757 663647112561405093425159)
        ·
          refine ⟨995470668842107640137739, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 663647112561405093425159 995470668842107640137739)
          ·
            refine ⟨1493206003263161460206609, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 995470668842107640137739 1493206003263161460206609)
            ·
              refine ⟨1119904502447371095154957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1493206003263161460206609 1119904502447371095154957)
              ·
                refine ⟨419964188417764160683109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1119904502447371095154957 419964188417764160683109)
                ·
                  refine ⟨78743285328330780128083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 419964188417764160683109 78743285328330780128083)
                  ·
                    rfl

theorem cell21_345042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 3, 1, 1, 2, 3, 4].length) (baseStart_345042 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345042 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345042 prefixEnd_345042 := by exact prefixLift 345042
  have htrace : WordTrace (prefixWord ++ tailWord_345042) baseStart_345042 baseEnd_345042 := by
    simpa [prefixWord, tailWord_345042, baseEnd_345042] using wordTrace_append hprefix tailTrace_345042
  have hstable : (prefixWord ++ tailWord_345042).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345042).length < 2 ^ (prefixWord ++ tailWord_345042).sum := by decide
  have hdescent : baseEnd_345042 < baseStart_345042 := by decide
  rcases family_descends (prefixWord ++ tailWord_345042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345146 : List Nat := [3, 1, 1, 1, 3, 1, 5, 1, 5]
def baseStart_345146 : Nat := 118140960795 + 345146 * 2 ^ 59
def prefixEnd_345146 : Nat := 4983230072969 + 3 ^ 40 * 345146 * 2
def baseEnd_345146 : Nat := 78767019545249710394537

theorem tailTrace_345146 : CollatzResearch.WordTrace tailWord_345146 prefixEnd_345146 78767019545249710394537 := by
  unfold tailWord_345146
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147127201900615772239823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8392339205068308725972861 3147127201900615772239823)
  ·
    refine ⟨4720690802850923658359735, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3147127201900615772239823 4720690802850923658359735)
    ·
      refine ⟨7081036204276385487539603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4720690802850923658359735 7081036204276385487539603)
      ·
        refine ⟨10621554306414578231309405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7081036204276385487539603 10621554306414578231309405)
        ·
          refine ⟨3983082864905466836741027, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10621554306414578231309405 3983082864905466836741027)
          ·
            refine ⟨5974624297358200255111541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3983082864905466836741027 5974624297358200255111541)
            ·
              refine ⟨560121027877331273916707, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 5974624297358200255111541 560121027877331273916707)
              ·
                refine ⟨840181541815996910875061, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 560121027877331273916707 840181541815996910875061)
                ·
                  refine ⟨78767019545249710394537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 840181541815996910875061 78767019545249710394537)
                  ·
                    rfl

theorem cell21_345146_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 3, 1, 5, 1, 5].length) (baseStart_345146 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345146 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345146 prefixEnd_345146 := by exact prefixLift 345146
  have htrace : WordTrace (prefixWord ++ tailWord_345146) baseStart_345146 baseEnd_345146 := by
    simpa [prefixWord, tailWord_345146, baseEnd_345146] using wordTrace_append hprefix tailTrace_345146
  have hstable : (prefixWord ++ tailWord_345146).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345146).length < 2 ^ (prefixWord ++ tailWord_345146).sum := by decide
  have hdescent : baseEnd_345146 < baseStart_345146 := by decide
  rcases family_descends (prefixWord ++ tailWord_345146) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345194 : List Nat := [3, 1, 3, 2, 2, 2, 2, 2, 4]
def baseStart_345194 : Nat := 118140960795 + 345194 * 2 ^ 59
def prefixEnd_345194 : Nat := 4983230072969 + 3 ^ 40 * 345194 * 2
def baseEnd_345194 : Nat := 78777973799212293594439

theorem tailTrace_345194 : CollatzResearch.WordTrace tailWord_345194 prefixEnd_345194 78777973799212293594439 := by
  unfold tailWord_345194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3147564877857141821676659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8393506340952378191137757 3147564877857141821676659)
  ·
    refine ⟨4721347316785712732514989, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3147564877857141821676659 4721347316785712732514989)
    ·
      refine ⟨1770505243794642274693121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4721347316785712732514989 1770505243794642274693121)
      ·
        refine ⟨1327878932845981706019841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1770505243794642274693121 1327878932845981706019841)
        ·
          refine ⟨995909199634486279514881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1327878932845981706019841 995909199634486279514881)
          ·
            refine ⟨746931899725864709636161, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 995909199634486279514881 746931899725864709636161)
            ·
              refine ⟨560198924794398532227121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 746931899725864709636161 560198924794398532227121)
              ·
                refine ⟨420149193595798899170341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560198924794398532227121 420149193595798899170341)
                ·
                  refine ⟨78777973799212293594439, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420149193595798899170341 78777973799212293594439)
                  ·
                    rfl

theorem cell21_345194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 2, 2, 2, 2, 4].length) (baseStart_345194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345194 prefixEnd_345194 := by exact prefixLift 345194
  have htrace : WordTrace (prefixWord ++ tailWord_345194) baseStart_345194 baseEnd_345194 := by
    simpa [prefixWord, tailWord_345194, baseEnd_345194] using wordTrace_append hprefix tailTrace_345194
  have hstable : (prefixWord ++ tailWord_345194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345194).length < 2 ^ (prefixWord ++ tailWord_345194).sum := by decide
  have hdescent : baseEnd_345194 < baseStart_345194 := by decide
  rcases family_descends (prefixWord ++ tailWord_345194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345197 : List Nat := [1, 5, 1, 1, 2, 4, 2, 2, 3]
def baseStart_345197 : Nat := 118140960795 + 345197 * 2 ^ 59
def prefixEnd_345197 : Nat := 4983230072969 + 3 ^ 40 * 345197 * 2
def baseEnd_345197 : Nat := 78778658440084955044433

theorem tailTrace_345197 : CollatzResearch.WordTrace tailWord_345197 prefixEnd_345197 78778658440084955044433 := by
  unfold tailWord_345197
  simp only [CollatzResearch.WordTrace]
  refine ⟨12590368930417698799065845, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8393579286945132532710563 12590368930417698799065845)
  ·
    refine ⟨1180347087226659262412423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12590368930417698799065845 1180347087226659262412423)
    ·
      refine ⟨1770520630839988893618635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1180347087226659262412423 1770520630839988893618635)
      ·
        refine ⟨2655780946259983340427953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1770520630839988893618635 2655780946259983340427953)
        ·
          refine ⟨1991835709694987505320965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2655780946259983340427953 1991835709694987505320965)
          ·
            refine ⟨373469195567810157247681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 1991835709694987505320965 373469195567810157247681)
            ·
              refine ⟨280101896675857617935761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 373469195567810157247681 280101896675857617935761)
              ·
                refine ⟨210076422506893213451821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280101896675857617935761 210076422506893213451821)
                ·
                  refine ⟨78778658440084955044433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210076422506893213451821 78778658440084955044433)
                  ·
                    rfl

theorem cell21_345197_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 2, 4, 2, 2, 3].length) (baseStart_345197 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345197 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345197 prefixEnd_345197 := by exact prefixLift 345197
  have htrace : WordTrace (prefixWord ++ tailWord_345197) baseStart_345197 baseEnd_345197 := by
    simpa [prefixWord, tailWord_345197, baseEnd_345197] using wordTrace_append hprefix tailTrace_345197
  have hstable : (prefixWord ++ tailWord_345197).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345197).length < 2 ^ (prefixWord ++ tailWord_345197).sum := by decide
  have hdescent : baseEnd_345197 < baseStart_345197 := by decide
  rcases family_descends (prefixWord ++ tailWord_345197) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345239 : List Nat := [1, 1, 3, 3, 3, 1, 1, 5, 3]
def baseStart_345239 : Nat := 118140960795 + 345239 * 2 ^ 59
def prefixEnd_345239 : Nat := 4983230072969 + 3 ^ 40 * 345239 * 2
def baseEnd_345239 : Nat := 78788243412302215344347

theorem tailTrace_345239 : CollatzResearch.WordTrace tailWord_345239 prefixEnd_345239 78788243412302215344347 := by
  unfold tailWord_345239
  simp only [CollatzResearch.WordTrace]
  refine ⟨12591900796265539972094771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8394600530843693314729847 12591900796265539972094771)
  ·
    refine ⟨18887851194398309958142157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12591900796265539972094771 18887851194398309958142157)
    ·
      refine ⟨7082944197899366234303309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18887851194398309958142157 7082944197899366234303309)
      ·
        refine ⟨2656104074212262337863741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7082944197899366234303309 2656104074212262337863741)
        ·
          refine ⟨996039027829598376698903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2656104074212262337863741 996039027829598376698903)
          ·
            refine ⟨1494058541744397565048355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 996039027829598376698903 1494058541744397565048355)
            ·
              refine ⟨2241087812616596347572533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1494058541744397565048355 2241087812616596347572533)
              ·
                refine ⟨210101982432805907584925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2241087812616596347572533 210101982432805907584925)
                ·
                  refine ⟨78788243412302215344347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210101982432805907584925 78788243412302215344347)
                  ·
                    rfl

theorem cell21_345239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 1, 1, 5, 3].length) (baseStart_345239 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345239 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345239 prefixEnd_345239 := by exact prefixLift 345239
  have htrace : WordTrace (prefixWord ++ tailWord_345239) baseStart_345239 baseEnd_345239 := by
    simpa [prefixWord, tailWord_345239, baseEnd_345239] using wordTrace_append hprefix tailTrace_345239
  have hstable : (prefixWord ++ tailWord_345239).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345239).length < 2 ^ (prefixWord ++ tailWord_345239).sum := by decide
  have hdescent : baseEnd_345239 < baseStart_345239 := by decide
  rcases family_descends (prefixWord ++ tailWord_345239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345253 : List Nat := [1, 3, 1, 2, 1, 4, 3, 2, 4]
def baseStart_345253 : Nat := 118140960795 + 345253 * 2 ^ 59
def prefixEnd_345253 : Nat := 4983230072969 + 3 ^ 40 * 345253 * 2
def baseEnd_345253 : Nat := 78791438403041302110985

theorem tailTrace_345253 : CollatzResearch.WordTrace tailWord_345253 prefixEnd_345253 78791438403041302110985 := by
  unfold tailWord_345253
  simp only [CollatzResearch.WordTrace]
  refine ⟨12592411418214820363104413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8394940945476546908736275 12592411418214820363104413)
  ·
    refine ⟨4722154281830557636164155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12592411418214820363104413 4722154281830557636164155)
    ·
      refine ⟨7083231422745836454246233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4722154281830557636164155 7083231422745836454246233)
      ·
        refine ⟨5312423567059377340684675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7083231422745836454246233 5312423567059377340684675)
        ·
          refine ⟨7968635350589066011027013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5312423567059377340684675 7968635350589066011027013)
          ·
            refine ⟨1494119128235449877067565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7968635350589066011027013 1494119128235449877067565)
            ·
              refine ⟨560294673088293703900337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1494119128235449877067565 560294673088293703900337)
              ·
                refine ⟨420221004816220277925253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 560294673088293703900337 420221004816220277925253)
                ·
                  refine ⟨78791438403041302110985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 420221004816220277925253 78791438403041302110985)
                  ·
                    rfl

theorem cell21_345253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 4, 3, 2, 4].length) (baseStart_345253 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345253 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345253 prefixEnd_345253 := by exact prefixLift 345253
  have htrace : WordTrace (prefixWord ++ tailWord_345253) baseStart_345253 baseEnd_345253 := by
    simpa [prefixWord, tailWord_345253, baseEnd_345253] using wordTrace_append hprefix tailTrace_345253
  have hstable : (prefixWord ++ tailWord_345253).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345253).length < 2 ^ (prefixWord ++ tailWord_345253).sum := by decide
  have hdescent : baseEnd_345253 < baseStart_345253 := by decide
  rcases family_descends (prefixWord ++ tailWord_345253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345284 : List Nat := [2, 3, 3, 1, 3, 1, 1, 7]
def baseStart_345284 : Nat := 118140960795 + 345284 * 2 ^ 59
def prefixEnd_345284 : Nat := 4983230072969 + 3 ^ 40 * 345284 * 2
def baseEnd_345284 : Nat := 26266171008464045698085

theorem tailTrace_345284 : CollatzResearch.WordTrace tailWord_345284 prefixEnd_345284 26266171008464045698085 := by
  unfold tailWord_345284
  simp only [CollatzResearch.WordTrace]
  refine ⟨6296771040551256328741453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8395694720735008438321937 6296771040551256328741453)
  ·
    refine ⟨2361289140206721123278045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6296771040551256328741453 2361289140206721123278045)
    ·
      refine ⟨885483427577520421229267, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2361289140206721123278045 885483427577520421229267)
      ·
        refine ⟨1328225141366280631843901, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 885483427577520421229267 1328225141366280631843901)
        ·
          refine ⟨498084428012355236941463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1328225141366280631843901 498084428012355236941463)
          ·
            refine ⟨747126642018532855412195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 498084428012355236941463 747126642018532855412195)
            ·
              refine ⟨1120689963027799283118293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 747126642018532855412195 1120689963027799283118293)
              ·
                refine ⟨26266171008464045698085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1120689963027799283118293 26266171008464045698085)
                ·
                  rfl

theorem cell21_345284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 7].length) (baseStart_345284 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345284 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345284 prefixEnd_345284 := by exact prefixLift 345284
  have htrace : WordTrace (prefixWord ++ tailWord_345284) baseStart_345284 baseEnd_345284 := by
    simpa [prefixWord, tailWord_345284, baseEnd_345284] using wordTrace_append hprefix tailTrace_345284
  have hstable : (prefixWord ++ tailWord_345284).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345284).length < 2 ^ (prefixWord ++ tailWord_345284).sum := by decide
  have hdescent : baseEnd_345284 < baseStart_345284 := by decide
  rcases family_descends (prefixWord ++ tailWord_345284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345312 : List Nat := [2, 1, 1, 3, 1, 4, 2, 1, 6]
def baseStart_345312 : Nat := 118140960795 + 345312 * 2 ^ 59
def prefixEnd_345312 : Nat := 4983230072969 + 3 ^ 40 * 345312 * 2
def baseEnd_345312 : Nat := 78804903006870310627531

theorem tailTrace_345312 : CollatzResearch.WordTrace tailWord_345312 prefixEnd_345312 78804903006870310627531 := by
  unfold tailWord_345312
  simp only [CollatzResearch.WordTrace]
  refine ⟨6297281662500536719751095, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8396375550000715626334793 6297281662500536719751095)
  ·
    refine ⟨9445922493750805079626643, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6297281662500536719751095 9445922493750805079626643)
    ·
      refine ⟨14168883740626207619439965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9445922493750805079626643 14168883740626207619439965)
      ·
        refine ⟨5313331402734827857289987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14168883740626207619439965 5313331402734827857289987)
        ·
          refine ⟨7969997104102241785934981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5313331402734827857289987 7969997104102241785934981)
          ·
            refine ⟨1494374457019170334862809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 7969997104102241785934981 1494374457019170334862809)
            ·
              refine ⟨1120780842764377751147107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1494374457019170334862809 1120780842764377751147107)
              ·
                refine ⟨1681171264146566626720661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1120780842764377751147107 1681171264146566626720661)
                ·
                  refine ⟨78804903006870310627531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1681171264146566626720661 78804903006870310627531)
                  ·
                    rfl

theorem cell21_345312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 4, 2, 1, 6].length) (baseStart_345312 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345312 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345312 prefixEnd_345312 := by exact prefixLift 345312
  have htrace : WordTrace (prefixWord ++ tailWord_345312) baseStart_345312 baseEnd_345312 := by
    simpa [prefixWord, tailWord_345312, baseEnd_345312] using wordTrace_append hprefix tailTrace_345312
  have hstable : (prefixWord ++ tailWord_345312).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345312).length < 2 ^ (prefixWord ++ tailWord_345312).sum := by decide
  have hdescent : baseEnd_345312 < baseStart_345312 := by decide
  rcases family_descends (prefixWord ++ tailWord_345312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345433 : List Nat := [1, 2, 1, 2, 2, 2, 3, 3, 5]
def baseStart_345433 : Nat := 118140960795 + 345433 * 2 ^ 59
def prefixEnd_345433 : Nat := 4983230072969 + 3 ^ 40 * 345433 * 2
def baseEnd_345433 : Nat := 78832516855400989110617

theorem tailTrace_345433 : CollatzResearch.WordTrace tailWord_345433 prefixEnd_345433 78832516855400989110617 := by
  unfold tailWord_345433
  simp only [CollatzResearch.WordTrace]
  refine ⟨12598976557562711104656953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8399317705041807403104635 12598976557562711104656953)
  ·
    refine ⟨9449232418172033328492715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12598976557562711104656953 9449232418172033328492715)
    ·
      refine ⟨14173848627258049992739073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9449232418172033328492715 14173848627258049992739073)
      ·
        refine ⟨10630386470443537494554305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14173848627258049992739073 10630386470443537494554305)
        ·
          refine ⟨7972789852832653120915729, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10630386470443537494554305 7972789852832653120915729)
          ·
            refine ⟨5979592389624489840686797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 7972789852832653120915729 5979592389624489840686797)
            ·
              refine ⟨2242347146109183690257549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 5979592389624489840686797 2242347146109183690257549)
              ·
                refine ⟨840880179790943883846581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2242347146109183690257549 840880179790943883846581)
                ·
                  refine ⟨78832516855400989110617, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 840880179790943883846581 78832516855400989110617)
                  ·
                    rfl

theorem cell21_345433_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 3, 3, 5].length) (baseStart_345433 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345433 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345433 prefixEnd_345433 := by exact prefixLift 345433
  have htrace : WordTrace (prefixWord ++ tailWord_345433) baseStart_345433 baseEnd_345433 := by
    simpa [prefixWord, tailWord_345433, baseEnd_345433] using wordTrace_append hprefix tailTrace_345433
  have hstable : (prefixWord ++ tailWord_345433).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345433).length < 2 ^ (prefixWord ++ tailWord_345433).sum := by decide
  have hdescent : baseEnd_345433 < baseStart_345433 := by decide
  rcases family_descends (prefixWord ++ tailWord_345433) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345470 : List Nat := [4, 2, 3, 2, 2, 1, 7]
def baseStart_345470 : Nat := 118140960795 + 345470 * 2 ^ 59
def prefixEnd_345470 : Nat := 4983230072969 + 3 ^ 40 * 345470 * 2
def baseEnd_345470 : Nat := 8760106751055238554875

theorem tailTrace_345470 : CollatzResearch.WordTrace tailWord_345470 prefixEnd_345470 8760106751055238554875 := by
  unfold tailWord_345470
  simp only [CollatzResearch.WordTrace]
  refine ⟨1575040757303583302969233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8400217372285777615835909 1575040757303583302969233)
  ·
    refine ⟨1181280567977687477226925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1575040757303583302969233 1181280567977687477226925)
    ·
      refine ⟨442980212991632803960097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 1181280567977687477226925 442980212991632803960097)
      ·
        refine ⟨332235159743724602970073, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 442980212991632803960097 332235159743724602970073)
        ·
          refine ⟨249176369807793452227555, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 332235159743724602970073 249176369807793452227555)
          ·
            refine ⟨373764554711690178341333, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 249176369807793452227555 373764554711690178341333)
            ·
              refine ⟨8760106751055238554875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 373764554711690178341333 8760106751055238554875)
              ·
                rfl

theorem cell21_345470_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 2, 2, 1, 7].length) (baseStart_345470 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345470 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345470 prefixEnd_345470 := by exact prefixLift 345470
  have htrace : WordTrace (prefixWord ++ tailWord_345470) baseStart_345470 baseEnd_345470 := by
    simpa [prefixWord, tailWord_345470, baseEnd_345470] using wordTrace_append hprefix tailTrace_345470
  have hstable : (prefixWord ++ tailWord_345470).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345470).length < 2 ^ (prefixWord ++ tailWord_345470).sum := by decide
  have hdescent : baseEnd_345470 < baseStart_345470 := by decide
  rcases family_descends (prefixWord ++ tailWord_345470) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345523 : List Nat := [1, 1, 1, 2, 3, 1, 1, 3, 8]
def baseStart_345523 : Nat := 118140960795 + 345523 * 2 ^ 59
def prefixEnd_345523 : Nat := 4983230072969 + 3 ^ 40 * 345523 * 2
def baseEnd_345523 : Nat := 78853056081580832610433

theorem tailTrace_345523 : CollatzResearch.WordTrace tailWord_345523 prefixEnd_345523 78853056081580832610433 := by
  unfold tailWord_345523
  simp only [CollatzResearch.WordTrace]
  refine ⟨12602259127236656475433223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8401506084824437650288815 12602259127236656475433223)
  ·
    refine ⟨18903388690854984713149835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12602259127236656475433223 18903388690854984713149835)
    ·
      refine ⟨28355083036282477069724753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18903388690854984713149835 28355083036282477069724753)
      ·
        refine ⟨21266312277211857802293565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28355083036282477069724753 21266312277211857802293565)
        ·
          refine ⟨7974867103954446675860087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21266312277211857802293565 7974867103954446675860087)
          ·
            refine ⟨11962300655931670013790131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 7974867103954446675860087 11962300655931670013790131)
            ·
              refine ⟨17943450983897505020685197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 11962300655931670013790131 17943450983897505020685197)
              ·
                refine ⟨6728794118961564382756949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 17943450983897505020685197 6728794118961564382756949)
                ·
                  refine ⟨78853056081580832610433, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6728794118961564382756949 78853056081580832610433)
                  ·
                    rfl

theorem cell21_345523_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 1, 3, 8].length) (baseStart_345523 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345523 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345523 prefixEnd_345523 := by exact prefixLift 345523
  have htrace : WordTrace (prefixWord ++ tailWord_345523) baseStart_345523 baseEnd_345523 := by
    simpa [prefixWord, tailWord_345523, baseEnd_345523] using wordTrace_append hprefix tailTrace_345523
  have hstable : (prefixWord ++ tailWord_345523).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345523).length < 2 ^ (prefixWord ++ tailWord_345523).sum := by decide
  have hdescent : baseEnd_345523 < baseStart_345523 := by decide
  rcases family_descends (prefixWord ++ tailWord_345523) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345706 : List Nat := [3, 1, 3, 2, 1, 11]
def baseStart_345706 : Nat := 118140960795 + 345706 * 2 ^ 59
def prefixEnd_345706 : Nat := 4983230072969 + 3 ^ 40 * 345706 * 2
def baseEnd_345706 : Nat := 2922030339807895594817

theorem tailTrace_345706 : CollatzResearch.WordTrace tailWord_345706 prefixEnd_345706 2922030339807895594817 := by
  unfold tailWord_345706
  simp only [CollatzResearch.WordTrace]
  refine ⟨3152233421393419682336243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8405955790382452486229981 3152233421393419682336243)
  ·
    refine ⟨4728350132090129523504365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3152233421393419682336243 4728350132090129523504365)
    ·
      refine ⟨1773131299533798571314137, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4728350132090129523504365 1773131299533798571314137)
      ·
        refine ⟨1329848474650348928485603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1773131299533798571314137 1329848474650348928485603)
        ·
          refine ⟨1994772711975523392728405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1329848474650348928485603 1994772711975523392728405)
          ·
            refine ⟨2922030339807895594817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 11 1994772711975523392728405 2922030339807895594817)
            ·
              rfl

theorem cell21_345706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 11].length) (baseStart_345706 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345706 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345706 prefixEnd_345706 := by exact prefixLift 345706
  have htrace : WordTrace (prefixWord ++ tailWord_345706) baseStart_345706 baseEnd_345706 := by
    simpa [prefixWord, tailWord_345706, baseEnd_345706] using wordTrace_append hprefix tailTrace_345706
  have hstable : (prefixWord ++ tailWord_345706).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345706).length < 2 ^ (prefixWord ++ tailWord_345706).sum := by decide
  have hdescent : baseEnd_345706 < baseStart_345706 := by decide
  rcases family_descends (prefixWord ++ tailWord_345706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345712 : List Nat := [2, 1, 1, 1, 6, 3, 2, 2, 3]
def baseStart_345712 : Nat := 118140960795 + 345712 * 2 ^ 59
def prefixEnd_345712 : Nat := 4983230072969 + 3 ^ 40 * 345712 * 2
def baseEnd_345712 : Nat := 78896188456558503960047

theorem tailTrace_345712 : CollatzResearch.WordTrace tailWord_345712 prefixEnd_345712 78896188456558503960047 := by
  unfold tailWord_345712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6304576261775970877031695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8406101682367961169375593 6304576261775970877031695)
  ·
    refine ⟨9456864392663956315547543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6304576261775970877031695 9456864392663956315547543)
    ·
      refine ⟨14185296588995934473321315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9456864392663956315547543 14185296588995934473321315)
      ·
        refine ⟨21277944883493901709981973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14185296588995934473321315 21277944883493901709981973)
        ·
          refine ⟨997403666413776642655405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 21277944883493901709981973 997403666413776642655405)
          ·
            refine ⟨374026374905166240995777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 997403666413776642655405 374026374905166240995777)
            ·
              refine ⟨280519781178874680746833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 374026374905166240995777 280519781178874680746833)
              ·
                refine ⟨210389835884156010560125, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 280519781178874680746833 210389835884156010560125)
                ·
                  refine ⟨78896188456558503960047, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210389835884156010560125 78896188456558503960047)
                  ·
                    rfl

theorem cell21_345712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 6, 3, 2, 2, 3].length) (baseStart_345712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345712 prefixEnd_345712 := by exact prefixLift 345712
  have htrace : WordTrace (prefixWord ++ tailWord_345712) baseStart_345712 baseEnd_345712 := by
    simpa [prefixWord, tailWord_345712, baseEnd_345712] using wordTrace_append hprefix tailTrace_345712
  have hstable : (prefixWord ++ tailWord_345712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345712).length < 2 ^ (prefixWord ++ tailWord_345712).sum := by decide
  have hdescent : baseEnd_345712 < baseStart_345712 := by decide
  rcases family_descends (prefixWord ++ tailWord_345712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345805 : List Nat := [1, 6, 2, 1, 1, 3, 1, 3, 3]
def baseStart_345805 : Nat := 118140960795 + 345805 * 2 ^ 59
def prefixEnd_345805 : Nat := 4983230072969 + 3 ^ 40 * 345805 * 2
def baseEnd_345805 : Nat := 78917412323611008909857

theorem tailTrace_345805 : CollatzResearch.WordTrace tailWord_345805 prefixEnd_345805 78917412323611008909857 := by
  unfold tailWord_345805
  simp only [CollatzResearch.WordTrace]
  refine ⟨12612544512215018637198869, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8408363008143345758132579 12612544512215018637198869)
  ·
    refine ⟨591213024010078998618697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 12612544512215018637198869 591213024010078998618697)
    ·
      refine ⟨443409768007559248964023, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 591213024010078998618697 443409768007559248964023)
      ·
        refine ⟨665114652011338873446035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 443409768007559248964023 665114652011338873446035)
        ·
          refine ⟨997671978017008310169053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 665114652011338873446035 997671978017008310169053)
          ·
            refine ⟨374126991756378116313395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 997671978017008310169053 374126991756378116313395)
            ·
              refine ⟨561190487634567174470093, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374126991756378116313395 561190487634567174470093)
              ·
                refine ⟨210446432862962690426285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 561190487634567174470093 210446432862962690426285)
                ·
                  refine ⟨78917412323611008909857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210446432862962690426285 78917412323611008909857)
                  ·
                    rfl

theorem cell21_345805_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 2, 1, 1, 3, 1, 3, 3].length) (baseStart_345805 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345805 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345805 prefixEnd_345805 := by exact prefixLift 345805
  have htrace : WordTrace (prefixWord ++ tailWord_345805) baseStart_345805 baseEnd_345805 := by
    simpa [prefixWord, tailWord_345805, baseEnd_345805] using wordTrace_append hprefix tailTrace_345805
  have hstable : (prefixWord ++ tailWord_345805).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345805).length < 2 ^ (prefixWord ++ tailWord_345805).sum := by decide
  have hdescent : baseEnd_345805 < baseStart_345805 := by decide
  rcases family_descends (prefixWord ++ tailWord_345805) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345937 : List Nat := [1, 2, 2, 1, 5, 3, 1, 2, 4]
def baseStart_345937 : Nat := 118140960795 + 345937 * 2 ^ 59
def prefixEnd_345937 : Nat := 4983230072969 + 3 ^ 40 * 345937 * 2
def baseEnd_345937 : Nat := 78947536522008112709587

theorem tailTrace_345937 : CollatzResearch.WordTrace tailWord_345937 prefixEnd_345937 78947536522008112709587 := by
  unfold tailWord_345937
  simp only [CollatzResearch.WordTrace]
  refine ⟨12617358947736805181004065, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8411572631824536787336043 12617358947736805181004065)
  ·
    refine ⟨9463019210802603885753049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12617358947736805181004065 9463019210802603885753049)
    ·
      refine ⟨7097264408101952914314787, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9463019210802603885753049 7097264408101952914314787)
      ·
        refine ⟨10645896612152929371472181, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7097264408101952914314787 10645896612152929371472181)
        ·
          refine ⟨998052807389337128575517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10645896612152929371472181 998052807389337128575517)
          ·
            refine ⟨374269802771001423215819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 998052807389337128575517 374269802771001423215819)
            ·
              refine ⟨561404704156502134823729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 374269802771001423215819 561404704156502134823729)
              ·
                refine ⟨421053528117376601117797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561404704156502134823729 421053528117376601117797)
                ·
                  refine ⟨78947536522008112709587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421053528117376601117797 78947536522008112709587)
                  ·
                    rfl

theorem cell21_345937_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 5, 3, 1, 2, 4].length) (baseStart_345937 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345937 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345937 prefixEnd_345937 := by exact prefixLift 345937
  have htrace : WordTrace (prefixWord ++ tailWord_345937) baseStart_345937 baseEnd_345937 := by
    simpa [prefixWord, tailWord_345937, baseEnd_345937] using wordTrace_append hprefix tailTrace_345937
  have hstable : (prefixWord ++ tailWord_345937).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345937).length < 2 ^ (prefixWord ++ tailWord_345937).sum := by decide
  have hdescent : baseEnd_345937 < baseStart_345937 := by decide
  rcases family_descends (prefixWord ++ tailWord_345937) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345954 : List Nat := [3, 3, 2, 1, 2, 2, 3, 1, 4]
def baseStart_345954 : Nat := 118140960795 + 345954 * 2 ^ 59
def prefixEnd_345954 : Nat := 4983230072969 + 3 ^ 40 * 345954 * 2
def baseEnd_345954 : Nat := 78951416153619860926219

theorem tailTrace_345954 : CollatzResearch.WordTrace tailWord_345954 prefixEnd_345954 78951416153619860926219 := by
  unfold tailWord_345954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3154494747168804271093229, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8411985992450144722915277 3154494747168804271093229)
  ·
    refine ⟨1182935530188301601659961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3154494747168804271093229 1182935530188301601659961)
    ·
      refine ⟨887201647641226201244971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1182935530188301601659961 887201647641226201244971)
      ·
        refine ⟨1330802471461839301867457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 887201647641226201244971 1330802471461839301867457)
        ·
          refine ⟨998101853596379476400593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1330802471461839301867457 998101853596379476400593)
          ·
            refine ⟨748576390197284607300445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 998101853596379476400593 748576390197284607300445)
            ·
              refine ⟨280716146323981727737667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 748576390197284607300445 280716146323981727737667)
              ·
                refine ⟨421074219485972591606501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280716146323981727737667 421074219485972591606501)
                ·
                  refine ⟨78951416153619860926219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421074219485972591606501 78951416153619860926219)
                  ·
                    rfl

theorem cell21_345954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_345954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345954 prefixEnd_345954 := by exact prefixLift 345954
  have htrace : WordTrace (prefixWord ++ tailWord_345954) baseStart_345954 baseEnd_345954 := by
    simpa [prefixWord, tailWord_345954, baseEnd_345954] using wordTrace_append hprefix tailTrace_345954
  have hstable : (prefixWord ++ tailWord_345954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345954).length < 2 ^ (prefixWord ++ tailWord_345954).sum := by decide
  have hdescent : baseEnd_345954 < baseStart_345954 := by decide
  rcases family_descends (prefixWord ++ tailWord_345954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_345965 : List Nat := [1, 5, 1, 1, 1, 1, 4, 2, 5]
def baseStart_345965 : Nat := 118140960795 + 345965 * 2 ^ 59
def prefixEnd_345965 : Nat := 4983230072969 + 3 ^ 40 * 345965 * 2
def baseEnd_345965 : Nat := 78953926503486286242863

theorem tailTrace_345965 : CollatzResearch.WordTrace tailWord_345965 prefixEnd_345965 78953926503486286242863 := by
  unfold tailWord_345965
  simp only [CollatzResearch.WordTrace]
  refine ⟨12618380191635365963023349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8412253461090243975348899 12618380191635365963023349)
  ·
    refine ⟨1182973142965815559033439, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12618380191635365963023349 1182973142965815559033439)
    ·
      refine ⟨1774459714448723338550159, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1182973142965815559033439 1774459714448723338550159)
      ·
        refine ⟨2661689571673085007825239, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774459714448723338550159 2661689571673085007825239)
        ·
          refine ⟨3992534357509627511737859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2661689571673085007825239 3992534357509627511737859)
          ·
            refine ⟨5988801536264441267606789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 3992534357509627511737859 5988801536264441267606789)
            ·
              refine ⟨1122900288049582737676273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 5988801536264441267606789 1122900288049582737676273)
              ·
                refine ⟨842175216037187053257205, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1122900288049582737676273 842175216037187053257205)
                ·
                  refine ⟨78953926503486286242863, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 842175216037187053257205 78953926503486286242863)
                  ·
                    rfl

theorem cell21_345965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 1, 4, 2, 5].length) (baseStart_345965 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_345965 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_345965 prefixEnd_345965 := by exact prefixLift 345965
  have htrace : WordTrace (prefixWord ++ tailWord_345965) baseStart_345965 baseEnd_345965 := by
    simpa [prefixWord, tailWord_345965, baseEnd_345965] using wordTrace_append hprefix tailTrace_345965
  have hstable : (prefixWord ++ tailWord_345965).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_345965).length < 2 ^ (prefixWord ++ tailWord_345965).sum := by decide
  have hdescent : baseEnd_345965 < baseStart_345965 := by decide
  rcases family_descends (prefixWord ++ tailWord_345965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346010 : List Nat := [3, 1, 1, 4, 2, 1, 1, 8]
def baseStart_346010 : Nat := 118140960795 + 346010 * 2 ^ 59
def prefixEnd_346010 : Nat := 4983230072969 + 3 ^ 40 * 346010 * 2
def baseEnd_346010 : Nat := 26321398705525402664257

theorem tailTrace_346010 : CollatzResearch.WordTrace tailWord_346010 prefixEnd_346010 26321398705525402664257 := by
  unfold tailWord_346010
  simp only [CollatzResearch.WordTrace]
  refine ⟨3155005369118084662102871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8413347650981559098940989 3155005369118084662102871)
  ·
    refine ⟨4732508053677126993154307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3155005369118084662102871 4732508053677126993154307)
    ·
      refine ⟨7098762080515690489731461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4732508053677126993154307 7098762080515690489731461)
      ·
        refine ⟨1331017890096691966824649, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 7098762080515690489731461 1331017890096691966824649)
        ·
          refine ⟨998263417572518975118487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1331017890096691966824649 998263417572518975118487)
          ·
            refine ⟨1497395126358778462677731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 998263417572518975118487 1497395126358778462677731)
            ·
              refine ⟨2246092689538167694016597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1497395126358778462677731 2246092689538167694016597)
              ·
                refine ⟨26321398705525402664257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2246092689538167694016597 26321398705525402664257)
                ·
                  rfl

theorem cell21_346010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 1, 8].length) (baseStart_346010 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346010 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346010 prefixEnd_346010 := by exact prefixLift 346010
  have htrace : WordTrace (prefixWord ++ tailWord_346010) baseStart_346010 baseEnd_346010 := by
    simpa [prefixWord, tailWord_346010, baseEnd_346010] using wordTrace_append hprefix tailTrace_346010
  have hstable : (prefixWord ++ tailWord_346010).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346010).length < 2 ^ (prefixWord ++ tailWord_346010).sum := by decide
  have hdescent : baseEnd_346010 < baseStart_346010 := by decide
  rcases family_descends (prefixWord ++ tailWord_346010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346013 : List Nat := [1, 4, 2, 1, 2, 2, 4, 1, 4]
def baseStart_346013 : Nat := 118140960795 + 346013 * 2 ^ 59
def prefixEnd_346013 : Nat := 4983230072969 + 3 ^ 40 * 346013 * 2
def baseEnd_346013 : Nat := 78964880757448869442765

theorem tailTrace_346013 : CollatzResearch.WordTrace tailWord_346013 prefixEnd_346013 78964880757448869442765 := by
  unfold tailWord_346013
  simp only [CollatzResearch.WordTrace]
  refine ⟨12620130895461470160770693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8413420596974313440513795 12620130895461470160770693)
  ·
    refine ⟨2366274542899025655144505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12620130895461470160770693 2366274542899025655144505)
    ·
      refine ⟨1774705907174269241358379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2366274542899025655144505 1774705907174269241358379)
      ·
        refine ⟨2662058860761403862037569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1774705907174269241358379 2662058860761403862037569)
        ·
          refine ⟨1996544145571052896528177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2662058860761403862037569 1996544145571052896528177)
          ·
            refine ⟨1497408109178289672396133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1996544145571052896528177 1497408109178289672396133)
            ·
              refine ⟨280764020470929313574275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1497408109178289672396133 280764020470929313574275)
              ·
                refine ⟨421146030706393970361413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280764020470929313574275 421146030706393970361413)
                ·
                  refine ⟨78964880757448869442765, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421146030706393970361413 78964880757448869442765)
                  ·
                    rfl

theorem cell21_346013_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 4, 1, 4].length) (baseStart_346013 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346013 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346013 prefixEnd_346013 := by exact prefixLift 346013
  have htrace : WordTrace (prefixWord ++ tailWord_346013) baseStart_346013 baseEnd_346013 := by
    simpa [prefixWord, tailWord_346013, baseEnd_346013] using wordTrace_append hprefix tailTrace_346013
  have hstable : (prefixWord ++ tailWord_346013).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346013).length < 2 ^ (prefixWord ++ tailWord_346013).sum := by decide
  have hdescent : baseEnd_346013 < baseStart_346013 := by decide
  rcases family_descends (prefixWord ++ tailWord_346013) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346117 : List Nat := [1, 3, 1, 1, 2, 5, 2, 1, 5]
def baseStart_346117 : Nat := 118140960795 + 346117 * 2 ^ 59
def prefixEnd_346117 : Nat := 4983230072969 + 3 ^ 40 * 346117 * 2
def baseEnd_346117 : Nat := 78988614974367799709219

theorem tailTrace_346117 : CollatzResearch.WordTrace tailWord_346117 prefixEnd_346117 78988614974367799709219 := by
  unfold tailWord_346117
  simp only [CollatzResearch.WordTrace]
  refine ⟨12623924087084695922556605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8415949391389797281704403 12623924087084695922556605)
  ·
    refine ⟨4733971532656760970958727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12623924087084695922556605 4733971532656760970958727)
    ·
      refine ⟨7100957298985141456438091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4733971532656760970958727 7100957298985141456438091)
      ·
        refine ⟨10651435948477712184657137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7100957298985141456438091 10651435948477712184657137)
        ·
          refine ⟨7988576961358284138492853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10651435948477712184657137 7988576961358284138492853)
          ·
            refine ⟨748929090127339137983705, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 7988576961358284138492853 748929090127339137983705)
            ·
              refine ⟨561696817595504353487779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 748929090127339137983705 561696817595504353487779)
              ·
                refine ⟨842545226393256530231669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 561696817595504353487779 842545226393256530231669)
                ·
                  refine ⟨78988614974367799709219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 842545226393256530231669 78988614974367799709219)
                  ·
                    rfl

theorem cell21_346117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 5, 2, 1, 5].length) (baseStart_346117 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346117 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346117 prefixEnd_346117 := by exact prefixLift 346117
  have htrace : WordTrace (prefixWord ++ tailWord_346117) baseStart_346117 baseEnd_346117 := by
    simpa [prefixWord, tailWord_346117, baseEnd_346117] using wordTrace_append hprefix tailTrace_346117
  have hstable : (prefixWord ++ tailWord_346117).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346117).length < 2 ^ (prefixWord ++ tailWord_346117).sum := by decide
  have hdescent : baseEnd_346117 < baseStart_346117 := by decide
  rcases family_descends (prefixWord ++ tailWord_346117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346131 : List Nat := [1, 1, 1, 2, 1, 4, 2, 5, 4]
def baseStart_346131 : Nat := 118140960795 + 346131 * 2 ^ 59
def prefixEnd_346131 : Nat := 4983230072969 + 3 ^ 40 * 346131 * 2
def baseEnd_346131 : Nat := 78991809965106886475857

theorem tailTrace_346131 : CollatzResearch.WordTrace tailWord_346131 prefixEnd_346131 78991809965106886475857 := by
  unfold tailWord_346131
  simp only [CollatzResearch.WordTrace]
  refine ⟨12624434709033976313566247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8416289806022650875710831 12624434709033976313566247)
  ·
    refine ⟨18936652063550964470349371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12624434709033976313566247 18936652063550964470349371)
    ·
      refine ⟨28404978095326446705524057, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18936652063550964470349371 28404978095326446705524057)
      ·
        refine ⟨21303733571494835029143043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28404978095326446705524057 21303733571494835029143043)
        ·
          refine ⟨31955600357242252543714565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21303733571494835029143043 31955600357242252543714565)
          ·
            refine ⟨5991675066982922351946481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 31955600357242252543714565 5991675066982922351946481)
            ·
              refine ⟨4493756300237191763959861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 5991675066982922351946481 4493756300237191763959861)
              ·
                refine ⟨421289653147236727871237, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4493756300237191763959861 421289653147236727871237)
                ·
                  refine ⟨78991809965106886475857, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421289653147236727871237 78991809965106886475857)
                  ·
                    rfl

theorem cell21_346131_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 4, 2, 5, 4].length) (baseStart_346131 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346131 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346131 prefixEnd_346131 := by exact prefixLift 346131
  have htrace : WordTrace (prefixWord ++ tailWord_346131) baseStart_346131 baseEnd_346131 := by
    simpa [prefixWord, tailWord_346131, baseEnd_346131] using wordTrace_append hprefix tailTrace_346131
  have hstable : (prefixWord ++ tailWord_346131).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346131).length < 2 ^ (prefixWord ++ tailWord_346131).sum := by decide
  have hdescent : baseEnd_346131 < baseStart_346131 := by decide
  rcases family_descends (prefixWord ++ tailWord_346131) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346162 : List Nat := [3, 2, 1, 1, 2, 5, 7]
def baseStart_346162 : Nat := 118140960795 + 346162 * 2 ^ 59
def prefixEnd_346162 : Nat := 4983230072969 + 3 ^ 40 * 346162 * 2
def baseEnd_346162 : Nat := 8777653843050857939903

theorem tailTrace_346162 : CollatzResearch.WordTrace tailWord_346162 prefixEnd_346162 8777653843050857939903 := by
  unfold tailWord_346162
  simp only [CollatzResearch.WordTrace]
  refine ⟨3156391342980417151986185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8417043581281112405296493 3156391342980417151986185)
  ·
    refine ⟨2367293507235312863989639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3156391342980417151986185 2367293507235312863989639)
    ·
      refine ⟨3550940260852969295984459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2367293507235312863989639 3550940260852969295984459)
      ·
        refine ⟨5326410391279453943976689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3550940260852969295984459 5326410391279453943976689)
        ·
          refine ⟨3994807793459590457982517, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5326410391279453943976689 3994807793459590457982517)
          ·
            refine ⟨374513230636836605435861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 3994807793459590457982517 374513230636836605435861)
            ·
              refine ⟨8777653843050857939903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 374513230636836605435861 8777653843050857939903)
              ·
                rfl

theorem cell21_346162_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 5, 7].length) (baseStart_346162 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346162 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346162 prefixEnd_346162 := by exact prefixLift 346162
  have htrace : WordTrace (prefixWord ++ tailWord_346162) baseStart_346162 baseEnd_346162 := by
    simpa [prefixWord, tailWord_346162, baseEnd_346162] using wordTrace_append hprefix tailTrace_346162
  have hstable : (prefixWord ++ tailWord_346162).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346162).length < 2 ^ (prefixWord ++ tailWord_346162).sum := by decide
  have hdescent : baseEnd_346162 < baseStart_346162 := by decide
  rcases family_descends (prefixWord ++ tailWord_346162) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346224 : List Nat := [2, 1, 1, 1, 5, 3, 2, 2, 4]
def baseStart_346224 : Nat := 118140960795 + 346224 * 2 ^ 59
def prefixEnd_346224 : Nat := 4983230072969 + 3 ^ 40 * 346224 * 2
def baseEnd_346224 : Nat := 79013033832159391425667

theorem tailTrace_346224 : CollatzResearch.WordTrace tailWord_346224 prefixEnd_346224 79013033832159391425667 := by
  unfold tailWord_346224
  simp only [CollatzResearch.WordTrace]
  refine ⟨6313913348848526598350863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8418551131798035464467817 6313913348848526598350863)
  ·
    refine ⟨9470870023272789897526295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6313913348848526598350863 9470870023272789897526295)
    ·
      refine ⟨14206305034909184846289443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9470870023272789897526295 14206305034909184846289443)
      ·
        refine ⟨21309457552363777269434165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14206305034909184846289443 21309457552363777269434165)
        ·
          refine ⟨1997761645534104119009453, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 21309457552363777269434165 1997761645534104119009453)
          ·
            refine ⟨749160617075289044628545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1997761645534104119009453 749160617075289044628545)
            ·
              refine ⟨561870462806466783471409, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 749160617075289044628545 561870462806466783471409)
              ·
                refine ⟨421402847104850087603557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 561870462806466783471409 421402847104850087603557)
                ·
                  refine ⟨79013033832159391425667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421402847104850087603557 79013033832159391425667)
                  ·
                    rfl

theorem cell21_346224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 5, 3, 2, 2, 4].length) (baseStart_346224 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346224 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346224 prefixEnd_346224 := by exact prefixLift 346224
  have htrace : WordTrace (prefixWord ++ tailWord_346224) baseStart_346224 baseEnd_346224 := by
    simpa [prefixWord, tailWord_346224, baseEnd_346224] using wordTrace_append hprefix tailTrace_346224
  have hstable : (prefixWord ++ tailWord_346224).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346224).length < 2 ^ (prefixWord ++ tailWord_346224).sum := by decide
  have hdescent : baseEnd_346224 < baseStart_346224 := by decide
  rcases family_descends (prefixWord ++ tailWord_346224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346292 : List Nat := [2, 5, 3, 1, 1, 1, 3, 1, 4]
def baseStart_346292 : Nat := 118140960795 + 346292 * 2 ^ 59
def prefixEnd_346292 : Nat := 4983230072969 + 3 ^ 40 * 346292 * 2
def baseEnd_346292 : Nat := 79028552358606384292195

theorem tailTrace_346292 : CollatzResearch.WordTrace tailWord_346292 prefixEnd_346292 79028552358606384292195 := by
  unfold tailWord_346292
  simp only [CollatzResearch.WordTrace]
  refine ⟨6315153430725350405088565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8420204574300467206784753 6315153430725350405088565)
  ·
    refine ⟨592045634130501600477053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 6315153430725350405088565 592045634130501600477053)
    ·
      refine ⟨222017112798938100178895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 592045634130501600477053 222017112798938100178895)
      ·
        refine ⟨333025669198407150268343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222017112798938100178895 333025669198407150268343)
        ·
          refine ⟨499538503797610725402515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 333025669198407150268343 499538503797610725402515)
          ·
            refine ⟨749307755696416088103773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 499538503797610725402515 749307755696416088103773)
            ·
              refine ⟨280990408386156033038915, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 749307755696416088103773 280990408386156033038915)
              ·
                refine ⟨421485612579234049558373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 280990408386156033038915 421485612579234049558373)
                ·
                  refine ⟨79028552358606384292195, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421485612579234049558373 79028552358606384292195)
                  ·
                    rfl

theorem cell21_346292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 3, 1, 1, 1, 3, 1, 4].length) (baseStart_346292 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346292 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346292 prefixEnd_346292 := by exact prefixLift 346292
  have htrace : WordTrace (prefixWord ++ tailWord_346292) baseStart_346292 baseEnd_346292 := by
    simpa [prefixWord, tailWord_346292, baseEnd_346292] using wordTrace_append hprefix tailTrace_346292
  have hstable : (prefixWord ++ tailWord_346292).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346292).length < 2 ^ (prefixWord ++ tailWord_346292).sum := by decide
  have hdescent : baseEnd_346292 < baseStart_346292 := by decide
  rcases family_descends (prefixWord ++ tailWord_346292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346297 : List Nat := [1, 2, 1, 4, 1, 2, 2, 8]
def baseStart_346297 : Nat := 118140960795 + 346297 * 2 ^ 59
def prefixEnd_346297 : Nat := 4983230072969 + 3 ^ 40 * 346297 * 2
def baseEnd_346297 : Nat := 26343231142242495569617

theorem tailTrace_346297 : CollatzResearch.WordTrace tailWord_346297 prefixEnd_346297 26343231142242495569617 := by
  unfold tailWord_346297
  simp only [CollatzResearch.WordTrace]
  refine ⟨12630489226432586664109145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8420326150955057776072763 12630489226432586664109145)
  ·
    refine ⟨9472866919824439998081859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12630489226432586664109145 9472866919824439998081859)
    ·
      refine ⟨14209300379736659997122789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9472866919824439998081859 14209300379736659997122789)
      ·
        refine ⟨2664243821200623749460523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14209300379736659997122789 2664243821200623749460523)
        ·
          refine ⟨3996365731800935624190785, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2664243821200623749460523 3996365731800935624190785)
          ·
            refine ⟨2997274298850701718143089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 3996365731800935624190785 2997274298850701718143089)
            ·
              refine ⟨2247955724138026288607317, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 2997274298850701718143089 2247955724138026288607317)
              ·
                refine ⟨26343231142242495569617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2247955724138026288607317 26343231142242495569617)
                ·
                  rfl

theorem cell21_346297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 2, 8].length) (baseStart_346297 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346297 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346297 prefixEnd_346297 := by exact prefixLift 346297
  have htrace : WordTrace (prefixWord ++ tailWord_346297) baseStart_346297 baseEnd_346297 := by
    simpa [prefixWord, tailWord_346297, baseEnd_346297] using wordTrace_append hprefix tailTrace_346297
  have hstable : (prefixWord ++ tailWord_346297).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346297).length < 2 ^ (prefixWord ++ tailWord_346297).sum := by decide
  have hdescent : baseEnd_346297 < baseStart_346297 := by decide
  rcases family_descends (prefixWord ++ tailWord_346297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346449 : List Nat := [1, 2, 2, 1, 4, 3, 8]
def baseStart_346449 : Nat := 118140960795 + 346449 * 2 ^ 59
def prefixEnd_346449 : Nat := 4983230072969 + 3 ^ 40 * 346449 * 2
def baseEnd_346449 : Nat := 8784931321956555575023

theorem tailTrace_346449 : CollatzResearch.WordTrace tailWord_346449 prefixEnd_346449 8784931321956555575023 := by
  unfold tailWord_346449
  simp only [CollatzResearch.WordTrace]
  refine ⟨12636033121881916623642401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8424022081254611082428267 12636033121881916623642401)
  ·
    refine ⟨9477024841411437467731801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12636033121881916623642401 9477024841411437467731801)
    ·
      refine ⟨7107768631058578100798851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9477024841411437467731801 7107768631058578100798851)
      ·
        refine ⟨10661652946587867151198277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7107768631058578100798851 10661652946587867151198277)
        ·
          refine ⟨1999059927485225090849677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10661652946587867151198277 1999059927485225090849677)
          ·
            refine ⟨749647472806959409068629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1999059927485225090849677 749647472806959409068629)
            ·
              refine ⟨8784931321956555575023, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 749647472806959409068629 8784931321956555575023)
              ·
                rfl

theorem cell21_346449_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 3, 8].length) (baseStart_346449 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346449 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346449 prefixEnd_346449 := by exact prefixLift 346449
  have htrace : WordTrace (prefixWord ++ tailWord_346449) baseStart_346449 baseEnd_346449 := by
    simpa [prefixWord, tailWord_346449, baseEnd_346449] using wordTrace_append hprefix tailTrace_346449
  have hstable : (prefixWord ++ tailWord_346449).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346449).length < 2 ^ (prefixWord ++ tailWord_346449).sum := by decide
  have hdescent : baseEnd_346449 < baseStart_346449 := by decide
  rcases family_descends (prefixWord ++ tailWord_346449) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346452 : List Nat := [2, 4, 1, 1, 2, 2, 3, 2, 4]
def baseStart_346452 : Nat := 118140960795 + 346452 * 2 ^ 59
def prefixEnd_346452 : Nat := 4983230072969 + 3 ^ 40 * 346452 * 2
def baseEnd_346452 : Nat := 79065066538481661625201

theorem tailTrace_346452 : CollatzResearch.WordTrace tailWord_346452 prefixEnd_346452 79065066538481661625201 := by
  unfold tailWord_346452
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318071270435524068000805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8424095027247365424001073 6318071270435524068000805)
  ·
    refine ⟨1184638363206660762750151, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6318071270435524068000805 1184638363206660762750151)
    ·
      refine ⟨1776957544809991144125227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1184638363206660762750151 1776957544809991144125227)
      ·
        refine ⟨2665436317214986716187841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1776957544809991144125227 2665436317214986716187841)
        ·
          refine ⟨1999077237911240037140881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2665436317214986716187841 1999077237911240037140881)
          ·
            refine ⟨1499307928433430027855661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1999077237911240037140881 1499307928433430027855661)
            ·
              refine ⟨562240473162536260445873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1499307928433430027855661 562240473162536260445873)
              ·
                refine ⟨421680354871902195334405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 562240473162536260445873 421680354871902195334405)
                ·
                  refine ⟨79065066538481661625201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421680354871902195334405 79065066538481661625201)
                  ·
                    rfl

theorem cell21_346452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 2, 2, 3, 2, 4].length) (baseStart_346452 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346452 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346452 prefixEnd_346452 := by exact prefixLift 346452
  have htrace : WordTrace (prefixWord ++ tailWord_346452) baseStart_346452 baseEnd_346452 := by
    simpa [prefixWord, tailWord_346452, baseEnd_346452] using wordTrace_append hprefix tailTrace_346452
  have hstable : (prefixWord ++ tailWord_346452).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346452).length < 2 ^ (prefixWord ++ tailWord_346452).sum := by decide
  have hdescent : baseEnd_346452 < baseStart_346452 := by decide
  rcases family_descends (prefixWord ++ tailWord_346452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346480 : List Nat := [2, 1, 1, 1, 4, 3, 2, 2, 5]
def baseStart_346480 : Nat := 118140960795 + 346480 * 2 ^ 59
def prefixEnd_346480 : Nat := 4983230072969 + 3 ^ 40 * 346480 * 2
def baseEnd_346480 : Nat := 79071456519959835158477

theorem tailTrace_346480 : CollatzResearch.WordTrace tailWord_346480 prefixEnd_346480 79071456519959835158477 := by
  unfold tailWord_346480
  simp only [CollatzResearch.WordTrace]
  refine ⟨6318581892384804459010447, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8424775856513072612013929 6318581892384804459010447)
  ·
    refine ⟨9477872838577206688515671, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6318581892384804459010447 9477872838577206688515671)
    ·
      refine ⟨14216809257865810032773507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9477872838577206688515671 14216809257865810032773507)
      ·
        refine ⟨21325213886798715049160261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14216809257865810032773507 21325213886798715049160261)
        ·
          refine ⟨3998477603774759071717549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21325213886798715049160261 3998477603774759071717549)
          ·
            refine ⟨1499429101415534651894081, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3998477603774759071717549 1499429101415534651894081)
            ·
              refine ⟨1124571826061650988920561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1499429101415534651894081 1124571826061650988920561)
              ·
                refine ⟨843428869546238241690421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1124571826061650988920561 843428869546238241690421)
                ·
                  refine ⟨79071456519959835158477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 843428869546238241690421 79071456519959835158477)
                  ·
                    rfl

theorem cell21_346480_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 3, 2, 2, 5].length) (baseStart_346480 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346480 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346480 prefixEnd_346480 := by exact prefixLift 346480
  have htrace : WordTrace (prefixWord ++ tailWord_346480) baseStart_346480 baseEnd_346480 := by
    simpa [prefixWord, tailWord_346480, baseEnd_346480] using wordTrace_append hprefix tailTrace_346480
  have hstable : (prefixWord ++ tailWord_346480).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346480).length < 2 ^ (prefixWord ++ tailWord_346480).sum := by decide
  have hdescent : baseEnd_346480 < baseStart_346480 := by decide
  rcases family_descends (prefixWord ++ tailWord_346480) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346528 : List Nat := [2, 1, 1, 4, 1, 3, 4, 1, 4]
def baseStart_346528 : Nat := 118140960795 + 346528 * 2 ^ 59
def prefixEnd_346528 : Nat := 4983230072969 + 3 ^ 40 * 346528 * 2
def baseEnd_346528 : Nat := 79082410773922418358379

theorem tailTrace_346528 : CollatzResearch.WordTrace tailWord_346528 prefixEnd_346528 79082410773922418358379 := by
  unfold tailWord_346528
  simp only [CollatzResearch.WordTrace]
  refine ⟨6319457244297856557884119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8425942992397142077178825 6319457244297856557884119)
  ·
    refine ⟨9479185866446784836826179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6319457244297856557884119 9479185866446784836826179)
    ·
      refine ⟨14218778799670177255239269, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9479185866446784836826179 14218778799670177255239269)
      ·
        refine ⟨2666021024938158235357363, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14218778799670177255239269 2666021024938158235357363)
        ·
          refine ⟨3999031537407237353036045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2666021024938158235357363 3999031537407237353036045)
          ·
            refine ⟨1499636826527714007388517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 3999031537407237353036045 1499636826527714007388517)
            ·
              refine ⟨281181904973946376385347, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1499636826527714007388517 281181904973946376385347)
              ·
                refine ⟨421772857460919564578021, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281181904973946376385347 421772857460919564578021)
                ·
                  refine ⟨79082410773922418358379, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 421772857460919564578021 79082410773922418358379)
                  ·
                    rfl

theorem cell21_346528_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 3, 4, 1, 4].length) (baseStart_346528 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346528 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346528 prefixEnd_346528 := by exact prefixLift 346528
  have htrace : WordTrace (prefixWord ++ tailWord_346528) baseStart_346528 baseEnd_346528 := by
    simpa [prefixWord, tailWord_346528, baseEnd_346528] using wordTrace_append hprefix tailTrace_346528
  have hstable : (prefixWord ++ tailWord_346528).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346528).length < 2 ^ (prefixWord ++ tailWord_346528).sum := by decide
  have hdescent : baseEnd_346528 < baseStart_346528 := by decide
  rcases family_descends (prefixWord ++ tailWord_346528) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346666 : List Nat := [3, 1, 4, 1, 1, 2, 3, 3, 3]
def baseStart_346666 : Nat := 118140960795 + 346666 * 2 ^ 59
def prefixEnd_346666 : Nat := 4983230072969 + 3 ^ 40 * 346666 * 2
def baseEnd_346666 : Nat := 79113904254064845058097

theorem tailTrace_346666 : CollatzResearch.WordTrace tailWord_346666 prefixEnd_346666 79113904254064845058097 := by
  unfold tailWord_346666
  simp only [CollatzResearch.WordTrace]
  refine ⟨3160986940523940671072963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8429298508063841789527901 3160986940523940671072963)
  ·
    refine ⟨4741480410785911006609445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3160986940523940671072963 4741480410785911006609445)
    ·
      refine ⟨889027577022358313739271, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 4741480410785911006609445 889027577022358313739271)
      ·
        refine ⟨1333541365533537470608907, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 889027577022358313739271 1333541365533537470608907)
        ·
          refine ⟨2000312048300306205913361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1333541365533537470608907 2000312048300306205913361)
          ·
            refine ⟨1500234036225229654435021, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2000312048300306205913361 1500234036225229654435021)
            ·
              refine ⟨562587763584461120413133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1500234036225229654435021 562587763584461120413133)
              ·
                refine ⟨210970411344172920154925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 562587763584461120413133 210970411344172920154925)
                ·
                  refine ⟨79113904254064845058097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 210970411344172920154925 79113904254064845058097)
                  ·
                    rfl

theorem cell21_346666_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 1, 2, 3, 3, 3].length) (baseStart_346666 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346666 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346666 prefixEnd_346666 := by exact prefixLift 346666
  have htrace : WordTrace (prefixWord ++ tailWord_346666) baseStart_346666 baseEnd_346666 := by
    simpa [prefixWord, tailWord_346666, baseEnd_346666] using wordTrace_append hprefix tailTrace_346666
  have hstable : (prefixWord ++ tailWord_346666).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346666).length < 2 ^ (prefixWord ++ tailWord_346666).sum := by decide
  have hdescent : baseEnd_346666 < baseStart_346666 := by decide
  rcases family_descends (prefixWord ++ tailWord_346666) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346669 : List Nat := [1, 5, 4, 1, 2, 1, 7]
def baseStart_346669 : Nat := 118140960795 + 346669 * 2 ^ 59
def prefixEnd_346669 : Nat := 4983230072969 + 3 ^ 40 * 346669 * 2
def baseEnd_346669 : Nat := 8790509877215278500899

theorem tailTrace_346669 : CollatzResearch.WordTrace tailWord_346669 prefixEnd_346669 8790509877215278500899 := by
  unfold tailWord_346669
  simp only [CollatzResearch.WordTrace]
  refine ⟨12644057181084894196651061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8429371454056596131100707 12644057181084894196651061)
  ·
    refine ⟨1185380360726708830936037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12644057181084894196651061 1185380360726708830936037)
    ·
      refine ⟨222258817636257905800507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 1185380360726708830936037 222258817636257905800507)
      ·
        refine ⟨333388226454386858700761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 222258817636257905800507 333388226454386858700761)
        ·
          refine ⟨250041169840790144025571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 333388226454386858700761 250041169840790144025571)
          ·
            refine ⟨375061754761185216038357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250041169840790144025571 375061754761185216038357)
            ·
              refine ⟨8790509877215278500899, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 375061754761185216038357 8790509877215278500899)
              ·
                rfl

theorem cell21_346669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 4, 1, 2, 1, 7].length) (baseStart_346669 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346669 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346669 prefixEnd_346669 := by exact prefixLift 346669
  have htrace : WordTrace (prefixWord ++ tailWord_346669) baseStart_346669 baseEnd_346669 := by
    simpa [prefixWord, tailWord_346669, baseEnd_346669] using wordTrace_append hprefix tailTrace_346669
  have hstable : (prefixWord ++ tailWord_346669).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346669).length < 2 ^ (prefixWord ++ tailWord_346669).sum := by decide
  have hdescent : baseEnd_346669 < baseStart_346669 := by decide
  rcases family_descends (prefixWord ++ tailWord_346669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346736 : List Nat := [2, 1, 1, 1, 16]
def baseStart_346736 : Nat := 118140960795 + 346736 * 2 ^ 59
def prefixEnd_346736 : Nat := 4983230072969 + 3 ^ 40 * 346736 * 2
def baseEnd_346736 : Nat := 976912088984694801127

theorem tailTrace_346736 : CollatzResearch.WordTrace tailWord_346736 prefixEnd_346736 976912088984694801127 := by
  unfold tailWord_346736
  simp only [CollatzResearch.WordTrace]
  refine ⟨6323250435921082319670031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8431000581228109759560041 6323250435921082319670031)
  ·
    refine ⟨9484875653881623479505047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6323250435921082319670031 9484875653881623479505047)
    ·
      refine ⟨14227313480822435219257571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9484875653881623479505047 14227313480822435219257571)
      ·
        refine ⟨21340970221233652828886357, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14227313480822435219257571 21340970221233652828886357)
        ·
          refine ⟨976912088984694801127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 21340970221233652828886357 976912088984694801127)
          ·
            rfl

theorem cell21_346736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 16].length) (baseStart_346736 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346736 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346736 prefixEnd_346736 := by exact prefixLift 346736
  have htrace : WordTrace (prefixWord ++ tailWord_346736) baseStart_346736 baseEnd_346736 := by
    simpa [prefixWord, tailWord_346736, baseEnd_346736] using wordTrace_append hprefix tailTrace_346736
  have hstable : (prefixWord ++ tailWord_346736).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346736).length < 2 ^ (prefixWord ++ tailWord_346736).sum := by decide
  have hdescent : baseEnd_346736 < baseStart_346736 := by decide
  rcases family_descends (prefixWord ++ tailWord_346736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346767 : List Nat := [1, 1, 2, 1, 1, 1, 1, 8, 5]
def baseStart_346767 : Nat := 118140960795 + 346767 * 2 ^ 59
def prefixEnd_346767 : Nat := 4983230072969 + 3 ^ 40 * 346767 * 2
def baseEnd_346767 : Nat := 79136953830111113874557

theorem tailTrace_346767 : CollatzResearch.WordTrace tailWord_346767 prefixEnd_346767 79136953830111113874557 := by
  unfold tailWord_346767
  simp only [CollatzResearch.WordTrace]
  refine ⟨12647631534729856933718555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8431754356486571289145703 12647631534729856933718555)
  ·
    refine ⟨18971447302094785400577833, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12647631534729856933718555 18971447302094785400577833)
    ·
      refine ⟨14228585476571089050433375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 18971447302094785400577833 14228585476571089050433375)
      ·
        refine ⟨21342878214856633575650063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14228585476571089050433375 21342878214856633575650063)
        ·
          refine ⟨32014317322284950363475095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21342878214856633575650063 32014317322284950363475095)
          ·
            refine ⟨48021475983427425545212643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 32014317322284950363475095 48021475983427425545212643)
            ·
              refine ⟨72032213975141138317818965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 48021475983427425545212643 72032213975141138317818965)
              ·
                refine ⟨844127507521185214661941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 72032213975141138317818965 844127507521185214661941)
                ·
                  refine ⟨79136953830111113874557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 844127507521185214661941 79136953830111113874557)
                  ·
                    rfl

theorem cell21_346767_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 1, 1, 8, 5].length) (baseStart_346767 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346767 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346767 prefixEnd_346767 := by exact prefixLift 346767
  have htrace : WordTrace (prefixWord ++ tailWord_346767) baseStart_346767 baseEnd_346767 := by
    simpa [prefixWord, tailWord_346767, baseEnd_346767] using wordTrace_append hprefix tailTrace_346767
  have hstable : (prefixWord ++ tailWord_346767).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346767).length < 2 ^ (prefixWord ++ tailWord_346767).sum := by decide
  have hdescent : baseEnd_346767 < baseStart_346767 := by decide
  rcases family_descends (prefixWord ++ tailWord_346767) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346953 : List Nat := [1, 2, 1, 1, 2, 6, 2, 3, 3]
def baseStart_346953 : Nat := 118140960795 + 346953 * 2 ^ 59
def prefixEnd_346953 : Nat := 4983230072969 + 3 ^ 40 * 346953 * 2
def baseEnd_346953 : Nat := 79179401564216123774177

theorem tailTrace_346953 : CollatzResearch.WordTrace tailWord_346953 prefixEnd_346953 79179401564216123774177 := by
  unfold tailWord_346953
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654415512056010699989513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8436277008037340466659675 12654415512056010699989513)
  ·
    refine ⟨9490811634042008024992135, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12654415512056010699989513 9490811634042008024992135)
    ·
      refine ⟨14236217451063012037488203, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9490811634042008024992135 14236217451063012037488203)
      ·
        refine ⟨21354326176594518056232305, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14236217451063012037488203 21354326176594518056232305)
        ·
          refine ⟨16015744632445888542174229, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21354326176594518056232305 16015744632445888542174229)
          ·
            refine ⟨750738029645901025414417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 16015744632445888542174229 750738029645901025414417)
            ·
              refine ⟨563053522234425769060813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 750738029645901025414417 563053522234425769060813)
              ·
                refine ⟨211145070837909663397805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 563053522234425769060813 211145070837909663397805)
                ·
                  refine ⟨79179401564216123774177, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211145070837909663397805 79179401564216123774177)
                  ·
                    rfl

theorem cell21_346953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 2, 6, 2, 3, 3].length) (baseStart_346953 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346953 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346953 prefixEnd_346953 := by exact prefixLift 346953
  have htrace : WordTrace (prefixWord ++ tailWord_346953) baseStart_346953 baseEnd_346953 := by
    simpa [prefixWord, tailWord_346953, baseEnd_346953] using wordTrace_append hprefix tailTrace_346953
  have hstable : (prefixWord ++ tailWord_346953).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346953).length < 2 ^ (prefixWord ++ tailWord_346953).sum := by decide
  have hdescent : baseEnd_346953 < baseStart_346953 := by decide
  rcases family_descends (prefixWord ++ tailWord_346953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346967 : List Nat := [1, 1, 3, 2, 4, 1, 3, 2, 4]
def baseStart_346967 : Nat := 118140960795 + 346967 * 2 ^ 59
def prefixEnd_346967 : Nat := 4983230072969 + 3 ^ 40 * 346967 * 2
def baseEnd_346967 : Nat := 79182596554955210540815

theorem tailTrace_346967 : CollatzResearch.WordTrace tailWord_346967 prefixEnd_346967 79182596554955210540815 := by
  unfold tailWord_346967
  simp only [CollatzResearch.WordTrace]
  refine ⟨12654926134005291090999155, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8436617422670194060666103 12654926134005291090999155)
  ·
    refine ⟨18982389201007936636498733, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12654926134005291090999155 18982389201007936636498733)
    ·
      refine ⟨7118395950377976238687025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 18982389201007936636498733 7118395950377976238687025)
      ·
        refine ⟨5338796962783482179015269, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7118395950377976238687025 5338796962783482179015269)
        ·
          refine ⟨1001024430521902908565363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 5338796962783482179015269 1001024430521902908565363)
          ·
            refine ⟨1501536645782854362848045, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001024430521902908565363 1501536645782854362848045)
            ·
              refine ⟨563076242168570386068017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1501536645782854362848045 563076242168570386068017)
              ·
                refine ⟨422307181626427789551013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563076242168570386068017 422307181626427789551013)
                ·
                  refine ⟨79182596554955210540815, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422307181626427789551013 79182596554955210540815)
                  ·
                    rfl

theorem cell21_346967_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 4, 1, 3, 2, 4].length) (baseStart_346967 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346967 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346967 prefixEnd_346967 := by exact prefixLift 346967
  have htrace : WordTrace (prefixWord ++ tailWord_346967) baseStart_346967 baseEnd_346967 := by
    simpa [prefixWord, tailWord_346967, baseEnd_346967] using wordTrace_append hprefix tailTrace_346967
  have hstable : (prefixWord ++ tailWord_346967).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346967).length < 2 ^ (prefixWord ++ tailWord_346967).sum := by decide
  have hdescent : baseEnd_346967 < baseStart_346967 := by decide
  rcases family_descends (prefixWord ++ tailWord_346967) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346984 : List Nat := [2, 1, 4, 2, 1, 3, 3, 1, 4]
def baseStart_346984 : Nat := 118140960795 + 346984 * 2 ^ 59
def prefixEnd_346984 : Nat := 4983230072969 + 3 ^ 40 * 346984 * 2
def baseEnd_346984 : Nat := 79186476186566958757447

theorem tailTrace_346984 : CollatzResearch.WordTrace tailWord_346984 prefixEnd_346984 79186476186566958757447 := by
  unfold tailWord_346984
  simp only [CollatzResearch.WordTrace]
  refine ⟨6327773087471851497184003, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8437030783295801996245337 6327773087471851497184003)
  ·
    refine ⟨9491659631207777245776005, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6327773087471851497184003 9491659631207777245776005)
    ·
      refine ⟨1779686180851458233583001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9491659631207777245776005 1779686180851458233583001)
      ·
        refine ⟨1334764635638593675187251, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1779686180851458233583001 1334764635638593675187251)
        ·
          refine ⟨2002146953457890512780877, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1334764635638593675187251 2002146953457890512780877)
          ·
            refine ⟨750805107546708942292829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2002146953457890512780877 750805107546708942292829)
            ·
              refine ⟨281551915330015853359811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 750805107546708942292829 281551915330015853359811)
              ·
                refine ⟨422327872995023780039717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281551915330015853359811 422327872995023780039717)
                ·
                  refine ⟨79186476186566958757447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422327872995023780039717 79186476186566958757447)
                  ·
                    rfl

theorem cell21_346984_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 3, 3, 1, 4].length) (baseStart_346984 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346984 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346984 prefixEnd_346984 := by exact prefixLift 346984
  have htrace : WordTrace (prefixWord ++ tailWord_346984) baseStart_346984 baseEnd_346984 := by
    simpa [prefixWord, tailWord_346984, baseEnd_346984] using wordTrace_append hprefix tailTrace_346984
  have hstable : (prefixWord ++ tailWord_346984).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346984).length < 2 ^ (prefixWord ++ tailWord_346984).sum := by decide
  have hdescent : baseEnd_346984 < baseStart_346984 := by decide
  rcases family_descends (prefixWord ++ tailWord_346984) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346995 : List Nat := [1, 1, 1, 2, 2, 1, 6, 2, 5]
def baseStart_346995 : Nat := 118140960795 + 346995 * 2 ^ 59
def prefixEnd_346995 : Nat := 4983230072969 + 3 ^ 40 * 346995 * 2
def baseEnd_346995 : Nat := 79188986536433384074091

theorem tailTrace_346995 : CollatzResearch.WordTrace tailWord_346995 prefixEnd_346995 79188986536433384074091 := by
  unfold tailWord_346995
  simp only [CollatzResearch.WordTrace]
  refine ⟨12655947377903851873018439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8437298251935901248678959 12655947377903851873018439)
  ·
    refine ⟨18983921066855777809527659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12655947377903851873018439 18983921066855777809527659)
    ·
      refine ⟨28475881600283666714291489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18983921066855777809527659 28475881600283666714291489)
      ·
        refine ⟨21356911200212750035718617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28475881600283666714291489 21356911200212750035718617)
        ·
          refine ⟨16017683400159562526788963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21356911200212750035718617 16017683400159562526788963)
          ·
            refine ⟨24026525100239343790183445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16017683400159562526788963 24026525100239343790183445)
            ·
              refine ⟨1126243364073719240164849, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24026525100239343790183445 1126243364073719240164849)
              ·
                refine ⟨844682523055289430123637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1126243364073719240164849 844682523055289430123637)
                ·
                  refine ⟨79188986536433384074091, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 844682523055289430123637 79188986536433384074091)
                  ·
                    rfl

theorem cell21_346995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 1, 6, 2, 5].length) (baseStart_346995 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346995 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346995 prefixEnd_346995 := by exact prefixLift 346995
  have htrace : WordTrace (prefixWord ++ tailWord_346995) baseStart_346995 baseEnd_346995 := by
    simpa [prefixWord, tailWord_346995, baseEnd_346995] using wordTrace_append hprefix tailTrace_346995
  have hstable : (prefixWord ++ tailWord_346995).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346995).length < 2 ^ (prefixWord ++ tailWord_346995).sum := by decide
  have hdescent : baseEnd_346995 < baseStart_346995 := by decide
  rcases family_descends (prefixWord ++ tailWord_346995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_346998 : List Nat := [5, 1, 1, 3, 1, 2, 1, 7]
def baseStart_346998 : Nat := 118140960795 + 346998 * 2 ^ 59
def prefixEnd_346998 : Nat := 4983230072969 + 3 ^ 40 * 346998 * 2
def baseEnd_346998 : Nat := 26396557059102015174695

theorem tailTrace_346998 : CollatzResearch.WordTrace tailWord_346998 prefixEnd_346998 26396557059102015174695 := by
  unfold tailWord_346998
  simp only [CollatzResearch.WordTrace]
  refine ⟨791003549805811461586103, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8437371197928655590251765 791003549805811461586103)
  ·
    refine ⟨1186505324708717192379155, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 791003549805811461586103 1186505324708717192379155)
    ·
      refine ⟨1779757987063075788568733, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1186505324708717192379155 1779757987063075788568733)
      ·
        refine ⟨667409245148653420713275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1779757987063075788568733 667409245148653420713275)
        ·
          refine ⟨1001113867722980131069913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 667409245148653420713275 1001113867722980131069913)
          ·
            refine ⟨750835400792235098302435, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1001113867722980131069913 750835400792235098302435)
            ·
              refine ⟨1126253101188352647453653, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 750835400792235098302435 1126253101188352647453653)
              ·
                refine ⟨26396557059102015174695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1126253101188352647453653 26396557059102015174695)
                ·
                  rfl

theorem cell21_346998_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 3, 1, 2, 1, 7].length) (baseStart_346998 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_346998 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_346998 prefixEnd_346998 := by exact prefixLift 346998
  have htrace : WordTrace (prefixWord ++ tailWord_346998) baseStart_346998 baseEnd_346998 := by
    simpa [prefixWord, tailWord_346998, baseEnd_346998] using wordTrace_append hprefix tailTrace_346998
  have hstable : (prefixWord ++ tailWord_346998).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_346998).length < 2 ^ (prefixWord ++ tailWord_346998).sum := by decide
  have hdescent : baseEnd_346998 < baseStart_346998 := by decide
  rcases family_descends (prefixWord ++ tailWord_346998) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347040 : List Nat := [2, 1, 1, 4, 1, 1, 3, 8]
def baseStart_347040 : Nat := 118140960795 + 347040 * 2 ^ 59
def prefixEnd_347040 : Nat := 4983230072969 + 3 ^ 40 * 347040 * 2
def baseEnd_347040 : Nat := 26399752049841101941333

theorem tailTrace_347040 : CollatzResearch.WordTrace tailWord_347040 prefixEnd_347040 26399752049841101941333 := by
  unfold tailWord_347040
  simp only [CollatzResearch.WordTrace]
  refine ⟨6328794331370412279203287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8438392441827216372271049 6328794331370412279203287)
  ·
    refine ⟨9493191497055618418804931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6328794331370412279203287 9493191497055618418804931)
    ·
      refine ⟨14239787245583427628207397, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9493191497055618418804931 14239787245583427628207397)
      ·
        refine ⟨2669960108546892680288887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14239787245583427628207397 2669960108546892680288887)
        ·
          refine ⟨4004940162820339020433331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2669960108546892680288887 4004940162820339020433331)
          ·
            refine ⟨6007410244230508530649997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4004940162820339020433331 6007410244230508530649997)
            ·
              refine ⟨2252778841586440698993749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6007410244230508530649997 2252778841586440698993749)
              ·
                refine ⟨26399752049841101941333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2252778841586440698993749 26399752049841101941333)
                ·
                  rfl

theorem cell21_347040_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 8].length) (baseStart_347040 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347040 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347040 prefixEnd_347040 := by exact prefixLift 347040
  have htrace : WordTrace (prefixWord ++ tailWord_347040) baseStart_347040 baseEnd_347040 := by
    simpa [prefixWord, tailWord_347040, baseEnd_347040] using wordTrace_append hprefix tailTrace_347040
  have hstable : (prefixWord ++ tailWord_347040).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347040).length < 2 ^ (prefixWord ++ tailWord_347040).sum := by decide
  have hdescent : baseEnd_347040 < baseStart_347040 := by decide
  rcases family_descends (prefixWord ++ tailWord_347040) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347043 : List Nat := [1, 1, 1, 4, 1, 2, 6, 1, 4]
def baseStart_347043 : Nat := 118140960795 + 347043 * 2 ^ 59
def prefixEnd_347043 : Nat := 4983230072969 + 3 ^ 40 * 347043 * 2
def baseEnd_347043 : Nat := 79199940790395967273993

theorem tailTrace_347043 : CollatzResearch.WordTrace tailWord_347043 prefixEnd_347043 79199940790395967273993 := by
  unfold tailWord_347043
  simp only [CollatzResearch.WordTrace]
  refine ⟨12657698081729956070765783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8438465387819970713843855 12657698081729956070765783)
  ·
    refine ⟨18986547122594934106148675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12657698081729956070765783 18986547122594934106148675)
    ·
      refine ⟨28479820683892401159223013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18986547122594934106148675 28479820683892401159223013)
      ·
        refine ⟨5339966378229825217354315, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28479820683892401159223013 5339966378229825217354315)
        ·
          refine ⟨8009949567344737826031473, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5339966378229825217354315 8009949567344737826031473)
          ·
            refine ⟨6007462175508553369523605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8009949567344737826031473 6007462175508553369523605)
            ·
              refine ⟨281599789476963439196419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6007462175508553369523605 281599789476963439196419)
              ·
                refine ⟨422399684215445158794629, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 281599789476963439196419 422399684215445158794629)
                ·
                  refine ⟨79199940790395967273993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422399684215445158794629 79199940790395967273993)
                  ·
                    rfl

theorem cell21_347043_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 2, 6, 1, 4].length) (baseStart_347043 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347043 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347043 prefixEnd_347043 := by exact prefixLift 347043
  have htrace : WordTrace (prefixWord ++ tailWord_347043) baseStart_347043 baseEnd_347043 := by
    simpa [prefixWord, tailWord_347043, baseEnd_347043] using wordTrace_append hprefix tailTrace_347043
  have hstable : (prefixWord ++ tailWord_347043).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347043).length < 2 ^ (prefixWord ++ tailWord_347043).sum := by decide
  have hdescent : baseEnd_347043 < baseStart_347043 := by decide
  rcases family_descends (prefixWord ++ tailWord_347043) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347147 : List Nat := [1, 1, 1, 1, 6, 2, 1, 3, 5]
def baseStart_347147 : Nat := 118140960795 + 347147 * 2 ^ 59
def prefixEnd_347147 : Nat := 4983230072969 + 3 ^ 40 * 347147 * 2
def baseEnd_347147 : Nat := 79223675007314897540447

theorem tailTrace_347147 : CollatzResearch.WordTrace tailWord_347147 prefixEnd_347147 79223675007314897540447 := by
  unfold tailWord_347147
  simp only [CollatzResearch.WordTrace]
  refine ⟨12661491273353181832551695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8440994182235454555034463 12661491273353181832551695)
  ·
    refine ⟨18992236910029772748827543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12661491273353181832551695 18992236910029772748827543)
    ·
      refine ⟨28488355365044659123241315, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 18992236910029772748827543 28488355365044659123241315)
      ·
        refine ⟨42732533047566988684861973, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 28488355365044659123241315 42732533047566988684861973)
        ·
          refine ⟨2003087486604702594602905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 42732533047566988684861973 2003087486604702594602905)
          ·
            refine ⟨1502315614953526945952179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2003087486604702594602905 1502315614953526945952179)
            ·
              refine ⟨2253473422430290418928269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1502315614953526945952179 2253473422430290418928269)
              ·
                refine ⟨845052533411358907098101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2253473422430290418928269 845052533411358907098101)
                ·
                  refine ⟨79223675007314897540447, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 845052533411358907098101 79223675007314897540447)
                  ·
                    rfl

theorem cell21_347147_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 2, 1, 3, 5].length) (baseStart_347147 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347147 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347147 prefixEnd_347147 := by exact prefixLift 347147
  have htrace : WordTrace (prefixWord ++ tailWord_347147) baseStart_347147 baseEnd_347147 := by
    simpa [prefixWord, tailWord_347147, baseEnd_347147] using wordTrace_append hprefix tailTrace_347147
  have hstable : (prefixWord ++ tailWord_347147).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347147).length < 2 ^ (prefixWord ++ tailWord_347147).sum := by decide
  have hdescent : baseEnd_347147 < baseStart_347147 := by decide
  rcases family_descends (prefixWord ++ tailWord_347147) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347192 : List Nat := [2, 1, 2, 1, 5, 1, 9]
def baseStart_347192 : Nat := 118140960795 + 347192 * 2 ^ 59
def prefixEnd_347192 : Nat := 4983230072969 + 3 ^ 40 * 347192 * 2
def baseEnd_347192 : Nat := 8803771624489424365595

theorem tailTrace_347192 : CollatzResearch.WordTrace tailWord_347192 prefixEnd_347192 8803771624489424365595 := by
  unfold tailWord_347192
  simp only [CollatzResearch.WordTrace]
  refine ⟨6331566279095077258969915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8442088372126769678626553 6331566279095077258969915)
  ·
    refine ⟨9497349418642615888454873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6331566279095077258969915 9497349418642615888454873)
    ·
      refine ⟨7123012063981961916341155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9497349418642615888454873 7123012063981961916341155)
      ·
        refine ⟨10684518095972942874511733, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7123012063981961916341155 10684518095972942874511733)
        ·
          refine ⟨1001673571497463394485475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10684518095972942874511733 1001673571497463394485475)
          ·
            refine ⟨1502510357246195091728213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1001673571497463394485475 1502510357246195091728213)
            ·
              refine ⟨8803771624489424365595, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1502510357246195091728213 8803771624489424365595)
              ·
                rfl

theorem cell21_347192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 9].length) (baseStart_347192 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347192 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347192 prefixEnd_347192 := by exact prefixLift 347192
  have htrace : WordTrace (prefixWord ++ tailWord_347192) baseStart_347192 baseEnd_347192 := by
    simpa [prefixWord, tailWord_347192, baseEnd_347192] using wordTrace_append hprefix tailTrace_347192
  have hstable : (prefixWord ++ tailWord_347192).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347192).length < 2 ^ (prefixWord ++ tailWord_347192).sum := by decide
  have hdescent : baseEnd_347192 < baseStart_347192 := by decide
  rcases family_descends (prefixWord ++ tailWord_347192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347257 : List Nat := [1, 2, 1, 3, 5, 1, 1, 4, 3]
def baseStart_347257 : Nat := 118140960795 + 347257 * 2 ^ 59
def prefixEnd_347257 : Nat := 4983230072969 + 3 ^ 40 * 347257 * 2
def baseEnd_347257 : Nat := 79248778505979150706889

theorem tailTrace_347257 : CollatzResearch.WordTrace tailWord_347257 prefixEnd_347257 79248778505979150706889 := by
  unfold tailWord_347257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12665503302954670619056025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8443668868636447079370683 12665503302954670619056025)
  ·
    refine ⟨9499127477216002964292019, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12665503302954670619056025 9499127477216002964292019)
    ·
      refine ⟨14248691215824004446438029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9499127477216002964292019 14248691215824004446438029)
      ·
        refine ⟨5343259205934001667414261, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14248691215824004446438029 5343259205934001667414261)
        ·
          refine ⟨500930550556312656320087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5343259205934001667414261 500930550556312656320087)
          ·
            refine ⟨751395825834468984480131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 500930550556312656320087 751395825834468984480131)
            ·
              refine ⟨1127093738751703476720197, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 751395825834468984480131 1127093738751703476720197)
              ·
                refine ⟨211330076015944401885037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1127093738751703476720197 211330076015944401885037)
                ·
                  refine ⟨79248778505979150706889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211330076015944401885037 79248778505979150706889)
                  ·
                    rfl

theorem cell21_347257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 5, 1, 1, 4, 3].length) (baseStart_347257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347257 prefixEnd_347257 := by exact prefixLift 347257
  have htrace : WordTrace (prefixWord ++ tailWord_347257) baseStart_347257 baseEnd_347257 := by
    simpa [prefixWord, tailWord_347257, baseEnd_347257] using wordTrace_append hprefix tailTrace_347257
  have hstable : (prefixWord ++ tailWord_347257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347257).length < 2 ^ (prefixWord ++ tailWord_347257).sum := by decide
  have hdescent : baseEnd_347257 < baseStart_347257 := by decide
  rcases family_descends (prefixWord ++ tailWord_347257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347423 : List Nat := [1, 1, 2, 4, 4, 1, 2, 2, 4]
def baseStart_347423 : Nat := 118140960795 + 347423 * 2 ^ 59
def prefixEnd_347423 : Nat := 4983230072969 + 3 ^ 40 * 347423 * 2
def baseEnd_347423 : Nat := 79286661967599750939883

theorem tailTrace_347423 : CollatzResearch.WordTrace tailWord_347423 prefixEnd_347423 79286661967599750939883 := by
  unfold tailWord_347423
  simp only [CollatzResearch.WordTrace]
  refine ⟨12671557820353280969598923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8447705213568853979732615 12671557820353280969598923)
  ·
    refine ⟨19007336730529921454398385, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12671557820353280969598923 19007336730529921454398385)
    ·
      refine ⟨14255502547897441090798789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19007336730529921454398385 14255502547897441090798789)
      ·
        refine ⟨2672906727730770204524773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 14255502547897441090798789 2672906727730770204524773)
        ·
          refine ⟨501170011449519413348395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2672906727730770204524773 501170011449519413348395)
          ·
            refine ⟨751755017174279120022593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 501170011449519413348395 751755017174279120022593)
            ·
              refine ⟨563816262880709340016945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 751755017174279120022593 563816262880709340016945)
              ·
                refine ⟨422862197160532005012709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563816262880709340016945 422862197160532005012709)
                ·
                  refine ⟨79286661967599750939883, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422862197160532005012709 79286661967599750939883)
                  ·
                    rfl

theorem cell21_347423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 4, 1, 2, 2, 4].length) (baseStart_347423 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347423 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347423 prefixEnd_347423 := by exact prefixLift 347423
  have htrace : WordTrace (prefixWord ++ tailWord_347423) baseStart_347423 baseEnd_347423 := by
    simpa [prefixWord, tailWord_347423, baseEnd_347423] using wordTrace_append hprefix tailTrace_347423
  have hstable : (prefixWord ++ tailWord_347423).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347423).length < 2 ^ (prefixWord ++ tailWord_347423).sum := by decide
  have hdescent : baseEnd_347423 < baseStart_347423 := by decide
  rcases family_descends (prefixWord ++ tailWord_347423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347468 : List Nat := [2, 2, 1, 3, 2, 2, 1, 5, 3]
def baseStart_347468 : Nat := 118140960795 + 347468 * 2 ^ 59
def prefixEnd_347468 : Nat := 4983230072969 + 3 ^ 40 * 347468 * 2
def baseEnd_347468 : Nat := 79296931580689672689791

theorem tailTrace_347468 : CollatzResearch.WordTrace tailWord_347468 prefixEnd_347468 79296931580689672689791 := by
  unfold tailWord_347468
  simp only [CollatzResearch.WordTrace]
  refine ⟨6336599552595126827493529, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8448799403460169103324705 6336599552595126827493529)
  ·
    refine ⟨4752449664446345120620147, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6336599552595126827493529 4752449664446345120620147)
    ·
      refine ⟨7128674496669517680930221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4752449664446345120620147 7128674496669517680930221)
      ·
        refine ⟨2673252936251069130348833, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7128674496669517680930221 2673252936251069130348833)
        ·
          refine ⟨2004939702188301847761625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2673252936251069130348833 2004939702188301847761625)
          ·
            refine ⟨1503704776641226385821219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2004939702188301847761625 1503704776641226385821219)
            ·
              refine ⟨2255557164961839578731829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1503704776641226385821219 2255557164961839578731829)
              ·
                refine ⟨211458484215172460506109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2255557164961839578731829 211458484215172460506109)
                ·
                  refine ⟨79296931580689672689791, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211458484215172460506109 79296931580689672689791)
                  ·
                    rfl

theorem cell21_347468_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 2, 2, 1, 5, 3].length) (baseStart_347468 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347468 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347468 prefixEnd_347468 := by exact prefixLift 347468
  have htrace : WordTrace (prefixWord ++ tailWord_347468) baseStart_347468 baseEnd_347468 := by
    simpa [prefixWord, tailWord_347468, baseEnd_347468] using wordTrace_append hprefix tailTrace_347468
  have hstable : (prefixWord ++ tailWord_347468).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347468).length < 2 ^ (prefixWord ++ tailWord_347468).sum := by decide
  have hdescent : baseEnd_347468 < baseStart_347468 := by decide
  rcases family_descends (prefixWord ++ tailWord_347468) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347482 : List Nat := [3, 1, 1, 2, 1, 2, 5, 2, 4]
def baseStart_347482 : Nat := 118140960795 + 347482 * 2 ^ 59
def prefixEnd_347482 : Nat := 4983230072969 + 3 ^ 40 * 347482 * 2
def baseEnd_347482 : Nat := 79300126571428759456429

theorem tailTrace_347482 : CollatzResearch.WordTrace tailWord_347482 prefixEnd_347482 79300126571428759456429 := by
  unfold tailWord_347482
  simp only [CollatzResearch.WordTrace]
  refine ⟨3168427431784883511499175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8449139818093022697331133 3168427431784883511499175)
  ·
    refine ⟨4752641147677325267248763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3168427431784883511499175 4752641147677325267248763)
    ·
      refine ⟨7128961721515987900873145, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4752641147677325267248763 7128961721515987900873145)
      ·
        refine ⟨5346721291136990925654859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7128961721515987900873145 5346721291136990925654859)
        ·
          refine ⟨8020081936705486388482289, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5346721291136990925654859 8020081936705486388482289)
          ·
            refine ⟨6015061452529114791361717, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8020081936705486388482289 6015061452529114791361717)
            ·
              refine ⟨563912011174604511690161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6015061452529114791361717 563912011174604511690161)
              ·
                refine ⟨422934008380953383767621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 563912011174604511690161 422934008380953383767621)
                ·
                  refine ⟨79300126571428759456429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 422934008380953383767621 79300126571428759456429)
                  ·
                    rfl

theorem cell21_347482_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 2, 5, 2, 4].length) (baseStart_347482 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347482 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347482 prefixEnd_347482 := by exact prefixLift 347482
  have htrace : WordTrace (prefixWord ++ tailWord_347482) baseStart_347482 baseEnd_347482 := by
    simpa [prefixWord, tailWord_347482, baseEnd_347482] using wordTrace_append hprefix tailTrace_347482
  have hstable : (prefixWord ++ tailWord_347482).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347482).length < 2 ^ (prefixWord ++ tailWord_347482).sum := by decide
  have hdescent : baseEnd_347482 < baseStart_347482 := by decide
  rcases family_descends (prefixWord ++ tailWord_347482) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347541 : List Nat := [1, 3, 2, 1, 1, 2, 4, 1, 6]
def baseStart_347541 : Nat := 118140960795 + 347541 * 2 ^ 59
def prefixEnd_347541 : Nat := 4983230072969 + 3 ^ 40 * 347541 * 2
def baseEnd_347541 : Nat := 79313591175257767972975

theorem tailTrace_347541 : CollatzResearch.WordTrace tailWord_347541 prefixEnd_347541 79313591175257767972975 := by
  unfold tailWord_347541
  simp only [CollatzResearch.WordTrace]
  refine ⟨12675861633925787122394477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8450574422617191414929651 12675861633925787122394477)
  ·
    refine ⟨4753448112722170170897929, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12675861633925787122394477 4753448112722170170897929)
    ·
      refine ⟨3565086084541627628173447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4753448112722170170897929 3565086084541627628173447)
      ·
        refine ⟨5347629126812441442260171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3565086084541627628173447 5347629126812441442260171)
        ·
          refine ⟨8021443690218662163390257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5347629126812441442260171 8021443690218662163390257)
          ·
            refine ⟨6016082767663996622542693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8021443690218662163390257 6016082767663996622542693)
            ·
              refine ⟨1128015518936999366726755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6016082767663996622542693 1128015518936999366726755)
              ·
                refine ⟨1692023278405499050090133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1128015518936999366726755 1692023278405499050090133)
                ·
                  refine ⟨79313591175257767972975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1692023278405499050090133 79313591175257767972975)
                  ·
                    rfl

theorem cell21_347541_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 4, 1, 6].length) (baseStart_347541 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347541 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347541 prefixEnd_347541 := by exact prefixLift 347541
  have htrace : WordTrace (prefixWord ++ tailWord_347541) baseStart_347541 baseEnd_347541 := by
    simpa [prefixWord, tailWord_347541, baseEnd_347541] using wordTrace_append hprefix tailTrace_347541
  have hstable : (prefixWord ++ tailWord_347541).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347541).length < 2 ^ (prefixWord ++ tailWord_347541).sum := by decide
  have hdescent : baseEnd_347541 < baseStart_347541 := by decide
  rcases family_descends (prefixWord ++ tailWord_347541) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347550 : List Nat := [4, 3, 1, 2, 3, 1, 2, 1, 4]
def baseStart_347550 : Nat := 118140960795 + 347550 * 2 ^ 59
def prefixEnd_347550 : Nat := 4983230072969 + 3 ^ 40 * 347550 * 2
def baseEnd_347550 : Nat := 79315645097875752322957

theorem tailTrace_347550 : CollatzResearch.WordTrace tailWord_347550 prefixEnd_347550 79315645097875752322957 := by
  unfold tailWord_347550
  simp only [CollatzResearch.WordTrace]
  refine ⟨1584523736361647707434013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8450793260595454439648069 1584523736361647707434013)
  ·
    refine ⟨594196401135617890287755, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1584523736361647707434013 594196401135617890287755)
    ·
      refine ⟨891294601703426835431633, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594196401135617890287755 891294601703426835431633)
      ·
        refine ⟨668470951277570126573725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 891294601703426835431633 668470951277570126573725)
        ·
          refine ⟨250676606729088797465147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 668470951277570126573725 250676606729088797465147)
          ·
            refine ⟨376014910093633196197721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 250676606729088797465147 376014910093633196197721)
            ·
              refine ⟨282011182570224897148291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376014910093633196197721 282011182570224897148291)
              ·
                refine ⟨423016773855337345722437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282011182570224897148291 423016773855337345722437)
                ·
                  refine ⟨79315645097875752322957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423016773855337345722437 79315645097875752322957)
                  ·
                    rfl

theorem cell21_347550_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 2, 3, 1, 2, 1, 4].length) (baseStart_347550 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347550 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347550 prefixEnd_347550 := by exact prefixLift 347550
  have htrace : WordTrace (prefixWord ++ tailWord_347550) baseStart_347550 baseEnd_347550 := by
    simpa [prefixWord, tailWord_347550, baseEnd_347550] using wordTrace_append hprefix tailTrace_347550
  have hstable : (prefixWord ++ tailWord_347550).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347550).length < 2 ^ (prefixWord ++ tailWord_347550).sum := by decide
  have hdescent : baseEnd_347550 < baseStart_347550 := by decide
  rcases family_descends (prefixWord ++ tailWord_347550) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347606 : List Nat := [5, 2, 1, 1, 1, 4, 1, 6]
def baseStart_347606 : Nat := 118140960795 + 347606 * 2 ^ 59
def prefixEnd_347606 : Nat := 4983230072969 + 3 ^ 40 * 347606 * 2
def baseEnd_347606 : Nat := 26442808353610699796503

theorem tailTrace_347606 : CollatzResearch.WordTrace tailWord_347606 prefixEnd_347606 26442808353610699796503 := by
  unfold tailWord_347606
  simp only [CollatzResearch.WordTrace]
  refine ⟨792389523668143951469417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8452154919126868815673781 792389523668143951469417)
  ·
    refine ⟨594292142751107963602063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 792389523668143951469417 594292142751107963602063)
    ·
      refine ⟨891438214126661945403095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 594292142751107963602063 891438214126661945403095)
      ·
        refine ⟨1337157321189992918104643, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891438214126661945403095 1337157321189992918104643)
        ·
          refine ⟨2005735981784989377156965, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337157321189992918104643 2005735981784989377156965)
          ·
            refine ⟨376075496584685508216931, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2005735981784989377156965 376075496584685508216931)
            ·
              refine ⟨564113244877028262325397, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376075496584685508216931 564113244877028262325397)
              ·
                refine ⟨26442808353610699796503, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 564113244877028262325397 26442808353610699796503)
                ·
                  rfl

theorem cell21_347606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 1, 1, 4, 1, 6].length) (baseStart_347606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347606 prefixEnd_347606 := by exact prefixLift 347606
  have htrace : WordTrace (prefixWord ++ tailWord_347606) baseStart_347606 baseEnd_347606 := by
    simpa [prefixWord, tailWord_347606, baseEnd_347606] using wordTrace_append hprefix tailTrace_347606
  have hstable : (prefixWord ++ tailWord_347606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347606).length < 2 ^ (prefixWord ++ tailWord_347606).sum := by decide
  have hdescent : baseEnd_347606 < baseStart_347606 := by decide
  rcases family_descends (prefixWord ++ tailWord_347606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347631 : List Nat := [1, 1, 2, 1, 4, 1, 2, 9]
def baseStart_347631 : Nat := 118140960795 + 347631 * 2 ^ 59
def prefixEnd_347631 : Nat := 4983230072969 + 3 ^ 40 * 347631 * 2
def baseEnd_347631 : Nat := 26444710133812537157597

theorem tailTrace_347631 : CollatzResearch.WordTrace tailWord_347631 prefixEnd_347631 26444710133812537157597 := by
  unfold tailWord_347631
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679144203599732493170747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8452762802399821662113831 12679144203599732493170747)
  ·
    refine ⟨19018716305399598739756121, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12679144203599732493170747 19018716305399598739756121)
    ·
      refine ⟨14264037229049699054817091, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19018716305399598739756121 14264037229049699054817091)
      ·
        refine ⟨21396055843574548582225637, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14264037229049699054817091 21396055843574548582225637)
        ·
          refine ⟨4011760470670227859167307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21396055843574548582225637 4011760470670227859167307)
          ·
            refine ⟨6017640706005341788750961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4011760470670227859167307 6017640706005341788750961)
            ·
              refine ⟨4513230529504006341563221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6017640706005341788750961 4513230529504006341563221)
              ·
                refine ⟨26444710133812537157597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 4513230529504006341563221 26444710133812537157597)
                ·
                  rfl

theorem cell21_347631_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 4, 1, 2, 9].length) (baseStart_347631 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347631 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347631 prefixEnd_347631 := by exact prefixLift 347631
  have htrace : WordTrace (prefixWord ++ tailWord_347631) baseStart_347631 baseEnd_347631 := by
    simpa [prefixWord, tailWord_347631, baseEnd_347631] using wordTrace_append hprefix tailTrace_347631
  have hstable : (prefixWord ++ tailWord_347631).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347631).length < 2 ^ (prefixWord ++ tailWord_347631).sum := by decide
  have hdescent : baseEnd_347631 < baseStart_347631 := by decide
  rcases family_descends (prefixWord ++ tailWord_347631) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347637 : List Nat := [1, 3, 5, 1, 1, 1, 1, 5, 3]
def baseStart_347637 : Nat := 118140960795 + 347637 * 2 ^ 59
def prefixEnd_347637 : Nat := 4983230072969 + 3 ^ 40 * 347637 * 2
def baseEnd_347637 : Nat := 79335499683182934372779

theorem tailTrace_347637 : CollatzResearch.WordTrace tailWord_347637 prefixEnd_347637 79335499683182934372779 := by
  unfold tailWord_347637
  simp only [CollatzResearch.WordTrace]
  refine ⟨12679363041577995517889165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8452908694385330345259443 12679363041577995517889165)
  ·
    refine ⟨4754761140591748319208437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12679363041577995517889165 4754761140591748319208437)
    ·
      refine ⟨445758856930476404925791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 4754761140591748319208437 445758856930476404925791)
      ·
        refine ⟨668638285395714607388687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 445758856930476404925791 668638285395714607388687)
        ·
          refine ⟨1002957428093571911083031, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 668638285395714607388687 1002957428093571911083031)
          ·
            refine ⟨1504436142140357866624547, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1002957428093571911083031 1504436142140357866624547)
            ·
              refine ⟨2256654213210536799936821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1504436142140357866624547 2256654213210536799936821)
              ·
                refine ⟨211561332488487824994077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2256654213210536799936821 211561332488487824994077)
                ·
                  refine ⟨79335499683182934372779, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211561332488487824994077 79335499683182934372779)
                  ·
                    rfl

theorem cell21_347637_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 1, 5, 3].length) (baseStart_347637 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347637 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347637 prefixEnd_347637 := by exact prefixLift 347637
  have htrace : WordTrace (prefixWord ++ tailWord_347637) baseStart_347637 baseEnd_347637 := by
    simpa [prefixWord, tailWord_347637, baseEnd_347637] using wordTrace_append hprefix tailTrace_347637
  have hstable : (prefixWord ++ tailWord_347637).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347637).length < 2 ^ (prefixWord ++ tailWord_347637).sum := by decide
  have hdescent : baseEnd_347637 < baseStart_347637 := by decide
  rcases family_descends (prefixWord ++ tailWord_347637) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347713 : List Nat := [1, 2, 5, 1, 1, 1, 5, 2, 3]
def baseStart_347713 : Nat := 118140960795 + 347713 * 2 ^ 59
def prefixEnd_347713 : Nat := 4983230072969 + 3 ^ 40 * 347713 * 2
def baseEnd_347713 : Nat := 79352843918623691105957

theorem tailTrace_347713 : CollatzResearch.WordTrace tailWord_347713 prefixEnd_347713 79352843918623691105957 := by
  unfold tailWord_347713
  simp only [CollatzResearch.WordTrace]
  refine ⟨12682134989302660497655793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8454756659535106998437195 12682134989302660497655793)
  ·
    refine ⟨9511601241976995373241845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12682134989302660497655793 9511601241976995373241845)
    ·
      refine ⟨891712616435343316241423, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9511601241976995373241845 891712616435343316241423)
      ·
        refine ⟨1337568924653014974362135, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 891712616435343316241423 1337568924653014974362135)
        ·
          refine ⟨2006353386979522461543203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1337568924653014974362135 2006353386979522461543203)
          ·
            refine ⟨3009530080469283692314805, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2006353386979522461543203 3009530080469283692314805)
            ·
              refine ⟨282143445043995346154513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3009530080469283692314805 282143445043995346154513)
              ·
                refine ⟨211607583782996509615885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282143445043995346154513 211607583782996509615885)
                ·
                  refine ⟨79352843918623691105957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211607583782996509615885 79352843918623691105957)
                  ·
                    rfl

theorem cell21_347713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 5, 2, 3].length) (baseStart_347713 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347713 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347713 prefixEnd_347713 := by exact prefixLift 347713
  have htrace : WordTrace (prefixWord ++ tailWord_347713) baseStart_347713 baseEnd_347713 := by
    simpa [prefixWord, tailWord_347713, baseEnd_347713] using wordTrace_append hprefix tailTrace_347713
  have hstable : (prefixWord ++ tailWord_347713).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347713).length < 2 ^ (prefixWord ++ tailWord_347713).sum := by decide
  have hdescent : baseEnd_347713 < baseStart_347713 := by decide
  rcases family_descends (prefixWord ++ tailWord_347713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347724 : List Nat := [2, 2, 1, 3, 1, 4, 2, 6]
def baseStart_347724 : Nat := 118140960795 + 347724 * 2 ^ 59
def prefixEnd_347724 : Nat := 4983230072969 + 3 ^ 40 * 347724 * 2
def baseEnd_347724 : Nat := 26451784756163372140867

theorem tailTrace_347724 : CollatzResearch.WordTrace tailWord_347724 prefixEnd_347724 26451784756163372140867 := by
  unfold tailWord_347724
  simp only [CollatzResearch.WordTrace]
  refine ⟨6341268096131404688153113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8455024128175206250870817 6341268096131404688153113)
  ·
    refine ⟨4755951072098553516114835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6341268096131404688153113 4755951072098553516114835)
    ·
      refine ⟨7133926608147830274172253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4755951072098553516114835 7133926608147830274172253)
      ·
        refine ⟨2675222478055436352814595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7133926608147830274172253 2675222478055436352814595)
        ·
          refine ⟨4012833717083154529221893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2675222478055436352814595 4012833717083154529221893)
          ·
            refine ⟨752406321953091474229105, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4012833717083154529221893 752406321953091474229105)
            ·
              refine ⟨564304741464818605671829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752406321953091474229105 564304741464818605671829)
              ·
                refine ⟨26451784756163372140867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 564304741464818605671829 26451784756163372140867)
                ·
                  rfl

theorem cell21_347724_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 3, 1, 4, 2, 6].length) (baseStart_347724 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347724 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347724 prefixEnd_347724 := by exact prefixLift 347724
  have htrace : WordTrace (prefixWord ++ tailWord_347724) baseStart_347724 baseEnd_347724 := by
    simpa [prefixWord, tailWord_347724, baseEnd_347724] using wordTrace_append hprefix tailTrace_347724
  have hstable : (prefixWord ++ tailWord_347724).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347724).length < 2 ^ (prefixWord ++ tailWord_347724).sum := by decide
  have hdescent : baseEnd_347724 < baseStart_347724 := by decide
  rcases family_descends (prefixWord ++ tailWord_347724) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347738 : List Nat := [3, 1, 1, 2, 1, 1, 1, 6, 5]
def baseStart_347738 : Nat := 118140960795 + 347738 * 2 ^ 59
def prefixEnd_347738 : Nat := 4983230072969 + 3 ^ 40 * 347738 * 2
def baseEnd_347738 : Nat := 79358549259229203189239

theorem tailTrace_347738 : CollatzResearch.WordTrace tailWord_347738 prefixEnd_347738 79358549259229203189239 := by
  unfold tailWord_347738
  simp only [CollatzResearch.WordTrace]
  refine ⟨3170761703553022441828967, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8455364542808059844877245 3170761703553022441828967)
  ·
    refine ⟨4756142555329533662743451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3170761703553022441828967 4756142555329533662743451)
    ·
      refine ⟨7134213832994300494115177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4756142555329533662743451 7134213832994300494115177)
      ·
        refine ⟨5350660374745725370586383, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7134213832994300494115177 5350660374745725370586383)
        ·
          refine ⟨8025990562118588055879575, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5350660374745725370586383 8025990562118588055879575)
          ·
            refine ⟨12038985843177882083819363, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8025990562118588055879575 12038985843177882083819363)
            ·
              refine ⟨18058478764766823125729045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12038985843177882083819363 18058478764766823125729045)
              ·
                refine ⟨846491192098444834018549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 18058478764766823125729045 846491192098444834018549)
                ·
                  refine ⟨79358549259229203189239, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846491192098444834018549 79358549259229203189239)
                  ·
                    rfl

theorem cell21_347738_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 6, 5].length) (baseStart_347738 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347738 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347738 prefixEnd_347738 := by exact prefixLift 347738
  have htrace : WordTrace (prefixWord ++ tailWord_347738) baseStart_347738 baseEnd_347738 := by
    simpa [prefixWord, tailWord_347738, baseEnd_347738] using wordTrace_append hprefix tailTrace_347738
  have hstable : (prefixWord ++ tailWord_347738).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347738).length < 2 ^ (prefixWord ++ tailWord_347738).sum := by decide
  have hdescent : baseEnd_347738 < baseStart_347738 := by decide
  rcases family_descends (prefixWord ++ tailWord_347738) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347786 : List Nat := [3, 1, 2, 3, 2, 1, 2, 3, 4]
def baseStart_347786 : Nat := 118140960795 + 347786 * 2 ^ 59
def prefixEnd_347786 : Nat := 4983230072969 + 3 ^ 40 * 347786 * 2
def baseEnd_347786 : Nat := 79369503513191786389141

theorem tailTrace_347786 : CollatzResearch.WordTrace tailWord_347786 prefixEnd_347786 79369503513191786389141 := by
  unfold tailWord_347786
  simp only [CollatzResearch.WordTrace]
  refine ⟨3171199379509548491265803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8456531678692129310042141 3171199379509548491265803)
  ·
    refine ⟨4756799069264322736898705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3171199379509548491265803 4756799069264322736898705)
    ·
      refine ⟨3567599301948242052674029, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4756799069264322736898705 3567599301948242052674029)
      ·
        refine ⟨1337849738230590769752761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3567599301948242052674029 1337849738230590769752761)
        ·
          refine ⟨1003387303672943077314571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1337849738230590769752761 1003387303672943077314571)
          ·
            refine ⟨1505080955509414615971857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1003387303672943077314571 1505080955509414615971857)
            ·
              refine ⟨1128810716632060961978893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1505080955509414615971857 1128810716632060961978893)
              ·
                refine ⟨423304018737022860742085, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1128810716632060961978893 423304018737022860742085)
                ·
                  refine ⟨79369503513191786389141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423304018737022860742085 79369503513191786389141)
                  ·
                    rfl

theorem cell21_347786_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 2, 1, 2, 3, 4].length) (baseStart_347786 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347786 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347786 prefixEnd_347786 := by exact prefixLift 347786
  have htrace : WordTrace (prefixWord ++ tailWord_347786) baseStart_347786 baseEnd_347786 := by
    simpa [prefixWord, tailWord_347786, baseEnd_347786] using wordTrace_append hprefix tailTrace_347786
  have hstable : (prefixWord ++ tailWord_347786).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347786).length < 2 ^ (prefixWord ++ tailWord_347786).sum := by decide
  have hdescent : baseEnd_347786 < baseStart_347786 := by decide
  rcases family_descends (prefixWord ++ tailWord_347786) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347831 : List Nat := [1, 1, 3, 1, 5, 2, 2, 1, 5]
def baseStart_347831 : Nat := 118140960795 + 347831 * 2 ^ 59
def prefixEnd_347831 : Nat := 4983230072969 + 3 ^ 40 * 347831 * 2
def baseEnd_347831 : Nat := 79379773126281708139049

theorem tailTrace_347831 : CollatzResearch.WordTrace tailWord_347831 prefixEnd_347831 79379773126281708139049 := by
  unfold tailWord_347831
  simp only [CollatzResearch.WordTrace]
  refine ⟨12686438802875166650451347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8457625868583444433634231 12686438802875166650451347)
  ·
    refine ⟨19029658204312749975677021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12686438802875166650451347 19029658204312749975677021)
    ·
      refine ⟨7136121826617281240878883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19029658204312749975677021 7136121826617281240878883)
      ·
        refine ⟨10704182739925921861318325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7136121826617281240878883 10704182739925921861318325)
        ·
          refine ⟨1003517131868055174498593, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 10704182739925921861318325 1003517131868055174498593)
          ·
            refine ⟨752637848901041380873945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1003517131868055174498593 752637848901041380873945)
            ·
              refine ⟨564478386675781035655459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 752637848901041380873945 564478386675781035655459)
              ·
                refine ⟨846717580013671553483189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 564478386675781035655459 846717580013671553483189)
                ·
                  refine ⟨79379773126281708139049, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 846717580013671553483189 79379773126281708139049)
                  ·
                    rfl

theorem cell21_347831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 5, 2, 2, 1, 5].length) (baseStart_347831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347831 prefixEnd_347831 := by exact prefixLift 347831
  have htrace : WordTrace (prefixWord ++ tailWord_347831) baseStart_347831 baseEnd_347831 := by
    simpa [prefixWord, tailWord_347831, baseEnd_347831] using wordTrace_append hprefix tailTrace_347831
  have hstable : (prefixWord ++ tailWord_347831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347831).length < 2 ^ (prefixWord ++ tailWord_347831).sum := by decide
  have hdescent : baseEnd_347831 < baseStart_347831 := by decide
  rcases family_descends (prefixWord ++ tailWord_347831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347938 : List Nat := [3, 3, 1, 1, 2, 1, 4, 2, 4]
def baseStart_347938 : Nat := 118140960795 + 347938 * 2 ^ 59
def prefixEnd_347938 : Nat := 4983230072969 + 3 ^ 40 * 347938 * 2
def baseEnd_347938 : Nat := 79404191984073299855497

theorem tailTrace_347938 : CollatzResearch.WordTrace tailWord_347938 prefixEnd_347938 79404191984073299855497 := by
  unfold tailWord_347938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3172585353371880981149117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8460227608991682616397645 3172585353371880981149117)
  ·
    refine ⟨1189719507514455367930919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3172585353371880981149117 1189719507514455367930919)
    ·
      refine ⟨1784579261271683051896379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1189719507514455367930919 1784579261271683051896379)
      ·
        refine ⟨2676868891907524577844569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1784579261271683051896379 2676868891907524577844569)
        ·
          refine ⟨2007651668930643433383427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2676868891907524577844569 2007651668930643433383427)
          ·
            refine ⟨3011477503395965150075141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2007651668930643433383427 3011477503395965150075141)
            ·
              refine ⟨564652031886743465639089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3011477503395965150075141 564652031886743465639089)
              ·
                refine ⟨423489023915057599229317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 564652031886743465639089 423489023915057599229317)
                ·
                  refine ⟨79404191984073299855497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423489023915057599229317 79404191984073299855497)
                  ·
                    rfl

theorem cell21_347938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 1, 4, 2, 4].length) (baseStart_347938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347938 prefixEnd_347938 := by exact prefixLift 347938
  have htrace : WordTrace (prefixWord ++ tailWord_347938) baseStart_347938 baseEnd_347938 := by
    simpa [prefixWord, tailWord_347938, baseEnd_347938] using wordTrace_append hprefix tailTrace_347938
  have hstable : (prefixWord ++ tailWord_347938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347938).length < 2 ^ (prefixWord ++ tailWord_347938).sum := by decide
  have hdescent : baseEnd_347938 < baseStart_347938 := by decide
  rcases family_descends (prefixWord ++ tailWord_347938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_347941 : List Nat := [1, 3, 1, 2, 3, 4, 2, 2, 3]
def baseStart_347941 : Nat := 118140960795 + 347941 * 2 ^ 59
def prefixEnd_347941 : Nat := 4983230072969 + 3 ^ 40 * 347941 * 2
def baseEnd_347941 : Nat := 79404876624945961305491

theorem tailTrace_347941 : CollatzResearch.WordTrace tailWord_347941 prefixEnd_347941 79404876624945961305491 := by
  unfold tailWord_347941
  simp only [CollatzResearch.WordTrace]
  refine ⟨12690450832476655436955677, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8460300554984436957970451 12690450832476655436955677)
  ·
    refine ⟨4758919062178745788858379, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12690450832476655436955677 4758919062178745788858379)
    ·
      refine ⟨7138378593268118683287569, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4758919062178745788858379 7138378593268118683287569)
      ·
        refine ⟨5353783944951089012465677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7138378593268118683287569 5353783944951089012465677)
        ·
          refine ⟨2007668979356658379674629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5353783944951089012465677 2007668979356658379674629)
          ·
            refine ⟨376437933629373446188993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2007668979356658379674629 376437933629373446188993)
            ·
              refine ⟨282328450222030084641745, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 376437933629373446188993 282328450222030084641745)
              ·
                refine ⟨211746337666522563481309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282328450222030084641745 211746337666522563481309)
                ·
                  refine ⟨79404876624945961305491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211746337666522563481309 79404876624945961305491)
                  ·
                    rfl

theorem cell21_347941_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 4, 2, 2, 3].length) (baseStart_347941 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_347941 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_347941 prefixEnd_347941 := by exact prefixLift 347941
  have htrace : WordTrace (prefixWord ++ tailWord_347941) baseStart_347941 baseEnd_347941 := by
    simpa [prefixWord, tailWord_347941, baseEnd_347941] using wordTrace_append hprefix tailTrace_347941
  have hstable : (prefixWord ++ tailWord_347941).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_347941).length < 2 ^ (prefixWord ++ tailWord_347941).sum := by decide
  have hdescent : baseEnd_347941 < baseStart_347941 := by decide
  rcases family_descends (prefixWord ++ tailWord_347941) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348062 : List Nat := [4, 3, 1, 3, 1, 1, 2, 6]
def baseStart_348062 : Nat := 118140960795 + 348062 * 2 ^ 59
def prefixEnd_348062 : Nat := 4983230072969 + 3 ^ 40 * 348062 * 2
def baseEnd_348062 : Nat := 26477496824492213262859

theorem tailTrace_348062 : CollatzResearch.WordTrace tailWord_348062 prefixEnd_348062 26477496824492213262859 := by
  unfold tailWord_348062
  simp only [CollatzResearch.WordTrace]
  refine ⟨1586858008129786637763805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8463242710025528734740293 1586858008129786637763805)
  ·
    refine ⟨595071753048669989161427, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 1586858008129786637763805 595071753048669989161427)
    ·
      refine ⟨892607629573004983742141, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 595071753048669989161427 892607629573004983742141)
      ·
        refine ⟨334727861089876868903303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 892607629573004983742141 334727861089876868903303)
        ·
          refine ⟨502091791634815303354955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 334727861089876868903303 502091791634815303354955)
          ·
            refine ⟨753137687452222955032433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502091791634815303354955 753137687452222955032433)
            ·
              refine ⟨564853265589167216274325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 753137687452222955032433 564853265589167216274325)
              ·
                refine ⟨26477496824492213262859, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 564853265589167216274325 26477496824492213262859)
                ·
                  rfl

theorem cell21_348062_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 3, 1, 1, 2, 6].length) (baseStart_348062 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348062 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348062 prefixEnd_348062 := by exact prefixLift 348062
  have htrace : WordTrace (prefixWord ++ tailWord_348062) baseStart_348062 baseEnd_348062 := by
    simpa [prefixWord, tailWord_348062, baseEnd_348062] using wordTrace_append hprefix tailTrace_348062
  have hstable : (prefixWord ++ tailWord_348062).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348062).length < 2 ^ (prefixWord ++ tailWord_348062).sum := by decide
  have hdescent : baseEnd_348062 < baseStart_348062 := by decide
  rcases family_descends (prefixWord ++ tailWord_348062) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348101 : List Nat := [1, 3, 1, 1, 1, 1, 1, 3, 9]
def baseStart_348101 : Nat := 118140960795 + 348101 * 2 ^ 59
def prefixEnd_348101 : Nat := 4983230072969 + 3 ^ 40 * 348101 * 2
def baseEnd_348101 : Nat := 79441390804821238638497

theorem tailTrace_348101 : CollatzResearch.WordTrace tailWord_348101 prefixEnd_348101 79441390804821238638497 := by
  unfold tailWord_348101
  simp only [CollatzResearch.WordTrace]
  refine ⟨12696286511897002762780157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8464191007931335175186771 12696286511897002762780157)
  ·
    refine ⟨4761107441961376036042559, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12696286511897002762780157 4761107441961376036042559)
    ·
      refine ⟨7141661162942064054063839, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4761107441961376036042559 7141661162942064054063839)
      ·
        refine ⟨10712491744413096081095759, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7141661162942064054063839 10712491744413096081095759)
        ·
          refine ⟨16068737616619644121643639, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10712491744413096081095759 16068737616619644121643639)
          ·
            refine ⟨24103106424929466182465459, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16068737616619644121643639 24103106424929466182465459)
            ·
              refine ⟨36154659637394199273698189, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 24103106424929466182465459 36154659637394199273698189)
              ·
                refine ⟨13557997364022824727636821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 36154659637394199273698189 13557997364022824727636821)
                ·
                  refine ⟨79441390804821238638497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 13557997364022824727636821 79441390804821238638497)
                  ·
                    rfl

theorem cell21_348101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 1, 3, 9].length) (baseStart_348101 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348101 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348101 prefixEnd_348101 := by exact prefixLift 348101
  have htrace : WordTrace (prefixWord ++ tailWord_348101) baseStart_348101 baseEnd_348101 := by
    simpa [prefixWord, tailWord_348101, baseEnd_348101] using wordTrace_append hprefix tailTrace_348101
  have hstable : (prefixWord ++ tailWord_348101).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348101).length < 2 ^ (prefixWord ++ tailWord_348101).sum := by decide
  have hdescent : baseEnd_348101 < baseStart_348101 := by decide
  rcases family_descends (prefixWord ++ tailWord_348101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348121 : List Nat := [1, 2, 1, 2, 7, 1, 1, 6]
def baseStart_348121 : Nat := 118140960795 + 348121 * 2 ^ 59
def prefixEnd_348121 : Nat := 4983230072969 + 3 ^ 40 * 348121 * 2
def baseEnd_348121 : Nat := 26481985025768549435041

theorem tailTrace_348121 : CollatzResearch.WordTrace tailWord_348121 prefixEnd_348121 26481985025768549435041 := by
  unfold tailWord_348121
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697015971824546178508217, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8464677314549697452338811 12697015971824546178508217)
  ·
    refine ⟨9522761978868409633881163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12697015971824546178508217 9522761978868409633881163)
    ·
      refine ⟨14284142968302614450821745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9522761978868409633881163 14284142968302614450821745)
      ·
        refine ⟨10713107226226960838116309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14284142968302614450821745 10713107226226960838116309)
        ·
          refine ⟨251088450614694394643351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 10713107226226960838116309 251088450614694394643351)
          ·
            refine ⟨376632675922041591965027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251088450614694394643351 376632675922041591965027)
            ·
              refine ⟨564949013883062387947541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 376632675922041591965027 564949013883062387947541)
              ·
                refine ⟨26481985025768549435041, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 564949013883062387947541 26481985025768549435041)
                ·
                  rfl

theorem cell21_348121_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 7, 1, 1, 6].length) (baseStart_348121 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348121 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348121 prefixEnd_348121 := by exact prefixLift 348121
  have htrace : WordTrace (prefixWord ++ tailWord_348121) baseStart_348121 baseEnd_348121 := by
    simpa [prefixWord, tailWord_348121, baseEnd_348121] using wordTrace_append hprefix tailTrace_348121
  have hstable : (prefixWord ++ tailWord_348121).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348121).length < 2 ^ (prefixWord ++ tailWord_348121).sum := by decide
  have hdescent : baseEnd_348121 < baseStart_348121 := by decide
  rcases family_descends (prefixWord ++ tailWord_348121) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348135 : List Nat := [1, 1, 5, 2, 3, 1, 1, 2, 5]
def baseStart_348135 : Nat := 118140960795 + 348135 * 2 ^ 59
def prefixEnd_348135 : Nat := 4983230072969 + 3 ^ 40 * 348135 * 2
def baseEnd_348135 : Nat := 79449150068044735071761

theorem tailTrace_348135 : CollatzResearch.WordTrace tailWord_348135 prefixEnd_348135 79449150068044735071761 := by
  unfold tailWord_348135
  simp only [CollatzResearch.WordTrace]
  refine ⟨12697526593773826569517859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8465017729182551046345239 12697526593773826569517859)
  ·
    refine ⟨19046289890660739854276789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12697526593773826569517859 19046289890660739854276789)
    ·
      refine ⟨1785589677249444361338449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19046289890660739854276789 1785589677249444361338449)
      ·
        refine ⟨1339192257937083271003837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1785589677249444361338449 1339192257937083271003837)
        ·
          refine ⟨502197096726406226626439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1339192257937083271003837 502197096726406226626439)
          ·
            refine ⟨753295645089609339939659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502197096726406226626439 753295645089609339939659)
            ·
              refine ⟨1129943467634414009909489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753295645089609339939659 1129943467634414009909489)
              ·
                refine ⟨847457600725810507432117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1129943467634414009909489 847457600725810507432117)
                ·
                  refine ⟨79449150068044735071761, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 847457600725810507432117 79449150068044735071761)
                  ·
                    rfl

theorem cell21_348135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 3, 1, 1, 2, 5].length) (baseStart_348135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348135 prefixEnd_348135 := by exact prefixLift 348135
  have htrace : WordTrace (prefixWord ++ tailWord_348135) baseStart_348135 baseEnd_348135 := by
    simpa [prefixWord, tailWord_348135, baseEnd_348135] using wordTrace_append hprefix tailTrace_348135
  have hstable : (prefixWord ++ tailWord_348135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348135).length < 2 ^ (prefixWord ++ tailWord_348135).sum := by decide
  have hdescent : baseEnd_348135 < baseStart_348135 := by decide
  rcases family_descends (prefixWord ++ tailWord_348135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348183 : List Nat := [1, 1, 3, 5, 2, 1, 3, 1, 4]
def baseStart_348183 : Nat := 118140960795 + 348183 * 2 ^ 59
def prefixEnd_348183 : Nat := 4983230072969 + 3 ^ 40 * 348183 * 2
def baseEnd_348183 : Nat := 79460104322007318271663

theorem tailTrace_348183 : CollatzResearch.WordTrace tailWord_348183 prefixEnd_348183 79460104322007318271663 := by
  unfold tailWord_348183
  simp only [CollatzResearch.WordTrace]
  refine ⟨12699277297599930767265203, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8466184865066620511510135 12699277297599930767265203)
  ·
    refine ⟨19048915946399896150897805, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12699277297599930767265203 19048915946399896150897805)
    ·
      refine ⟨7143343479899961056586677, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19048915946399896150897805 7143343479899961056586677)
      ·
        refine ⟨669688451240621349055001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 7143343479899961056586677 669688451240621349055001)
        ·
          refine ⟨502266338430466011791251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 669688451240621349055001 502266338430466011791251)
          ·
            refine ⟨753399507645699017686877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502266338430466011791251 753399507645699017686877)
            ·
              refine ⟨282524815367137131632579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753399507645699017686877 282524815367137131632579)
              ·
                refine ⟨423787223050705697448869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282524815367137131632579 423787223050705697448869)
                ·
                  refine ⟨79460104322007318271663, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423787223050705697448869 79460104322007318271663)
                  ·
                    rfl

theorem cell21_348183_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 5, 2, 1, 3, 1, 4].length) (baseStart_348183 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348183 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348183 prefixEnd_348183 := by exact prefixLift 348183
  have htrace : WordTrace (prefixWord ++ tailWord_348183) baseStart_348183 baseEnd_348183 := by
    simpa [prefixWord, tailWord_348183, baseEnd_348183] using wordTrace_append hprefix tailTrace_348183
  have hstable : (prefixWord ++ tailWord_348183).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348183).length < 2 ^ (prefixWord ++ tailWord_348183).sum := by decide
  have hdescent : baseEnd_348183 < baseStart_348183 := by decide
  rcases family_descends (prefixWord ++ tailWord_348183) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348194 : List Nat := [3, 3, 1, 1, 1, 2, 1, 4, 5]
def baseStart_348194 : Nat := 118140960795 + 348194 * 2 ^ 59
def prefixEnd_348194 : Nat := 4983230072969 + 3 ^ 40 * 348194 * 2
def baseEnd_348194 : Nat := 79462614671873743588307

theorem tailTrace_348194 : CollatzResearch.WordTrace tailWord_348194 prefixEnd_348194 79462614671873743588307 := by
  unfold tailWord_348194
  simp only [CollatzResearch.WordTrace]
  refine ⟨3174919625140019911478909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8466452333706719763943757 3174919625140019911478909)
  ·
    refine ⟨1190594859427507466804591, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 3174919625140019911478909 1190594859427507466804591)
    ·
      refine ⟨1785892289141261200206887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1190594859427507466804591 1785892289141261200206887)
      ·
        refine ⟨2678838433711891800310331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1785892289141261200206887 2678838433711891800310331)
        ·
          refine ⟨4018257650567837700465497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2678838433711891800310331 4018257650567837700465497)
          ·
            refine ⟨3013693237925878275349123, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4018257650567837700465497 3013693237925878275349123)
            ·
              refine ⟨4520539856888817413023685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3013693237925878275349123 4520539856888817413023685)
              ·
                refine ⟨847601223166653264941941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4520539856888817413023685 847601223166653264941941)
                ·
                  refine ⟨79462614671873743588307, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 847601223166653264941941 79462614671873743588307)
                  ·
                    rfl

theorem cell21_348194_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 1, 2, 1, 4, 5].length) (baseStart_348194 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348194 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348194 prefixEnd_348194 := by exact prefixLift 348194
  have htrace : WordTrace (prefixWord ++ tailWord_348194) baseStart_348194 baseEnd_348194 := by
    simpa [prefixWord, tailWord_348194, baseEnd_348194] using wordTrace_append hprefix tailTrace_348194
  have hstable : (prefixWord ++ tailWord_348194).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348194).length < 2 ^ (prefixWord ++ tailWord_348194).sum := by decide
  have hdescent : baseEnd_348194 < baseStart_348194 := by decide
  rcases family_descends (prefixWord ++ tailWord_348194) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348208 : List Nat := [2, 1, 1, 1, 2, 5, 1, 2, 6]
def baseStart_348208 : Nat := 118140960795 + 348208 * 2 ^ 59
def prefixEnd_348208 : Nat := 4983230072969 + 3 ^ 40 * 348208 * 2
def baseEnd_348208 : Nat := 79465809662612830354945

theorem tailTrace_348208 : CollatzResearch.WordTrace tailWord_348208 prefixEnd_348208 79465809662612830354945 := by
  unfold tailWord_348208
  simp only [CollatzResearch.WordTrace]
  refine ⟨6350094561254680018462639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8466792748339573357950185 6350094561254680018462639)
  ·
    refine ⟨9525141841882020027693959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6350094561254680018462639 9525141841882020027693959)
    ·
      refine ⟨14287712762823030041540939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9525141841882020027693959 14287712762823030041540939)
      ·
        refine ⟨21431569144234545062311409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14287712762823030041540939 21431569144234545062311409)
        ·
          refine ⟨16073676858175908796733557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 21431569144234545062311409 16073676858175908796733557)
          ·
            refine ⟨1506907205453991449693771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 16073676858175908796733557 1506907205453991449693771)
            ·
              refine ⟨2260360808180987174540657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1506907205453991449693771 2260360808180987174540657)
              ·
                refine ⟨1695270606135740380905493, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2260360808180987174540657 1695270606135740380905493)
                ·
                  refine ⟨79465809662612830354945, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1695270606135740380905493 79465809662612830354945)
                  ·
                    rfl

theorem cell21_348208_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 5, 1, 2, 6].length) (baseStart_348208 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348208 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348208 prefixEnd_348208 := by exact prefixLift 348208
  have htrace : WordTrace (prefixWord ++ tailWord_348208) baseStart_348208 baseEnd_348208 := by
    simpa [prefixWord, tailWord_348208, baseEnd_348208] using wordTrace_append hprefix tailTrace_348208
  have hstable : (prefixWord ++ tailWord_348208).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348208).length < 2 ^ (prefixWord ++ tailWord_348208).sum := by decide
  have hdescent : baseEnd_348208 < baseStart_348208 := by decide
  rcases family_descends (prefixWord ++ tailWord_348208) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348211 : List Nat := [1, 1, 1, 2, 4, 1, 5, 3, 3]
def baseStart_348211 : Nat := 118140960795 + 348211 * 2 ^ 59
def prefixEnd_348211 : Nat := 4983230072969 + 3 ^ 40 * 348211 * 2
def baseEnd_348211 : Nat := 79466494303485491804939

theorem tailTrace_348211 : CollatzResearch.WordTrace tailWord_348211 prefixEnd_348211 79466494303485491804939 := by
  unfold tailWord_348211
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700298541498491549284487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8466865694332327699522991 12700298541498491549284487)
  ·
    refine ⟨19050447812247737323926731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12700298541498491549284487 19050447812247737323926731)
    ·
      refine ⟨28575671718371605985890097, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19050447812247737323926731 28575671718371605985890097)
      ·
        refine ⟨21431753788778704489417573, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28575671718371605985890097 21431753788778704489417573)
        ·
          refine ⟨4018453835396007091765795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21431753788778704489417573 4018453835396007091765795)
          ·
            refine ⟨6027680753094010637648693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4018453835396007091765795 6027680753094010637648693)
            ·
              refine ⟨565095070602563497279565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 6027680753094010637648693 565095070602563497279565)
              ·
                refine ⟨211910651475961311479837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 565095070602563497279565 211910651475961311479837)
                ·
                  refine ⟨79466494303485491804939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 211910651475961311479837 79466494303485491804939)
                  ·
                    rfl

theorem cell21_348211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 1, 5, 3, 3].length) (baseStart_348211 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348211 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348211 prefixEnd_348211 := by exact prefixLift 348211
  have htrace : WordTrace (prefixWord ++ tailWord_348211) baseStart_348211 baseEnd_348211 := by
    simpa [prefixWord, tailWord_348211, baseEnd_348211] using wordTrace_append hprefix tailTrace_348211
  have hstable : (prefixWord ++ tailWord_348211).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348211).length < 2 ^ (prefixWord ++ tailWord_348211).sum := by decide
  have hdescent : baseEnd_348211 < baseStart_348211 := by decide
  rcases family_descends (prefixWord ++ tailWord_348211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348225 : List Nat := [1, 2, 5, 1, 2, 1, 2, 1, 6]
def baseStart_348225 : Nat := 118140960795 + 348225 * 2 ^ 59
def prefixEnd_348225 : Nat := 4983230072969 + 3 ^ 40 * 348225 * 2
def baseEnd_348225 : Nat := 79469689294224578571577

theorem tailTrace_348225 : CollatzResearch.WordTrace tailWord_348225 prefixEnd_348225 79469689294224578571577 := by
  unfold tailWord_348225
  simp only [CollatzResearch.WordTrace]
  refine ⟨12700809163447771940294129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8467206108965181293529419 12700809163447771940294129)
  ·
    refine ⟨9525606872585828955220597, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12700809163447771940294129 9525606872585828955220597)
    ·
      refine ⟨893025644304921464551931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9525606872585828955220597 893025644304921464551931)
      ·
        refine ⟨1339538466457382196827897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893025644304921464551931 1339538466457382196827897)
        ·
          refine ⟨1004653849843036647620923, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1339538466457382196827897 1004653849843036647620923)
          ·
            refine ⟨1506980774764554971431385, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1004653849843036647620923 1506980774764554971431385)
            ·
              refine ⟨1130235581073416228573539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1506980774764554971431385 1130235581073416228573539)
              ·
                refine ⟨1695353371610124342860309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1130235581073416228573539 1695353371610124342860309)
                ·
                  refine ⟨79469689294224578571577, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1695353371610124342860309 79469689294224578571577)
                  ·
                    rfl

theorem cell21_348225_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 2, 1, 2, 1, 6].length) (baseStart_348225 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348225 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348225 prefixEnd_348225 := by exact prefixLift 348225
  have htrace : WordTrace (prefixWord ++ tailWord_348225) baseStart_348225 baseEnd_348225 := by
    simpa [prefixWord, tailWord_348225, baseEnd_348225] using wordTrace_append hprefix tailTrace_348225
  have hstable : (prefixWord ++ tailWord_348225).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348225).length < 2 ^ (prefixWord ++ tailWord_348225).sum := by decide
  have hdescent : baseEnd_348225 < baseStart_348225 := by decide
  rcases family_descends (prefixWord ++ tailWord_348225) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348242 : List Nat := [3, 2, 2, 1, 4, 1, 1, 3, 4]
def baseStart_348242 : Nat := 118140960795 + 348242 * 2 ^ 59
def prefixEnd_348242 : Nat := 4983230072969 + 3 ^ 40 * 348242 * 2
def baseEnd_348242 : Nat := 79473568925836326788209

theorem tailTrace_348242 : CollatzResearch.WordTrace tailWord_348242 prefixEnd_348242 79473568925836326788209 := by
  unfold tailWord_348242
  simp only [CollatzResearch.WordTrace]
  refine ⟨3175357301096545960915745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8467619469590789229108653 3175357301096545960915745)
  ·
    refine ⟨2381517975822409470686809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3175357301096545960915745 2381517975822409470686809)
    ·
      refine ⟨1786138481866807103015107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2381517975822409470686809 1786138481866807103015107)
      ·
        refine ⟨2679207722800210654522661, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1786138481866807103015107 2679207722800210654522661)
        ·
          refine ⟨502351448025039497722999, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2679207722800210654522661 502351448025039497722999)
          ·
            refine ⟨753527172037559246584499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502351448025039497722999 753527172037559246584499)
            ·
              refine ⟨1130290758056338869876749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753527172037559246584499 1130290758056338869876749)
              ·
                refine ⟨423859034271127076203781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1130290758056338869876749 423859034271127076203781)
                ·
                  refine ⟨79473568925836326788209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 423859034271127076203781 79473568925836326788209)
                  ·
                    rfl

theorem cell21_348242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 4, 1, 1, 3, 4].length) (baseStart_348242 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348242 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348242 prefixEnd_348242 := by exact prefixLift 348242
  have htrace : WordTrace (prefixWord ++ tailWord_348242) baseStart_348242 baseEnd_348242 := by
    simpa [prefixWord, tailWord_348242, baseEnd_348242] using wordTrace_append hprefix tailTrace_348242
  have hstable : (prefixWord ++ tailWord_348242).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348242).length < 2 ^ (prefixWord ++ tailWord_348242).sum := by decide
  have hdescent : baseEnd_348242 < baseStart_348242 := by decide
  rcases family_descends (prefixWord ++ tailWord_348242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348391 : List Nat := [1, 1, 5, 3, 1, 1, 9]
def baseStart_348391 : Nat := 118140960795 + 348391 * 2 ^ 59
def prefixEnd_348391 : Nat := 4983230072969 + 3 ^ 40 * 348391 * 2
def baseEnd_348391 : Nat := 8834174750649464311619

theorem tailTrace_348391 : CollatzResearch.WordTrace tailWord_348391 prefixEnd_348391 8834174750649464311619 := by
  unfold tailWord_348391
  simp only [CollatzResearch.WordTrace]
  refine ⟨12706863680846382290837027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8471242453897588193891351 12706863680846382290837027)
  ·
    refine ⟨19060295521269573436255541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12706863680846382290837027 19060295521269573436255541)
    ·
      refine ⟨1786902705119022509648957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19060295521269573436255541 1786902705119022509648957)
      ·
        refine ⟨670088514419633441118359, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 1786902705119022509648957 670088514419633441118359)
        ·
          refine ⟨1005132771629450161677539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670088514419633441118359 1005132771629450161677539)
          ·
            refine ⟨1507699157444175242516309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1005132771629450161677539 1507699157444175242516309)
            ·
              refine ⟨8834174750649464311619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1507699157444175242516309 8834174750649464311619)
              ·
                rfl

theorem cell21_348391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 9].length) (baseStart_348391 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348391 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348391 prefixEnd_348391 := by exact prefixLift 348391
  have htrace : WordTrace (prefixWord ++ tailWord_348391) baseStart_348391 baseEnd_348391 := by
    simpa [prefixWord, tailWord_348391, baseEnd_348391] using wordTrace_append hprefix tailTrace_348391
  have hstable : (prefixWord ++ tailWord_348391).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348391).length < 2 ^ (prefixWord ++ tailWord_348391).sum := by decide
  have hdescent : baseEnd_348391 < baseStart_348391 := by decide
  rcases family_descends (prefixWord ++ tailWord_348391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348397 : List Nat := [1, 5, 1, 2, 3, 1, 3, 2, 3]
def baseStart_348397 : Nat := 118140960795 + 348397 * 2 ^ 59
def prefixEnd_348397 : Nat := 4983230072969 + 3 ^ 40 * 348397 * 2
def baseEnd_348397 : Nat := 79508942037590501704559

theorem tailTrace_348397 : CollatzResearch.WordTrace tailWord_348397 prefixEnd_348397 79508942037590501704559 := by
  unfold tailWord_348397
  simp only [CollatzResearch.WordTrace]
  refine ⟨12707082518824645315555445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8471388345883096877036963 12707082518824645315555445)
  ·
    refine ⟨1191288986139810498333323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12707082518824645315555445 1191288986139810498333323)
    ·
      refine ⟨1786933479209715747499985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1191288986139810498333323 1786933479209715747499985)
      ·
        refine ⟨1340200109407286810624989, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1786933479209715747499985 1340200109407286810624989)
        ·
          refine ⟨502575041027732553984371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1340200109407286810624989 502575041027732553984371)
          ·
            refine ⟨753862561541598830976557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502575041027732553984371 753862561541598830976557)
            ·
              refine ⟨282698460578099561616209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 753862561541598830976557 282698460578099561616209)
              ·
                refine ⟨212023845433574671212157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 282698460578099561616209 212023845433574671212157)
                ·
                  refine ⟨79508942037590501704559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212023845433574671212157 79508942037590501704559)
                  ·
                    rfl

theorem cell21_348397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 2, 3, 1, 3, 2, 3].length) (baseStart_348397 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348397 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348397 prefixEnd_348397 := by exact prefixLift 348397
  have htrace : WordTrace (prefixWord ++ tailWord_348397) baseStart_348397 baseEnd_348397 := by
    simpa [prefixWord, tailWord_348397, baseEnd_348397] using wordTrace_append hprefix tailTrace_348397
  have hstable : (prefixWord ++ tailWord_348397).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348397).length < 2 ^ (prefixWord ++ tailWord_348397).sum := by decide
  have hdescent : baseEnd_348397 < baseStart_348397 := by decide
  rcases family_descends (prefixWord ++ tailWord_348397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348456 : List Nat := [2, 1, 5, 1, 3, 1, 1, 4, 3]
def baseStart_348456 : Nat := 118140960795 + 348456 * 2 ^ 59
def prefixEnd_348456 : Nat := 4983230072969 + 3 ^ 40 * 348456 * 2
def baseEnd_348456 : Nat := 79522406641419510221105

theorem tailTrace_348456 : CollatzResearch.WordTrace tailWord_348456 prefixEnd_348456 79522406641419510221105 := by
  unfold tailWord_348456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6354617212805449195976611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8472822950407265594635481 6354617212805449195976611)
  ·
    refine ⟨9531925819208173793964917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6354617212805449195976611 9531925819208173793964917)
    ·
      refine ⟨893618045550766293184211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9531925819208173793964917 893618045550766293184211)
      ·
        refine ⟨1340427068326149439776317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 893618045550766293184211 1340427068326149439776317)
        ·
          refine ⟨502660150622306039916119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1340427068326149439776317 502660150622306039916119)
          ·
            refine ⟨753990225933459059874179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 502660150622306039916119 753990225933459059874179)
            ·
              refine ⟨1130985338900188589811269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 753990225933459059874179 1130985338900188589811269)
              ·
                refine ⟨212059751043785360589613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1130985338900188589811269 212059751043785360589613)
                ·
                  refine ⟨79522406641419510221105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212059751043785360589613 79522406641419510221105)
                  ·
                    rfl

theorem cell21_348456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 3, 1, 1, 4, 3].length) (baseStart_348456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348456 prefixEnd_348456 := by exact prefixLift 348456
  have htrace : WordTrace (prefixWord ++ tailWord_348456) baseStart_348456 baseEnd_348456 := by
    simpa [prefixWord, tailWord_348456, baseEnd_348456] using wordTrace_append hprefix tailTrace_348456
  have hstable : (prefixWord ++ tailWord_348456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348456).length < 2 ^ (prefixWord ++ tailWord_348456).sum := by decide
  have hdescent : baseEnd_348456 < baseStart_348456 := by decide
  rcases family_descends (prefixWord ++ tailWord_348456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348566 : List Nat := [5, 3, 1, 2, 1, 2, 1, 1, 5]
def baseStart_348566 : Nat := 118140960795 + 348566 * 2 ^ 59
def prefixEnd_348566 : Nat := 4983230072969 + 3 ^ 40 * 348566 * 2
def baseEnd_348566 : Nat := 79547510140083763387547

theorem tailTrace_348566 : CollatzResearch.WordTrace tailWord_348566 prefixEnd_348566 79547510140083763387547 := by
  unfold tailWord_348566
  simp only [CollatzResearch.WordTrace]
  refine ⟨794577903450774198653597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8475497636808258118971701 794577903450774198653597)
  ·
    refine ⟨297966713794040324495099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 794577903450774198653597 297966713794040324495099)
    ·
      refine ⟨446950070691060486742649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 297966713794040324495099 446950070691060486742649)
      ·
        refine ⟨335212553018295365056987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 446950070691060486742649 335212553018295365056987)
        ·
          refine ⟨502818829527443047585481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 335212553018295365056987 502818829527443047585481)
          ·
            refine ⟨377114122145582285689111, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 502818829527443047585481 377114122145582285689111)
            ·
              refine ⟨565671183218373428533667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377114122145582285689111 565671183218373428533667)
              ·
                refine ⟨848506774827560142800501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 565671183218373428533667 848506774827560142800501)
                ·
                  refine ⟨79547510140083763387547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848506774827560142800501 79547510140083763387547)
                  ·
                    rfl

theorem cell21_348566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 2, 1, 2, 1, 1, 5].length) (baseStart_348566 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348566 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348566 prefixEnd_348566 := by exact prefixLift 348566
  have htrace : WordTrace (prefixWord ++ tailWord_348566) baseStart_348566 baseEnd_348566 := by
    simpa [prefixWord, tailWord_348566, baseEnd_348566] using wordTrace_append hprefix tailTrace_348566
  have hstable : (prefixWord ++ tailWord_348566).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348566).length < 2 ^ (prefixWord ++ tailWord_348566).sum := by decide
  have hdescent : baseEnd_348566 < baseStart_348566 := by decide
  rcases family_descends (prefixWord ++ tailWord_348566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348633 : List Nat := [1, 2, 1, 2, 4, 1, 2, 3, 5]
def baseStart_348633 : Nat := 118140960795 + 348633 * 2 ^ 59
def prefixEnd_348633 : Nat := 4983230072969 + 3 ^ 40 * 348633 * 2
def baseEnd_348633 : Nat := 79562800452906535770743

theorem tailTrace_348633 : CollatzResearch.WordTrace tailWord_348633 prefixEnd_348633 79562800452906535770743 := by
  unfold tailWord_348633
  simp only [CollatzResearch.WordTrace]
  refine ⟨12715690145969657621146553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8477126763979771747431035 12715690145969657621146553)
  ·
    refine ⟨9536767609477243215859915, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12715690145969657621146553 9536767609477243215859915)
    ·
      refine ⟨14305151414215864823789873, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9536767609477243215859915 14305151414215864823789873)
      ·
        refine ⟨10728863560661898617842405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 14305151414215864823789873 10728863560661898617842405)
        ·
          refine ⟨2011661917624105990845451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10728863560661898617842405 2011661917624105990845451)
          ·
            refine ⟨3017492876436158986268177, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2011661917624105990845451 3017492876436158986268177)
            ·
              refine ⟨2263119657327119239701133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3017492876436158986268177 2263119657327119239701133)
              ·
                refine ⟨848669871497669714887925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2263119657327119239701133 848669871497669714887925)
                ·
                  refine ⟨79562800452906535770743, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848669871497669714887925 79562800452906535770743)
                  ·
                    rfl

theorem cell21_348633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 3, 5].length) (baseStart_348633 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348633 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348633 prefixEnd_348633 := by exact prefixLift 348633
  have htrace : WordTrace (prefixWord ++ tailWord_348633) baseStart_348633 baseEnd_348633 := by
    simpa [prefixWord, tailWord_348633, baseEnd_348633] using wordTrace_append hprefix tailTrace_348633
  have hstable : (prefixWord ++ tailWord_348633).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348633).length < 2 ^ (prefixWord ++ tailWord_348633).sum := by decide
  have hdescent : baseEnd_348633 < baseStart_348633 := by decide
  rcases family_descends (prefixWord ++ tailWord_348633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348650 : List Nat := [3, 1, 3, 1, 3, 2, 1, 2, 5]
def baseStart_348650 : Nat := 118140960795 + 348650 * 2 ^ 59
def prefixEnd_348650 : Nat := 4983230072969 + 3 ^ 40 * 348650 * 2
def baseEnd_348650 : Nat := 79566680084518283987375

theorem tailTrace_348650 : CollatzResearch.WordTrace tailWord_348650 prefixEnd_348650 79566680084518283987375 := by
  unfold tailWord_348650
  simp only [CollatzResearch.WordTrace]
  refine ⟨3179077546727017381128851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8477540124605379683010269 3179077546727017381128851)
  ·
    refine ⟨4768616320090526071693277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3179077546727017381128851 4768616320090526071693277)
    ·
      refine ⟨1788231120033947276884979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4768616320090526071693277 1788231120033947276884979)
      ·
        refine ⟨2682346680050920915327469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1788231120033947276884979 2682346680050920915327469)
        ·
          refine ⟨1005880005019095343247801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2682346680050920915327469 1005880005019095343247801)
          ·
            refine ⟨754410003764321507435851, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1005880005019095343247801 754410003764321507435851)
            ·
              refine ⟨1131615005646482261153777, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 754410003764321507435851 1131615005646482261153777)
              ·
                refine ⟨848711254234861695865333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131615005646482261153777 848711254234861695865333)
                ·
                  refine ⟨79566680084518283987375, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848711254234861695865333 79566680084518283987375)
                  ·
                    rfl

theorem cell21_348650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 3, 2, 1, 2, 5].length) (baseStart_348650 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348650 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348650 prefixEnd_348650 := by exact prefixLift 348650
  have htrace : WordTrace (prefixWord ++ tailWord_348650) baseStart_348650 baseEnd_348650 := by
    simpa [prefixWord, tailWord_348650, baseEnd_348650] using wordTrace_append hprefix tailTrace_348650
  have hstable : (prefixWord ++ tailWord_348650).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348650).length < 2 ^ (prefixWord ++ tailWord_348650).sum := by decide
  have hdescent : baseEnd_348650 < baseStart_348650 := by decide
  rcases family_descends (prefixWord ++ tailWord_348650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348709 : List Nat := [1, 3, 1, 2, 2, 1, 4, 2, 5]
def baseStart_348709 : Nat := 118140960795 + 348709 * 2 ^ 59
def prefixEnd_348709 : Nat := 4983230072969 + 3 ^ 40 * 348709 * 2
def baseEnd_348709 : Nat := 79580144688347292503921

theorem tailTrace_348709 : CollatzResearch.WordTrace tailWord_348709 prefixEnd_348709 79580144688347292503921 := by
  unfold tailWord_348709
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718462093694322600913181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8478974729129548400608787 12718462093694322600913181)
  ·
    refine ⟨4769423285135370975342443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12718462093694322600913181 4769423285135370975342443)
    ·
      refine ⟨7154134927703056463013665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4769423285135370975342443 7154134927703056463013665)
      ·
        refine ⟨5365601195777292347260249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7154134927703056463013665 5365601195777292347260249)
        ·
          refine ⟨4024200896832969260445187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5365601195777292347260249 4024200896832969260445187)
          ·
            refine ⟨6036301345249453890667781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024200896832969260445187 6036301345249453890667781)
            ·
              refine ⟨1131806502234272604500209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6036301345249453890667781 1131806502234272604500209)
              ·
                refine ⟨848854876675704453375157, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1131806502234272604500209 848854876675704453375157)
                ·
                  refine ⟨79580144688347292503921, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 848854876675704453375157 79580144688347292503921)
                  ·
                    rfl

theorem cell21_348709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 4, 2, 5].length) (baseStart_348709 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348709 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348709 prefixEnd_348709 := by exact prefixLift 348709
  have htrace : WordTrace (prefixWord ++ tailWord_348709) baseStart_348709 baseEnd_348709 := by
    simpa [prefixWord, tailWord_348709, baseEnd_348709] using wordTrace_append hprefix tailTrace_348709
  have hstable : (prefixWord ++ tailWord_348709).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348709).length < 2 ^ (prefixWord ++ tailWord_348709).sum := by decide
  have hdescent : baseEnd_348709 < baseStart_348709 := by decide
  rcases family_descends (prefixWord ++ tailWord_348709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348712 : List Nat := [2, 1, 5, 2, 1, 1, 4, 5]
def baseStart_348712 : Nat := 118140960795 + 348712 * 2 ^ 59
def prefixEnd_348712 : Nat := 4983230072969 + 3 ^ 40 * 348712 * 2
def baseEnd_348712 : Nat := 26526943109739984651305

theorem tailTrace_348712 : CollatzResearch.WordTrace tailWord_348712 prefixEnd_348712 26526943109739984651305 := by
  unfold tailWord_348712
  simp only [CollatzResearch.WordTrace]
  refine ⟨6359285756341727056636195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8479047675122302742181593 6359285756341727056636195)
  ·
    refine ⟨9538928634512590584954293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6359285756341727056636195 9538928634512590584954293)
    ·
      refine ⟨894274559485555367339465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 9538928634512590584954293 894274559485555367339465)
      ·
        refine ⟨670705919614166525504599, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 894274559485555367339465 670705919614166525504599)
        ·
          refine ⟨1006058879421249788256899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 670705919614166525504599 1006058879421249788256899)
          ·
            refine ⟨1509088319131874682385349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006058879421249788256899 1509088319131874682385349)
            ·
              refine ⟨282954059837226502947253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1509088319131874682385349 282954059837226502947253)
              ·
                refine ⟨26526943109739984651305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 282954059837226502947253 26526943109739984651305)
                ·
                  rfl

theorem cell21_348712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 4, 5].length) (baseStart_348712 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348712 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348712 prefixEnd_348712 := by exact prefixLift 348712
  have htrace : WordTrace (prefixWord ++ tailWord_348712) baseStart_348712 baseEnd_348712 := by
    simpa [prefixWord, tailWord_348712, baseEnd_348712] using wordTrace_append hprefix tailTrace_348712
  have hstable : (prefixWord ++ tailWord_348712).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348712).length < 2 ^ (prefixWord ++ tailWord_348712).sum := by decide
  have hdescent : baseEnd_348712 < baseStart_348712 := by decide
  rcases family_descends (prefixWord ++ tailWord_348712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348723 : List Nat := [1, 1, 1, 2, 4, 2, 1, 1, 8]
def baseStart_348723 : Nat := 118140960795 + 348723 * 2 ^ 59
def prefixEnd_348723 : Nat := 4983230072969 + 3 ^ 40 * 348723 * 2
def baseEnd_348723 : Nat := 79583339679086379270559

theorem tailTrace_348723 : CollatzResearch.WordTrace tailWord_348723 prefixEnd_348723 79583339679086379270559 := by
  unfold tailWord_348723
  simp only [CollatzResearch.WordTrace]
  refine ⟨12718972715643602991922823, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8479315143762401994615215 12718972715643602991922823)
  ·
    refine ⟨19078459073465404487884235, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12718972715643602991922823 19078459073465404487884235)
    ·
      refine ⟨28617688610198106731826353, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19078459073465404487884235 28617688610198106731826353)
      ·
        refine ⟨21463266457648580048869765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28617688610198106731826353 21463266457648580048869765)
        ·
          refine ⟨4024362460809108759163081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 21463266457648580048869765 4024362460809108759163081)
          ·
            refine ⟨3018271845606831569372311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4024362460809108759163081 3018271845606831569372311)
            ·
              refine ⟨4527407768410247354058467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3018271845606831569372311 4527407768410247354058467)
              ·
                refine ⟨6791111652615371031087701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4527407768410247354058467 6791111652615371031087701)
                ·
                  refine ⟨79583339679086379270559, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6791111652615371031087701 79583339679086379270559)
                  ·
                    rfl

theorem cell21_348723_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 4, 2, 1, 1, 8].length) (baseStart_348723 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348723 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348723 prefixEnd_348723 := by exact prefixLift 348723
  have htrace : WordTrace (prefixWord ++ tailWord_348723) baseStart_348723 baseEnd_348723 := by
    simpa [prefixWord, tailWord_348723, baseEnd_348723] using wordTrace_append hprefix tailTrace_348723
  have hstable : (prefixWord ++ tailWord_348723).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348723).length < 2 ^ (prefixWord ++ tailWord_348723).sum := by decide
  have hdescent : baseEnd_348723 < baseStart_348723 := by decide
  rcases family_descends (prefixWord ++ tailWord_348723) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348757 : List Nat := [1, 3, 2, 2, 1, 1, 6, 1, 4]
def baseStart_348757 : Nat := 118140960795 + 348757 * 2 ^ 59
def prefixEnd_348757 : Nat := 4983230072969 + 3 ^ 40 * 348757 * 2
def baseEnd_348757 : Nat := 79591098942309875703823

theorem tailTrace_348757 : CollatzResearch.WordTrace tailWord_348757 prefixEnd_348757 79591098942309875703823 := by
  unfold tailWord_348757
  simp only [CollatzResearch.WordTrace]
  refine ⟨12720212797520426798660525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8480141865013617865773683 12720212797520426798660525)
  ·
    refine ⟨4770079799070160049497697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12720212797520426798660525 4770079799070160049497697)
    ·
      refine ⟨3577559849302620037123273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4770079799070160049497697 3577559849302620037123273)
      ·
        refine ⟨2683169886976965027842455, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3577559849302620037123273 2683169886976965027842455)
        ·
          refine ⟨4024754830465447541763683, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683169886976965027842455 4024754830465447541763683)
          ·
            refine ⟨6037132245698171312645525, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4024754830465447541763683 6037132245698171312645525)
            ·
              refine ⟨282990574017101780280259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 6037132245698171312645525 282990574017101780280259)
              ·
                refine ⟨424485861025652670420389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 282990574017101780280259 424485861025652670420389)
                ·
                  refine ⟨79591098942309875703823, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424485861025652670420389 79591098942309875703823)
                  ·
                    rfl

theorem cell21_348757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 6, 1, 4].length) (baseStart_348757 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348757 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348757 prefixEnd_348757 := by exact prefixLift 348757
  have htrace : WordTrace (prefixWord ++ tailWord_348757) baseStart_348757 baseEnd_348757 := by
    simpa [prefixWord, tailWord_348757, baseEnd_348757] using wordTrace_append hprefix tailTrace_348757
  have hstable : (prefixWord ++ tailWord_348757).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348757).length < 2 ^ (prefixWord ++ tailWord_348757).sum := by decide
  have hdescent : baseEnd_348757 < baseStart_348757 := by decide
  rcases family_descends (prefixWord ++ tailWord_348757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348861 : List Nat := [1, 4, 1, 2, 1, 3, 1, 3, 5]
def baseStart_348861 : Nat := 118140960795 + 348861 * 2 ^ 59
def prefixEnd_348861 : Nat := 4983230072969 + 3 ^ 40 * 348861 * 2
def baseEnd_348861 : Nat := 79614833159228805970277

theorem tailTrace_348861 : CollatzResearch.WordTrace tailWord_348861 prefixEnd_348861 79614833159228805970277 := by
  unfold tailWord_348861
  simp only [CollatzResearch.WordTrace]
  refine ⟨12724005989143652560446437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8482670659429101706964291 12724005989143652560446437)
  ·
    refine ⟨2385751122964434855083707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12724005989143652560446437 2385751122964434855083707)
    ·
      refine ⟨3578626684446652282625561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2385751122964434855083707 3578626684446652282625561)
      ·
        refine ⟨2683970013334989211969171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3578626684446652282625561 2683970013334989211969171)
        ·
          refine ⟨4025955020002483817953757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2683970013334989211969171 4025955020002483817953757)
          ·
            refine ⟨1509733132500931431732659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4025955020002483817953757 1509733132500931431732659)
            ·
              refine ⟨2264599698751397147598989, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1509733132500931431732659 2264599698751397147598989)
              ·
                refine ⟨849224887031773930349621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2264599698751397147598989 849224887031773930349621)
                ·
                  refine ⟨79614833159228805970277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 849224887031773930349621 79614833159228805970277)
                  ·
                    rfl

theorem cell21_348861_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 3, 1, 3, 5].length) (baseStart_348861 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348861 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348861 prefixEnd_348861 := by exact prefixLift 348861
  have htrace : WordTrace (prefixWord ++ tailWord_348861) baseStart_348861 baseEnd_348861 := by
    simpa [prefixWord, tailWord_348861, baseEnd_348861] using wordTrace_append hprefix tailTrace_348861
  have hstable : (prefixWord ++ tailWord_348861).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348861).length < 2 ^ (prefixWord ++ tailWord_348861).sum := by decide
  have hdescent : baseEnd_348861 < baseStart_348861 := by decide
  rcases family_descends (prefixWord ++ tailWord_348861) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348895 : List Nat := [1, 1, 2, 3, 2, 5, 1, 3, 3]
def baseStart_348895 : Nat := 118140960795 + 348895 * 2 ^ 59
def prefixEnd_348895 : Nat := 4983230072969 + 3 ^ 40 * 348895 * 2
def baseEnd_348895 : Nat := 79622592422452302403541

theorem tailTrace_348895 : CollatzResearch.WordTrace tailWord_348895 prefixEnd_348895 79622592422452302403541 := by
  unfold tailWord_348895
  simp only [CollatzResearch.WordTrace]
  refine ⟨12725246071020476367184139, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8483497380680317578122759 12725246071020476367184139)
  ·
    refine ⟨19087869106530714550776209, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12725246071020476367184139 19087869106530714550776209)
    ·
      refine ⟨14315901829898035913082157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19087869106530714550776209 14315901829898035913082157)
      ·
        refine ⟨5368463186211763467405809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14315901829898035913082157 5368463186211763467405809)
        ·
          refine ⟨4026347389658822600554357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5368463186211763467405809 4026347389658822600554357)
          ·
            refine ⟨377470067780514618801971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4026347389658822600554357 377470067780514618801971)
            ·
              refine ⟨566205101670771928202957, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377470067780514618801971 566205101670771928202957)
              ·
                refine ⟨212326913126539473076109, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566205101670771928202957 212326913126539473076109)
                ·
                  refine ⟨79622592422452302403541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212326913126539473076109 79622592422452302403541)
                  ·
                    rfl

theorem cell21_348895_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 2, 5, 1, 3, 3].length) (baseStart_348895 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348895 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348895 prefixEnd_348895 := by exact prefixLift 348895
  have htrace : WordTrace (prefixWord ++ tailWord_348895) baseStart_348895 baseEnd_348895 := by
    simpa [prefixWord, tailWord_348895, baseEnd_348895] using wordTrace_append hprefix tailTrace_348895
  have hstable : (prefixWord ++ tailWord_348895).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348895).length < 2 ^ (prefixWord ++ tailWord_348895).sum := by decide
  have hdescent : baseEnd_348895 < baseStart_348895 := by decide
  rcases family_descends (prefixWord ++ tailWord_348895) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348926 : List Nat := [4, 2, 2, 1, 2, 1, 4, 1, 4]
def baseStart_348926 : Nat := 118140960795 + 348926 * 2 ^ 59
def prefixEnd_348926 : Nat := 4983230072969 + 3 ^ 40 * 348926 * 2
def baseEnd_348926 : Nat := 79629667044803137386811

theorem tailTrace_348926 : CollatzResearch.WordTrace tailWord_348926 prefixEnd_348926 79629667044803137386811 := by
  unfold tailWord_348926
  simp only [CollatzResearch.WordTrace]
  refine ⟨1590797091738521082695329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8484251155938779107708421 1590797091738521082695329)
  ·
    refine ⟨1193097818803890812021497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1590797091738521082695329 1193097818803890812021497)
    ·
      refine ⟨894823364102918109016123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1193097818803890812021497 894823364102918109016123)
      ·
        refine ⟨1342235046154377163524185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 894823364102918109016123 1342235046154377163524185)
        ·
          refine ⟨1006676284615782872643139, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1342235046154377163524185 1006676284615782872643139)
          ·
            refine ⟨1510014426923674308964709, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1006676284615782872643139 1510014426923674308964709)
            ·
              refine ⟨283127705048188932930883, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1510014426923674308964709 283127705048188932930883)
              ·
                refine ⟨424691557572283399396325, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283127705048188932930883 424691557572283399396325)
                ·
                  refine ⟨79629667044803137386811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424691557572283399396325 79629667044803137386811)
                  ·
                    rfl

theorem cell21_348926_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_348926 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348926 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348926 prefixEnd_348926 := by exact prefixLift 348926
  have htrace : WordTrace (prefixWord ++ tailWord_348926) baseStart_348926 baseEnd_348926 := by
    simpa [prefixWord, tailWord_348926, baseEnd_348926] using wordTrace_append hprefix tailTrace_348926
  have hstable : (prefixWord ++ tailWord_348926).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348926).length < 2 ^ (prefixWord ++ tailWord_348926).sum := by decide
  have hdescent : baseEnd_348926 < baseStart_348926 := by decide
  rcases family_descends (prefixWord ++ tailWord_348926) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_348954 : List Nat := [3, 1, 1, 3, 2, 1, 2, 5, 3]
def baseStart_348954 : Nat := 118140960795 + 348954 * 2 ^ 59
def prefixEnd_348954 : Nat := 4983230072969 + 3 ^ 40 * 348954 * 2
def baseEnd_348954 : Nat := 79636057026281310920087

theorem tailTrace_348954 : CollatzResearch.WordTrace tailWord_348954 prefixEnd_348954 79636057026281310920087 := by
  unfold tailWord_348954
  simp only [CollatzResearch.WordTrace]
  refine ⟨3181849494451682360895479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8484931985204486295721277 3181849494451682360895479)
  ·
    refine ⟨4772774241677523541343219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3181849494451682360895479 4772774241677523541343219)
    ·
      refine ⟨7159161362516285312014829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4772774241677523541343219 7159161362516285312014829)
      ·
        refine ⟨2684685510943606992005561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7159161362516285312014829 2684685510943606992005561)
        ·
          refine ⟨2013514133207705244004171, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2684685510943606992005561 2013514133207705244004171)
          ·
            refine ⟨3020271199811557866006257, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2013514133207705244004171 3020271199811557866006257)
            ·
              refine ⟨2265203399858668399504693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3020271199811557866006257 2265203399858668399504693)
              ·
                refine ⟨212362818736750162453565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2265203399858668399504693 212362818736750162453565)
                ·
                  refine ⟨79636057026281310920087, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212362818736750162453565 79636057026281310920087)
                  ·
                    rfl

theorem cell21_348954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 1, 2, 5, 3].length) (baseStart_348954 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_348954 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_348954 prefixEnd_348954 := by exact prefixLift 348954
  have htrace : WordTrace (prefixWord ++ tailWord_348954) baseStart_348954 baseEnd_348954 := by
    simpa [prefixWord, tailWord_348954, baseEnd_348954] using wordTrace_append hprefix tailTrace_348954
  have hstable : (prefixWord ++ tailWord_348954).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_348954).length < 2 ^ (prefixWord ++ tailWord_348954).sum := by decide
  have hdescent : baseEnd_348954 < baseStart_348954 := by decide
  rcases family_descends (prefixWord ++ tailWord_348954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349078 : List Nat := [5, 3, 1, 1, 1, 1, 2, 1, 6]
def baseStart_349078 : Nat := 118140960795 + 349078 * 2 ^ 59
def prefixEnd_349078 : Nat := 4983230072969 + 3 ^ 40 * 349078 * 2
def baseEnd_349078 : Nat := 79664355515684650853167

theorem tailTrace_349078 : CollatzResearch.WordTrace tailWord_349078 prefixEnd_349078 79664355515684650853167 := by
  unfold tailWord_349078
  simp only [CollatzResearch.WordTrace]
  refine ⟨795745039334843663818493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8487947086238332414063925 795745039334843663818493)
  ·
    refine ⟨298404389750566373931935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 795745039334843663818493 298404389750566373931935)
    ·
      refine ⟨447606584625849560897903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 298404389750566373931935 447606584625849560897903)
      ·
        refine ⟨671409876938774341346855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 447606584625849560897903 671409876938774341346855)
        ·
          refine ⟨1007114815408161512020283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671409876938774341346855 1007114815408161512020283)
          ·
            refine ⟨1510672223112242268030425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1007114815408161512020283 1510672223112242268030425)
            ·
              refine ⟨1133004167334181701022819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1510672223112242268030425 1133004167334181701022819)
              ·
                refine ⟨1699506251001272551534229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133004167334181701022819 1699506251001272551534229)
                ·
                  refine ⟨79664355515684650853167, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1699506251001272551534229 79664355515684650853167)
                  ·
                    rfl

theorem cell21_349078_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 2, 1, 6].length) (baseStart_349078 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349078 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349078 prefixEnd_349078 := by exact prefixLift 349078
  have htrace : WordTrace (prefixWord ++ tailWord_349078) baseStart_349078 baseEnd_349078 := by
    simpa [prefixWord, tailWord_349078, baseEnd_349078] using wordTrace_append hprefix tailTrace_349078
  have hstable : (prefixWord ++ tailWord_349078).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349078).length < 2 ^ (prefixWord ++ tailWord_349078).sum := by decide
  have hdescent : baseEnd_349078 < baseStart_349078 := by decide
  rcases family_descends (prefixWord ++ tailWord_349078) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349095 : List Nat := [1, 1, 6, 1, 4, 1, 2, 1, 4]
def baseStart_349095 : Nat := 118140960795 + 349095 * 2 ^ 59
def prefixEnd_349095 : Nat := 4983230072969 + 3 ^ 40 * 349095 * 2
def baseEnd_349095 : Nat := 79668235147296399069799

theorem tailTrace_349095 : CollatzResearch.WordTrace tailWord_349095 prefixEnd_349095 79668235147296399069799 := by
  unfold tailWord_349095
  simp only [CollatzResearch.WordTrace]
  refine ⟨12732540670295910524464739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8488360446863940349643159 12732540670295910524464739)
  ·
    refine ⟨19098811005443865786697109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12732540670295910524464739 19098811005443865786697109)
    ·
      refine ⟨895256765880181208751427, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19098811005443865786697109 895256765880181208751427)
      ·
        refine ⟨1342885148820271813127141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 895256765880181208751427 1342885148820271813127141)
        ·
          refine ⟨251790965403800964961339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 1342885148820271813127141 251790965403800964961339)
          ·
            refine ⟨377686448105701447442009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251790965403800964961339 377686448105701447442009)
            ·
              refine ⟨283264836079276085581507, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377686448105701447442009 283264836079276085581507)
              ·
                refine ⟨424897254118914128372261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283264836079276085581507 424897254118914128372261)
                ·
                  refine ⟨79668235147296399069799, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 424897254118914128372261 79668235147296399069799)
                  ·
                    rfl

theorem cell21_349095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 4, 1, 2, 1, 4].length) (baseStart_349095 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349095 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349095 prefixEnd_349095 := by exact prefixLift 349095
  have htrace : WordTrace (prefixWord ++ tailWord_349095) baseStart_349095 baseEnd_349095 := by
    simpa [prefixWord, tailWord_349095, baseEnd_349095] using wordTrace_append hprefix tailTrace_349095
  have hstable : (prefixWord ++ tailWord_349095).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349095).length < 2 ^ (prefixWord ++ tailWord_349095).sum := by decide
  have hdescent : baseEnd_349095 < baseStart_349095 := by decide
  rcases family_descends (prefixWord ++ tailWord_349095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349126 : List Nat := [6, 1, 3, 1, 2, 8]
def baseStart_349126 : Nat := 118140960795 + 349126 * 2 ^ 59
def prefixEnd_349126 : Nat := 4983230072969 + 3 ^ 40 * 349126 * 2
def baseEnd_349126 : Nat := 2950937398875823483447

theorem tailTrace_349126 : CollatzResearch.WordTrace tailWord_349126 prefixEnd_349126 2950937398875823483447 := by
  unfold tailWord_349126
  simp only [CollatzResearch.WordTrace]
  refine ⟨397927229161987588088851, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 8489114222122401879228821 397927229161987588088851)
  ·
    refine ⟨596890843742981382133277, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 397927229161987588088851 596890843742981382133277)
    ·
      refine ⟨223834066403618018299979, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 596890843742981382133277 223834066403618018299979)
      ·
        refine ⟨335751099605427027449969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 223834066403618018299979 335751099605427027449969)
        ·
          refine ⟨251813324704070270587477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 335751099605427027449969 251813324704070270587477)
          ·
            refine ⟨2950937398875823483447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 8 251813324704070270587477 2950937398875823483447)
            ·
              rfl

theorem cell21_349126_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 3, 1, 2, 8].length) (baseStart_349126 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349126 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349126 prefixEnd_349126 := by exact prefixLift 349126
  have htrace : WordTrace (prefixWord ++ tailWord_349126) baseStart_349126 baseEnd_349126 := by
    simpa [prefixWord, tailWord_349126, baseEnd_349126] using wordTrace_append hprefix tailTrace_349126
  have hstable : (prefixWord ++ tailWord_349126).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349126).length < 2 ^ (prefixWord ++ tailWord_349126).sum := by decide
  have hdescent : baseEnd_349126 < baseStart_349126 := by decide
  rcases family_descends (prefixWord ++ tailWord_349126) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349140 : List Nat := [2, 4, 1, 2, 1, 4, 2, 2, 3]
def baseStart_349140 : Nat := 118140960795 + 349140 * 2 ^ 59
def prefixEnd_349140 : Nat := 4983230072969 + 3 ^ 40 * 349140 * 2
def baseEnd_349140 : Nat := 79678504760386320819707

theorem tailTrace_349140 : CollatzResearch.WordTrace tailWord_349140 prefixEnd_349140 79678504760386320819707 := by
  unfold tailWord_349140
  simp only [CollatzResearch.WordTrace]
  refine ⟨6367090977566441604926437, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8489454636755255473235249 6367090977566441604926437)
  ·
    refine ⟨1193829558293707800923707, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 6367090977566441604926437 1193829558293707800923707)
    ·
      refine ⟨1790744337440561701385561, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1193829558293707800923707 1790744337440561701385561)
      ·
        refine ⟨1343058253080421276039171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1790744337440561701385561 1343058253080421276039171)
        ·
          refine ⟨2014587379620631914058757, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1343058253080421276039171 2014587379620631914058757)
          ·
            refine ⟨377735133678868483886017, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 2014587379620631914058757 377735133678868483886017)
            ·
              refine ⟨283301350259151362914513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 377735133678868483886017 283301350259151362914513)
              ·
                refine ⟨212476012694363522185885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283301350259151362914513 212476012694363522185885)
                ·
                  refine ⟨79678504760386320819707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212476012694363522185885 79678504760386320819707)
                  ·
                    rfl

theorem cell21_349140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 4, 2, 2, 3].length) (baseStart_349140 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349140 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349140 prefixEnd_349140 := by exact prefixLift 349140
  have htrace : WordTrace (prefixWord ++ tailWord_349140) baseStart_349140 baseEnd_349140 := by
    simpa [prefixWord, tailWord_349140, baseEnd_349140] using wordTrace_append hprefix tailTrace_349140
  have hstable : (prefixWord ++ tailWord_349140).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349140).length < 2 ^ (prefixWord ++ tailWord_349140).sum := by decide
  have hdescent : baseEnd_349140 < baseStart_349140 := by decide
  rcases family_descends (prefixWord ++ tailWord_349140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349151 : List Nat := [1, 1, 2, 3, 5, 2, 1, 6]
def baseStart_349151 : Nat := 118140960795 + 349151 * 2 ^ 59
def prefixEnd_349151 : Nat := 4983230072969 + 3 ^ 40 * 349151 * 2
def baseEnd_349151 : Nat := 26560338370084248712117

theorem tailTrace_349151 : CollatzResearch.WordTrace tailWord_349151 prefixEnd_349151 26560338370084248712117 := by
  unfold tailWord_349151
  simp only [CollatzResearch.WordTrace]
  refine ⟨12734583158093032088503307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8489722105395354725668871 12734583158093032088503307)
  ·
    refine ⟨19101874737139548132754961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12734583158093032088503307 19101874737139548132754961)
    ·
      refine ⟨14326406052854661099566221, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19101874737139548132754961 14326406052854661099566221)
      ·
        refine ⟨5372402269820497912337333, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14326406052854661099566221 5372402269820497912337333)
        ·
          refine ⟨503662712795671679281625, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 5372402269820497912337333 503662712795671679281625)
          ·
            refine ⟨377747034596753759461219, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 503662712795671679281625 377747034596753759461219)
            ·
              refine ⟨566620551895130639191829, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377747034596753759461219 566620551895130639191829)
              ·
                refine ⟨26560338370084248712117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 566620551895130639191829 26560338370084248712117)
                ·
                  rfl

theorem cell21_349151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 5, 2, 1, 6].length) (baseStart_349151 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349151 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349151 prefixEnd_349151 := by exact prefixLift 349151
  have htrace : WordTrace (prefixWord ++ tailWord_349151) baseStart_349151 baseEnd_349151 := by
    simpa [prefixWord, tailWord_349151, baseEnd_349151] using wordTrace_append hprefix tailTrace_349151
  have hstable : (prefixWord ++ tailWord_349151).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349151).length < 2 ^ (prefixWord ++ tailWord_349151).sum := by decide
  have hdescent : baseEnd_349151 < baseStart_349151 := by decide
  rcases family_descends (prefixWord ++ tailWord_349151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349196 : List Nat := [2, 2, 1, 2, 3, 2, 3, 2, 4]
def baseStart_349196 : Nat := 118140960795 + 349196 * 2 ^ 59
def prefixEnd_349196 : Nat := 4983230072969 + 3 ^ 40 * 349196 * 2
def baseEnd_349196 : Nat := 79691284723342667886259

theorem tailTrace_349196 : CollatzResearch.WordTrace tailWord_349196 prefixEnd_349196 79691284723342667886259 := by
  unfold tailWord_349196
  simp only [CollatzResearch.WordTrace]
  refine ⟨6368112221465002386945721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8490816295286669849260961 6368112221465002386945721)
  ·
    refine ⟨4776084166098751790209291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6368112221465002386945721 4776084166098751790209291)
    ·
      refine ⟨7164126249148127685313937, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4776084166098751790209291 7164126249148127685313937)
      ·
        refine ⟨5373094686861095763985453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7164126249148127685313937 5373094686861095763985453)
        ·
          refine ⟨2014910507572910911494545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5373094686861095763985453 2014910507572910911494545)
          ·
            refine ⟨1511182880679683183620909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2014910507572910911494545 1511182880679683183620909)
            ·
              refine ⟨566693580254881193857841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1511182880679683183620909 566693580254881193857841)
              ·
                refine ⟨425020185191160895393381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 566693580254881193857841 425020185191160895393381)
                ·
                  refine ⟨79691284723342667886259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425020185191160895393381 79691284723342667886259)
                  ·
                    rfl

theorem cell21_349196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 3, 2, 3, 2, 4].length) (baseStart_349196 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349196 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349196 prefixEnd_349196 := by exact prefixLift 349196
  have htrace : WordTrace (prefixWord ++ tailWord_349196) baseStart_349196 baseEnd_349196 := by
    simpa [prefixWord, tailWord_349196, baseEnd_349196] using wordTrace_append hprefix tailTrace_349196
  have hstable : (prefixWord ++ tailWord_349196).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349196).length < 2 ^ (prefixWord ++ tailWord_349196).sum := by decide
  have hdescent : baseEnd_349196 < baseStart_349196 := by decide
  rcases family_descends (prefixWord ++ tailWord_349196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349255 : List Nat := [1, 1, 4, 1, 3, 2, 2, 1, 6]
def baseStart_349255 : Nat := 118140960795 + 349255 * 2 ^ 59
def prefixEnd_349255 : Nat := 4983230072969 + 3 ^ 40 * 349255 * 2
def baseEnd_349255 : Nat := 79704749327171676402805

theorem tailTrace_349255 : CollatzResearch.WordTrace tailWord_349255 prefixEnd_349255 79704749327171676402805 := by
  unfold tailWord_349255
  simp only [CollatzResearch.WordTrace]
  refine ⟨12738376349716257850289219, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8492250899810838566859479 12738376349716257850289219)
  ·
    refine ⟨19107564524574386775433829, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12738376349716257850289219 19107564524574386775433829)
    ·
      refine ⟨3582668348357697520393843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 19107564524574386775433829 3582668348357697520393843)
      ·
        refine ⟨5374002522536546280590765, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3582668348357697520393843 5374002522536546280590765)
        ·
          refine ⟨2015250945951204855221537, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5374002522536546280590765 2015250945951204855221537)
          ·
            refine ⟨1511438209463403641416153, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2015250945951204855221537 1511438209463403641416153)
            ·
              refine ⟨1133578657097552731062115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1511438209463403641416153 1133578657097552731062115)
              ·
                refine ⟨1700367985646329096593173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1133578657097552731062115 1700367985646329096593173)
                ·
                  refine ⟨79704749327171676402805, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1700367985646329096593173 79704749327171676402805)
                  ·
                    rfl

theorem cell21_349255_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 2, 2, 1, 6].length) (baseStart_349255 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349255 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349255 prefixEnd_349255 := by exact prefixLift 349255
  have htrace : WordTrace (prefixWord ++ tailWord_349255) baseStart_349255 baseEnd_349255 := by
    simpa [prefixWord, tailWord_349255, baseEnd_349255] using wordTrace_append hprefix tailTrace_349255
  have hstable : (prefixWord ++ tailWord_349255).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349255).length < 2 ^ (prefixWord ++ tailWord_349255).sum := by decide
  have hdescent : baseEnd_349255 < baseStart_349255 := by decide
  rcases family_descends (prefixWord ++ tailWord_349255) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349320 : List Nat := [2, 1, 3, 4, 3, 1, 1, 6]
def baseStart_349320 : Nat := 118140960795 + 349320 * 2 ^ 59
def prefixEnd_349320 : Nat := 4983230072969 + 3 ^ 40 * 349320 * 2
def baseEnd_349320 : Nat := 26573194404248669273113

theorem tailTrace_349320 : CollatzResearch.WordTrace tailWord_349320 prefixEnd_349320 26573194404248669273113 := by
  unfold tailWord_349320
  simp only [CollatzResearch.WordTrace]
  refine ⟨6370373547240386975702707, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8493831396320515967603609 6370373547240386975702707)
  ·
    refine ⟨9555560320860580463554061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6370373547240386975702707 9555560320860580463554061)
    ·
      refine ⟨3583335120322717673832773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 9555560320860580463554061 3583335120322717673832773)
      ·
        refine ⟨671875335060509563843645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3583335120322717673832773 671875335060509563843645)
        ·
          refine ⟨251953250647691086441367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 671875335060509563843645 251953250647691086441367)
          ·
            refine ⟨377929875971536629662051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 251953250647691086441367 377929875971536629662051)
            ·
              refine ⟨566894813957304944493077, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 377929875971536629662051 566894813957304944493077)
              ·
                refine ⟨26573194404248669273113, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 566894813957304944493077 26573194404248669273113)
                ·
                  rfl

theorem cell21_349320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 4, 3, 1, 1, 6].length) (baseStart_349320 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349320 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349320 prefixEnd_349320 := by exact prefixLift 349320
  have htrace : WordTrace (prefixWord ++ tailWord_349320) baseStart_349320 baseEnd_349320 := by
    simpa [prefixWord, tailWord_349320, baseEnd_349320] using wordTrace_append hprefix tailTrace_349320
  have hstable : (prefixWord ++ tailWord_349320).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349320).length < 2 ^ (prefixWord ++ tailWord_349320).sum := by decide
  have hdescent : baseEnd_349320 < baseStart_349320 := by decide
  rcases family_descends (prefixWord ++ tailWord_349320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349331 : List Nat := [1, 1, 1, 2, 1, 2, 6, 3, 4]
def baseStart_349331 : Nat := 118140960795 + 349331 * 2 ^ 59
def prefixEnd_349331 : Nat := 4983230072969 + 3 ^ 40 * 349331 * 2
def baseEnd_349331 : Nat := 79722093562612433135983

theorem tailTrace_349331 : CollatzResearch.WordTrace tailWord_349331 prefixEnd_349331 79722093562612433135983 := by
  unfold tailWord_349331
  simp only [CollatzResearch.WordTrace]
  refine ⟨12741148297440922830055847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8494098864960615220037231 12741148297440922830055847)
  ·
    refine ⟨19111722446161384245083771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12741148297440922830055847 19111722446161384245083771)
    ·
      refine ⟨28667583669242076367625657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19111722446161384245083771 28667583669242076367625657)
      ·
        refine ⟨21500687751931557275719243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 28667583669242076367625657 21500687751931557275719243)
        ·
          refine ⟨32251031627897335913578865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21500687751931557275719243 32251031627897335913578865)
          ·
            refine ⟨24188273720923001935184149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 32251031627897335913578865 24188273720923001935184149)
            ·
              refine ⟨1133825330668265715711757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 24188273720923001935184149 1133825330668265715711757)
              ·
                refine ⟨425184499000599643391909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 1133825330668265715711757 425184499000599643391909)
                ·
                  refine ⟨79722093562612433135983, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425184499000599643391909 79722093562612433135983)
                  ·
                    rfl

theorem cell21_349331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 6, 3, 4].length) (baseStart_349331 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349331 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349331 prefixEnd_349331 := by exact prefixLift 349331
  have htrace : WordTrace (prefixWord ++ tailWord_349331) baseStart_349331 baseEnd_349331 := by
    simpa [prefixWord, tailWord_349331, baseEnd_349331] using wordTrace_append hprefix tailTrace_349331
  have hstable : (prefixWord ++ tailWord_349331).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349331).length < 2 ^ (prefixWord ++ tailWord_349331).sum := by decide
  have hdescent : baseEnd_349331 < baseStart_349331 := by decide
  rcases family_descends (prefixWord ++ tailWord_349331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349351 : List Nat := [1, 1, 6, 2, 1, 2, 2, 3, 3]
def baseStart_349351 : Nat := 118140960795 + 349351 * 2 ^ 59
def prefixEnd_349351 : Nat := 4983230072969 + 3 ^ 40 * 349351 * 2
def baseEnd_349351 : Nat := 79726657835096842802609

theorem tailTrace_349351 : CollatzResearch.WordTrace tailWord_349351 prefixEnd_349351 79726657835096842802609 := by
  unfold tailWord_349351
  simp only [CollatzResearch.WordTrace]
  refine ⟨12741877757368466245783907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8494585171578977497189271 12741877757368466245783907)
  ·
    refine ⟨19112816636052699368675861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12741877757368466245783907 19112816636052699368675861)
    ·
      refine ⟨895913279814970282906681, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 19112816636052699368675861 895913279814970282906681)
      ·
        refine ⟨671934959861227712180011, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 895913279814970282906681 671934959861227712180011)
        ·
          refine ⟨1007902439791841568270017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 671934959861227712180011 1007902439791841568270017)
          ·
            refine ⟨755926829843881176202513, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1007902439791841568270017 755926829843881176202513)
            ·
              refine ⟨566945122382910882151885, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 755926829843881176202513 566945122382910882151885)
              ·
                refine ⟨212604420893591580806957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 566945122382910882151885 212604420893591580806957)
                ·
                  refine ⟨79726657835096842802609, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212604420893591580806957 79726657835096842802609)
                  ·
                    rfl

theorem cell21_349351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 2, 1, 2, 2, 3, 3].length) (baseStart_349351 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349351 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349351 prefixEnd_349351 := by exact prefixLift 349351
  have htrace : WordTrace (prefixWord ++ tailWord_349351) baseStart_349351 baseEnd_349351 := by
    simpa [prefixWord, tailWord_349351, baseEnd_349351] using wordTrace_append hprefix tailTrace_349351
  have hstable : (prefixWord ++ tailWord_349351).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349351).length < 2 ^ (prefixWord ++ tailWord_349351).sum := by decide
  have hdescent : baseEnd_349351 < baseStart_349351 := by decide
  rcases family_descends (prefixWord ++ tailWord_349351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349438 : List Nat := [4, 2, 2, 1, 1, 2, 1, 8]
def baseStart_349438 : Nat := 118140960795 + 349438 * 2 ^ 59
def prefixEnd_349438 : Nat := 4983230072969 + 3 ^ 40 * 349438 * 2
def baseEnd_349438 : Nat := 26582170806801341617477

theorem tailTrace_349438 : CollatzResearch.WordTrace tailWord_349438 prefixEnd_349438 26582170806801341617477 := by
  unfold tailWord_349438
  simp only [CollatzResearch.WordTrace]
  refine ⟨1593131363506660013025121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8496700605368853402800645 1593131363506660013025121)
  ·
    refine ⟨1194848522629995009768841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1593131363506660013025121 1194848522629995009768841)
    ·
      refine ⟨896136391972496257326631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1194848522629995009768841 896136391972496257326631)
      ·
        refine ⟨1344204587958744385989947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896136391972496257326631 1344204587958744385989947)
        ·
          refine ⟨2016306881938116578984921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1344204587958744385989947 2016306881938116578984921)
          ·
            refine ⟨1512230161453587434238691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2016306881938116578984921 1512230161453587434238691)
            ·
              refine ⟨2268345242180381151358037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1512230161453587434238691 2268345242180381151358037)
              ·
                refine ⟨26582170806801341617477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2268345242180381151358037 26582170806801341617477)
                ·
                  rfl

theorem cell21_349438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 1, 1, 2, 1, 8].length) (baseStart_349438 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349438 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349438 prefixEnd_349438 := by exact prefixLift 349438
  have htrace : WordTrace (prefixWord ++ tailWord_349438) baseStart_349438 baseEnd_349438 := by
    simpa [prefixWord, tailWord_349438, baseEnd_349438] using wordTrace_append hprefix tailTrace_349438
  have hstable : (prefixWord ++ tailWord_349438).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349438).length < 2 ^ (prefixWord ++ tailWord_349438).sum := by decide
  have hdescent : baseEnd_349438 < baseStart_349438 := by decide
  rcases family_descends (prefixWord ++ tailWord_349438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349441 : List Nat := [1, 2, 4, 1, 1, 5, 2, 1, 4]
def baseStart_349441 : Nat := 118140960795 + 349441 * 2 ^ 59
def prefixEnd_349441 : Nat := 4983230072969 + 3 ^ 40 * 349441 * 2
def baseEnd_349441 : Nat := 79747197061276686302425

theorem tailTrace_349441 : CollatzResearch.WordTrace tailWord_349441 prefixEnd_349441 79747197061276686302425 := by
  unfold tailWord_349441
  simp only [CollatzResearch.WordTrace]
  refine ⟨12745160327042411616560177, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8496773551361607744373451 12745160327042411616560177)
  ·
    refine ⟨9558870245281808712420133, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12745160327042411616560177 9558870245281808712420133)
    ·
      refine ⟨1792288170990339133578775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9558870245281808712420133 1792288170990339133578775)
      ·
        refine ⟨2688432256485508700368163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1792288170990339133578775 2688432256485508700368163)
        ·
          refine ⟨4032648384728263050552245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2688432256485508700368163 4032648384728263050552245)
          ·
            refine ⟨378060786068274660989273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 4032648384728263050552245 378060786068274660989273)
            ·
              refine ⟨283545589551205995741955, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378060786068274660989273 283545589551205995741955)
              ·
                refine ⟨425318384326808993612933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283545589551205995741955 425318384326808993612933)
                ·
                  refine ⟨79747197061276686302425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425318384326808993612933 79747197061276686302425)
                  ·
                    rfl

theorem cell21_349441_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 5, 2, 1, 4].length) (baseStart_349441 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349441 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349441 prefixEnd_349441 := by exact prefixLift 349441
  have htrace : WordTrace (prefixWord ++ tailWord_349441) baseStart_349441 baseEnd_349441 := by
    simpa [prefixWord, tailWord_349441, baseEnd_349441] using wordTrace_append hprefix tailTrace_349441
  have hstable : (prefixWord ++ tailWord_349441).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349441).length < 2 ^ (prefixWord ++ tailWord_349441).sum := by decide
  have hdescent : baseEnd_349441 < baseStart_349441 := by decide
  rcases family_descends (prefixWord ++ tailWord_349441) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349596 : List Nat := [2, 2, 3, 4, 1, 1, 3, 2, 3]
def baseStart_349596 : Nat := 118140960795 + 349596 * 2 ^ 59
def prefixEnd_349596 : Nat := 4983230072969 + 3 ^ 40 * 349596 * 2
def baseEnd_349596 : Nat := 79782570173030861218775

theorem tailTrace_349596 : CollatzResearch.WordTrace tailWord_349596 prefixEnd_349596 79782570173030861218775 := by
  unfold tailWord_349596
  simp only [CollatzResearch.WordTrace]
  refine ⟨6375406820740436544226321, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8500542427653915392301761 6375406820740436544226321)
  ·
    refine ⟨4781555115555327408169741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6375406820740436544226321 4781555115555327408169741)
    ·
      refine ⟨1793083168333247778063653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 4781555115555327408169741 1793083168333247778063653)
      ·
        refine ⟨336203094062483958386935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 1793083168333247778063653 336203094062483958386935)
        ·
          refine ⟨504304641093725937580403, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 336203094062483958386935 504304641093725937580403)
          ·
            refine ⟨756456961640588906370605, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 504304641093725937580403 756456961640588906370605)
            ·
              refine ⟨283671360615220839888977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 756456961640588906370605 283671360615220839888977)
              ·
                refine ⟨212753520461415629916733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 283671360615220839888977 212753520461415629916733)
                ·
                  refine ⟨79782570173030861218775, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212753520461415629916733 79782570173030861218775)
                  ·
                    rfl

theorem cell21_349596_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 4, 1, 1, 3, 2, 3].length) (baseStart_349596 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349596 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349596 prefixEnd_349596 := by exact prefixLift 349596
  have htrace : WordTrace (prefixWord ++ tailWord_349596) baseStart_349596 baseEnd_349596 := by
    simpa [prefixWord, tailWord_349596, baseEnd_349596] using wordTrace_append hprefix tailTrace_349596
  have hstable : (prefixWord ++ tailWord_349596).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349596).length < 2 ^ (prefixWord ++ tailWord_349596).sum := by decide
  have hdescent : baseEnd_349596 < baseStart_349596 := by decide
  rcases family_descends (prefixWord ++ tailWord_349596) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349618 : List Nat := [3, 2, 1, 1, 1, 1, 2, 2, 8]
def baseStart_349618 : Nat := 118140960795 + 349618 * 2 ^ 59
def prefixEnd_349618 : Nat := 4983230072969 + 3 ^ 40 * 349618 * 2
def baseEnd_349618 : Nat := 79787590872763711852063

theorem tailTrace_349618 : CollatzResearch.WordTrace tailWord_349618 prefixEnd_349618 79787590872763711852063 := by
  unfold tailWord_349618
  simp only [CollatzResearch.WordTrace]
  refine ⟨3187904011850292711438377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8501077364934113897169005 3187904011850292711438377)
  ·
    refine ⟨2390928008887719533578783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3187904011850292711438377 2390928008887719533578783)
    ·
      refine ⟨3586392013331579300368175, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2390928008887719533578783 3586392013331579300368175)
      ·
        refine ⟨5379588019997368950552263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3586392013331579300368175 5379588019997368950552263)
        ·
          refine ⟨8069382029996053425828395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5379588019997368950552263 8069382029996053425828395)
          ·
            refine ⟨12104073044994080138742593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8069382029996053425828395 12104073044994080138742593)
            ·
              refine ⟨9078054783745560104056945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12104073044994080138742593 9078054783745560104056945)
              ·
                refine ⟨6808541087809170078042709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9078054783745560104056945 6808541087809170078042709)
                ·
                  refine ⟨79787590872763711852063, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6808541087809170078042709 79787590872763711852063)
                  ·
                    rfl

theorem cell21_349618_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 2, 2, 8].length) (baseStart_349618 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349618 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349618 prefixEnd_349618 := by exact prefixLift 349618
  have htrace : WordTrace (prefixWord ++ tailWord_349618) baseStart_349618 baseEnd_349618 := by
    simpa [prefixWord, tailWord_349618, baseEnd_349618] using wordTrace_append hprefix tailTrace_349618
  have hstable : (prefixWord ++ tailWord_349618).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349618).length < 2 ^ (prefixWord ++ tailWord_349618).sum := by decide
  have hdescent : baseEnd_349618 < baseStart_349618 := by decide
  rcases family_descends (prefixWord ++ tailWord_349618) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349680 : List Nat := [2, 1, 1, 1, 3, 5, 1, 2, 5]
def baseStart_349680 : Nat := 118140960795 + 349680 * 2 ^ 59
def prefixEnd_349680 : Nat := 4983230072969 + 3 ^ 40 * 349680 * 2
def baseEnd_349680 : Nat := 79801740117465381818603

theorem tailTrace_349680 : CollatzResearch.WordTrace tailWord_349680 prefixEnd_349680 79801740117465381818603 := by
  unfold tailWord_349680
  simp only [CollatzResearch.WordTrace]
  refine ⟨6376938686588277717255247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8502584915451036956340329 6376938686588277717255247)
  ·
    refine ⟨9565408029882416575882871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6376938686588277717255247 9565408029882416575882871)
    ·
      refine ⟨14348112044823624863824307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9565408029882416575882871 14348112044823624863824307)
      ·
        refine ⟨21522168067235437295736461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14348112044823624863824307 21522168067235437295736461)
        ·
          refine ⟨8070813025213288985901173, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21522168067235437295736461 8070813025213288985901173)
          ·
            refine ⟨756638721113745842428235, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 8070813025213288985901173 756638721113745842428235)
            ·
              refine ⟨1134958081670618763642353, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756638721113745842428235 1134958081670618763642353)
              ·
                refine ⟨851218561252964072731765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 1134958081670618763642353 851218561252964072731765)
                ·
                  refine ⟨79801740117465381818603, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 851218561252964072731765 79801740117465381818603)
                  ·
                    rfl

theorem cell21_349680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 5, 1, 2, 5].length) (baseStart_349680 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349680 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349680 prefixEnd_349680 := by exact prefixLift 349680
  have htrace : WordTrace (prefixWord ++ tailWord_349680) baseStart_349680 baseEnd_349680 := by
    simpa [prefixWord, tailWord_349680, baseEnd_349680] using wordTrace_append hprefix tailTrace_349680
  have hstable : (prefixWord ++ tailWord_349680).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349680).length < 2 ^ (prefixWord ++ tailWord_349680).sum := by decide
  have hdescent : baseEnd_349680 < baseStart_349680 := by decide
  rcases family_descends (prefixWord ++ tailWord_349680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349725 : List Nat := [1, 4, 2, 2, 1, 1, 2, 8]
def baseStart_349725 : Nat := 118140960795 + 349725 * 2 ^ 59
def prefixEnd_349725 : Nat := 4983230072969 + 3 ^ 40 * 349725 * 2
def baseEnd_349725 : Nat := 26604003243518434522837

theorem tailTrace_349725 : CollatzResearch.WordTrace tailWord_349725 prefixEnd_349725 26604003243518434522837 := by
  unfold tailWord_349725
  simp only [CollatzResearch.WordTrace]
  refine ⟨12755518658013528119898629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8503679105342352079932419 12755518658013528119898629)
  ·
    refine ⟨2391659748377536522480993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12755518658013528119898629 2391659748377536522480993)
    ·
      refine ⟨1793744811283152391860745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2391659748377536522480993 1793744811283152391860745)
      ·
        refine ⟨1345308608462364293895559, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1793744811283152391860745 1345308608462364293895559)
        ·
          refine ⟨2017962912693546440843339, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1345308608462364293895559 2017962912693546440843339)
          ·
            refine ⟨3026944369040319661265009, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2017962912693546440843339 3026944369040319661265009)
            ·
              refine ⟨2270208276780239745948757, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3026944369040319661265009 2270208276780239745948757)
              ·
                refine ⟨26604003243518434522837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 2270208276780239745948757 26604003243518434522837)
                ·
                  rfl

theorem cell21_349725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 1, 2, 8].length) (baseStart_349725 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349725 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349725 prefixEnd_349725 := by exact prefixLift 349725
  have htrace : WordTrace (prefixWord ++ tailWord_349725) baseStart_349725 baseEnd_349725 := by
    simpa [prefixWord, tailWord_349725, baseEnd_349725] using wordTrace_append hprefix tailTrace_349725
  have hstable : (prefixWord ++ tailWord_349725).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349725).length < 2 ^ (prefixWord ++ tailWord_349725).sum := by decide
  have hdescent : baseEnd_349725 < baseStart_349725 := by decide
  rcases family_descends (prefixWord ++ tailWord_349725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349742 : List Nat := [4, 1, 3, 1, 2, 2, 1, 7]
def baseStart_349742 : Nat := 118140960795 + 349742 * 2 ^ 59
def prefixEnd_349742 : Nat := 4983230072969 + 3 ^ 40 * 349742 * 2
def baseEnd_349742 : Nat := 26605296454055683928381

theorem tailTrace_349742 : CollatzResearch.WordTrace tailWord_349742 prefixEnd_349742 26605296454055683928381 := by
  unfold tailWord_349742
  simp only [CollatzResearch.WordTrace]
  refine ⟨1594517337368992502908435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8504092465967960015511653 1594517337368992502908435)
  ·
    refine ⟨2391776006053488754362653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1594517337368992502908435 2391776006053488754362653)
    ·
      refine ⟨896916002270058282885995, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 2391776006053488754362653 896916002270058282885995)
      ·
        refine ⟨1345374003405087424328993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 896916002270058282885995 1345374003405087424328993)
        ·
          refine ⟨1009030502553815568246745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1345374003405087424328993 1009030502553815568246745)
          ·
            refine ⟨756772876915361676185059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1009030502553815568246745 756772876915361676185059)
            ·
              refine ⟨1135159315373042514277589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 756772876915361676185059 1135159315373042514277589)
              ·
                refine ⟨26605296454055683928381, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1135159315373042514277589 26605296454055683928381)
                ·
                  rfl

theorem cell21_349742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 1, 2, 2, 1, 7].length) (baseStart_349742 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349742 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349742 prefixEnd_349742 := by exact prefixLift 349742
  have htrace : WordTrace (prefixWord ++ tailWord_349742) baseStart_349742 baseEnd_349742 := by
    simpa [prefixWord, tailWord_349742, baseEnd_349742] using wordTrace_append hprefix tailTrace_349742
  have hstable : (prefixWord ++ tailWord_349742).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349742).length < 2 ^ (prefixWord ++ tailWord_349742).sum := by decide
  have hdescent : baseEnd_349742 < baseStart_349742 := by decide
  rcases family_descends (prefixWord ++ tailWord_349742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349770 : List Nat := [3, 1, 2, 1, 1, 3, 1, 3, 6]
def baseStart_349770 : Nat := 118140960795 + 349770 * 2 ^ 59
def prefixEnd_349770 : Nat := 4983230072969 + 3 ^ 40 * 349770 * 2
def baseEnd_349770 : Nat := 79822279343645225318419

theorem tailTrace_349770 : CollatzResearch.WordTrace tailWord_349770 prefixEnd_349770 79822279343645225318419 := by
  unfold tailWord_349770
  simp only [CollatzResearch.WordTrace]
  refine ⟨3189289985712625201321691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8504773295233667203524509 3189289985712625201321691)
  ·
    refine ⟨4783934978568937801982537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3189289985712625201321691 4783934978568937801982537)
    ·
      refine ⟨3587951233926703351486903, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4783934978568937801982537 3587951233926703351486903)
      ·
        refine ⟨5381926850890055027230355, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3587951233926703351486903 5381926850890055027230355)
        ·
          refine ⟨8072890276335082540845533, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5381926850890055027230355 8072890276335082540845533)
          ·
            refine ⟨3027333853625655952817075, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 8072890276335082540845533 3027333853625655952817075)
            ·
              refine ⟨4541000780438483929225613, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3027333853625655952817075 4541000780438483929225613)
              ·
                refine ⟨1702875292664431473459605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 4541000780438483929225613 1702875292664431473459605)
                ·
                  refine ⟨79822279343645225318419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1702875292664431473459605 79822279343645225318419)
                  ·
                    rfl

theorem cell21_349770_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 1, 3, 1, 3, 6].length) (baseStart_349770 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349770 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349770 prefixEnd_349770 := by exact prefixLift 349770
  have htrace : WordTrace (prefixWord ++ tailWord_349770) baseStart_349770 baseEnd_349770 := by
    simpa [prefixWord, tailWord_349770, baseEnd_349770] using wordTrace_append hprefix tailTrace_349770
  have hstable : (prefixWord ++ tailWord_349770).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349770).length < 2 ^ (prefixWord ++ tailWord_349770).sum := by decide
  have hdescent : baseEnd_349770 < baseStart_349770 := by decide
  rcases family_descends (prefixWord ++ tailWord_349770) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349956 : List Nat := [2, 3, 2, 2, 1, 2, 4, 1, 4]
def baseStart_349956 : Nat := 118140960795 + 349956 * 2 ^ 59
def prefixEnd_349956 : Nat := 4983230072969 + 3 ^ 40 * 349956 * 2
def baseEnd_349956 : Nat := 79864727077750235218039

theorem tailTrace_349956 : CollatzResearch.WordTrace tailWord_349956 prefixEnd_349956 79864727077750235218039 := by
  unfold tailWord_349956
  simp only [CollatzResearch.WordTrace]
  refine ⟨6381971960088327285778861, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8509295946784436381038481 6381971960088327285778861)
  ·
    refine ⟨2393239485033122732167073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 6381971960088327285778861 2393239485033122732167073)
    ·
      refine ⟨1794929613774842049125305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2393239485033122732167073 1794929613774842049125305)
      ·
        refine ⟨1346197210331131536843979, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1794929613774842049125305 1346197210331131536843979)
        ·
          refine ⟨2019295815496697305265969, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1346197210331131536843979 2019295815496697305265969)
          ·
            refine ⟨1514471861622522978949477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 2019295815496697305265969 1514471861622522978949477)
            ·
              refine ⟨283963474054223058553027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1514471861622522978949477 283963474054223058553027)
              ·
                refine ⟨425945211081334587829541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 283963474054223058553027 425945211081334587829541)
                ·
                  refine ⟨79864727077750235218039, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 425945211081334587829541 79864727077750235218039)
                  ·
                    rfl

theorem cell21_349956_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 2, 1, 2, 4, 1, 4].length) (baseStart_349956 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349956 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349956 prefixEnd_349956 := by exact prefixLift 349956
  have htrace : WordTrace (prefixWord ++ tailWord_349956) baseStart_349956 baseEnd_349956 := by
    simpa [prefixWord, tailWord_349956, baseEnd_349956] using wordTrace_append hprefix tailTrace_349956
  have hstable : (prefixWord ++ tailWord_349956).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349956).length < 2 ^ (prefixWord ++ tailWord_349956).sum := by decide
  have hdescent : baseEnd_349956 < baseStart_349956 := by decide
  rcases family_descends (prefixWord ++ tailWord_349956) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_349970 : List Nat := [3, 2, 4, 1, 1, 1, 2, 7]
def baseStart_349970 : Nat := 118140960795 + 349970 * 2 ^ 59
def prefixEnd_349970 : Nat := 4983230072969 + 3 ^ 40 * 349970 * 2
def baseEnd_349970 : Nat := 26622640689496440661559

theorem tailTrace_349970 : CollatzResearch.WordTrace tailWord_349970 prefixEnd_349970 26622640689496440661559 := by
  unfold tailWord_349970
  simp only [CollatzResearch.WordTrace]
  refine ⟨3191113635531483740641841, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8509636361417289975044909 3191113635531483740641841)
  ·
    refine ⟨2393335226648612805481381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3191113635531483740641841 2393335226648612805481381)
    ·
      refine ⟨448750354996614901027759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 2393335226648612805481381 448750354996614901027759)
      ·
        refine ⟨673125532494922351541639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 448750354996614901027759 673125532494922351541639)
        ·
          refine ⟨1009688298742383527312459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673125532494922351541639 1009688298742383527312459)
          ·
            refine ⟨1514532448113575290968689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1009688298742383527312459 1514532448113575290968689)
            ·
              refine ⟨1135899336085181468226517, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1514532448113575290968689 1135899336085181468226517)
              ·
                refine ⟨26622640689496440661559, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1135899336085181468226517 26622640689496440661559)
                ·
                  rfl

theorem cell21_349970_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 4, 1, 1, 1, 2, 7].length) (baseStart_349970 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_349970 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_349970 prefixEnd_349970 := by exact prefixLift 349970
  have htrace : WordTrace (prefixWord ++ tailWord_349970) baseStart_349970 baseEnd_349970 := by
    simpa [prefixWord, tailWord_349970, baseEnd_349970] using wordTrace_append hprefix tailTrace_349970
  have hstable : (prefixWord ++ tailWord_349970).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_349970).length < 2 ^ (prefixWord ++ tailWord_349970).sum := by decide
  have hdescent : baseEnd_349970 < baseStart_349970 := by decide
  rcases family_descends (prefixWord ++ tailWord_349970) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350001 : List Nat := [1, 2, 2, 3, 2, 3, 1, 4, 3]
def baseStart_350001 : Nat := 118140960795 + 350001 * 2 ^ 59
def prefixEnd_350001 : Nat := 4983230072969 + 3 ^ 40 * 350001 * 2
def baseEnd_350001 : Nat := 79874996690840156967947

theorem tailTrace_350001 : CollatzResearch.WordTrace tailWord_350001 prefixEnd_350001 79874996690840156967947 := by
  unfold tailWord_350001
  simp only [CollatzResearch.WordTrace]
  refine ⟨12765585205013627256945857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8510390136675751504630571 12765585205013627256945857)
  ·
    refine ⟨9574188903760220442709393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12765585205013627256945857 9574188903760220442709393)
    ·
      refine ⟨7180641677820165332032045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9574188903760220442709393 7180641677820165332032045)
      ·
        refine ⟨2692740629182561999512017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7180641677820165332032045 2692740629182561999512017)
        ·
          refine ⟨2019555471886921499634013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 2692740629182561999512017 2019555471886921499634013)
          ·
            refine ⟨757333301957595562362755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2019555471886921499634013 757333301957595562362755)
            ·
              refine ⟨1135999952936393343544133, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 757333301957595562362755 1135999952936393343544133)
              ·
                refine ⟨212999991175573751914525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1135999952936393343544133 212999991175573751914525)
                ·
                  refine ⟨79874996690840156967947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 212999991175573751914525 79874996690840156967947)
                  ·
                    rfl

theorem cell21_350001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 3, 1, 4, 3].length) (baseStart_350001 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350001 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350001 prefixEnd_350001 := by exact prefixLift 350001
  have htrace : WordTrace (prefixWord ++ tailWord_350001) baseStart_350001 baseEnd_350001 := by
    simpa [prefixWord, tailWord_350001, baseEnd_350001] using wordTrace_append hprefix tailTrace_350001
  have hstable : (prefixWord ++ tailWord_350001).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350001).length < 2 ^ (prefixWord ++ tailWord_350001).sum := by decide
  have hdescent : baseEnd_350001 < baseStart_350001 := by decide
  rcases family_descends (prefixWord ++ tailWord_350001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350060 : List Nat := [2, 2, 1, 1, 4, 3, 2, 1, 5]
def baseStart_350060 : Nat := 118140960795 + 350060 * 2 ^ 59
def prefixEnd_350060 : Nat := 4983230072969 + 3 ^ 40 * 350060 * 2
def baseEnd_350060 : Nat := 79888461294669165484493

theorem tailTrace_350060 : CollatzResearch.WordTrace tailWord_350060 prefixEnd_350060 79888461294669165484493 := by
  unfold tailWord_350060
  simp only [CollatzResearch.WordTrace]
  refine ⟨6383868555899940166671817, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8511824741199920222229089 6383868555899940166671817)
  ·
    refine ⟨4787901416924955125003863, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6383868555899940166671817 4787901416924955125003863)
    ·
      refine ⟨7181852125387432687505795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4787901416924955125003863 7181852125387432687505795)
      ·
        refine ⟨10772778188081149031258693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7181852125387432687505795 10772778188081149031258693)
        ·
          refine ⟨2019895910265215443361005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 10772778188081149031258693 2019895910265215443361005)
          ·
            refine ⟨757460966349455791260377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 2019895910265215443361005 757460966349455791260377)
            ·
              refine ⟨568095724762091843445283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 757460966349455791260377 568095724762091843445283)
              ·
                refine ⟨852143587143137765167925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 568095724762091843445283 852143587143137765167925)
                ·
                  refine ⟨79888461294669165484493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 852143587143137765167925 79888461294669165484493)
                  ·
                    rfl

theorem cell21_350060_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 5].length) (baseStart_350060 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350060 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350060 prefixEnd_350060 := by exact prefixLift 350060
  have htrace : WordTrace (prefixWord ++ tailWord_350060) baseStart_350060 baseEnd_350060 := by
    simpa [prefixWord, tailWord_350060, baseEnd_350060] using wordTrace_append hprefix tailTrace_350060
  have hstable : (prefixWord ++ tailWord_350060).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350060).length < 2 ^ (prefixWord ++ tailWord_350060).sum := by decide
  have hdescent : baseEnd_350060 < baseStart_350060 := by decide
  rcases family_descends (prefixWord ++ tailWord_350060) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350074 : List Nat := [3, 1, 1, 1, 1, 1, 4, 5, 4]
def baseStart_350074 : Nat := 118140960795 + 350074 * 2 ^ 59
def prefixEnd_350074 : Nat := 4983230072969 + 3 ^ 40 * 350074 * 2
def baseEnd_350074 : Nat := 79891656285408252251131

theorem tailTrace_350074 : CollatzResearch.WordTrace tailWord_350074 prefixEnd_350074 79891656285408252251131 := by
  unfold tailWord_350074
  simp only [CollatzResearch.WordTrace]
  refine ⟨3192061933437290181088319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8512165155832773816235517 3192061933437290181088319)
  ·
    refine ⟨4788092900155935271632479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3192061933437290181088319 4788092900155935271632479)
    ·
      refine ⟨7182139350233902907448719, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4788092900155935271632479 7182139350233902907448719)
      ·
        refine ⟨10773209025350854361173079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7182139350233902907448719 10773209025350854361173079)
        ·
          refine ⟨16159813538026281541759619, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10773209025350854361173079 16159813538026281541759619)
          ·
            refine ⟨24239720307039422312639429, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16159813538026281541759619 24239720307039422312639429)
            ·
              refine ⟨4544947557569891683619893, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 24239720307039422312639429 4544947557569891683619893)
              ·
                refine ⟨426088833522177345339365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 4544947557569891683619893 426088833522177345339365)
                ·
                  refine ⟨79891656285408252251131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426088833522177345339365 79891656285408252251131)
                  ·
                    rfl

theorem cell21_350074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 1, 1, 4, 5, 4].length) (baseStart_350074 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350074 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350074 prefixEnd_350074 := by exact prefixLift 350074
  have htrace : WordTrace (prefixWord ++ tailWord_350074) baseStart_350074 baseEnd_350074 := by
    simpa [prefixWord, tailWord_350074, baseEnd_350074] using wordTrace_append hprefix tailTrace_350074
  have hstable : (prefixWord ++ tailWord_350074).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350074).length < 2 ^ (prefixWord ++ tailWord_350074).sum := by decide
  have hdescent : baseEnd_350074 < baseStart_350074 := by decide
  rcases family_descends (prefixWord ++ tailWord_350074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350243 : List Nat := [1, 1, 1, 4, 3, 1, 5, 1, 4]
def baseStart_350243 : Nat := 118140960795 + 350243 * 2 ^ 59
def prefixEnd_350243 : Nat := 4983230072969 + 3 ^ 40 * 350243 * 2
def baseEnd_350243 : Nat := 79930224387901513934119

theorem tailTrace_350243 : CollatzResearch.WordTrace tailWord_350243 prefixEnd_350243 79930224387901513934119 := by
  unfold tailWord_350243
  simp only [CollatzResearch.WordTrace]
  refine ⟨12774411670136902587255383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8516274446757935058170255 12774411670136902587255383)
  ·
    refine ⟨19161617505205353880883075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12774411670136902587255383 19161617505205353880883075)
    ·
      refine ⟨28742426257808030821324613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 19161617505205353880883075 28742426257808030821324613)
      ·
        refine ⟨5389204923339005778998365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 28742426257808030821324613 5389204923339005778998365)
        ·
          refine ⟨2020951846252127167124387, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5389204923339005778998365 2020951846252127167124387)
          ·
            refine ⟨3031427769378190750686581, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2020951846252127167124387 3031427769378190750686581)
            ·
              refine ⟨284196353379205382876867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3031427769378190750686581 284196353379205382876867)
              ·
                refine ⟨426294530068808074315301, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284196353379205382876867 426294530068808074315301)
                ·
                  refine ⟨79930224387901513934119, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426294530068808074315301 79930224387901513934119)
                  ·
                    rfl

theorem cell21_350243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 1, 5, 1, 4].length) (baseStart_350243 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350243 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350243 prefixEnd_350243 := by exact prefixLift 350243
  have htrace : WordTrace (prefixWord ++ tailWord_350243) baseStart_350243 baseEnd_350243 := by
    simpa [prefixWord, tailWord_350243, baseEnd_350243] using wordTrace_append hprefix tailTrace_350243
  have hstable : (prefixWord ++ tailWord_350243).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350243).length < 2 ^ (prefixWord ++ tailWord_350243).sum := by decide
  have hdescent : baseEnd_350243 < baseStart_350243 := by decide
  rcases family_descends (prefixWord ++ tailWord_350243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350257 : List Nat := [1, 2, 2, 3, 1, 3, 4, 5]
def baseStart_350257 : Nat := 118140960795 + 350257 * 2 ^ 59
def prefixEnd_350257 : Nat := 4983230072969 + 3 ^ 40 * 350257 * 2
def baseEnd_350257 : Nat := 26644473126213533566919

theorem tailTrace_350257 : CollatzResearch.WordTrace tailWord_350257 prefixEnd_350257 26644473126213533566919 := by
  unfold tailWord_350257
  simp only [CollatzResearch.WordTrace]
  refine ⟨12774922292086182978265025, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8516614861390788652176683 12774922292086182978265025)
  ·
    refine ⟨9581191719064637233698769, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12774922292086182978265025 9581191719064637233698769)
    ·
      refine ⟨7185893789298477925274077, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9581191719064637233698769 7185893789298477925274077)
      ·
        refine ⟨2694710170986929221977779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7185893789298477925274077 2694710170986929221977779)
        ·
          refine ⟨4042065256480393832966669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2694710170986929221977779 4042065256480393832966669)
          ·
            refine ⟨1515774471180147687362501, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4042065256480393832966669 1515774471180147687362501)
            ·
              refine ⟨284207713346277691380469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 1515774471180147687362501 284207713346277691380469)
              ·
                refine ⟨26644473126213533566919, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 284207713346277691380469 26644473126213533566919)
                ·
                  rfl

theorem cell21_350257_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 1, 3, 4, 5].length) (baseStart_350257 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350257 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350257 prefixEnd_350257 := by exact prefixLift 350257
  have htrace : WordTrace (prefixWord ++ tailWord_350257) baseStart_350257 baseEnd_350257 := by
    simpa [prefixWord, tailWord_350257, baseEnd_350257] using wordTrace_append hprefix tailTrace_350257
  have hstable : (prefixWord ++ tailWord_350257).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350257).length < 2 ^ (prefixWord ++ tailWord_350257).sum := by decide
  have hdescent : baseEnd_350257 < baseStart_350257 := by decide
  rcases family_descends (prefixWord ++ tailWord_350257) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350294 : List Nat := [5, 2, 2, 1, 1, 3, 2, 1, 4]
def baseStart_350294 : Nat := 118140960795 + 350294 * 2 ^ 59
def prefixEnd_350294 : Nat := 4983230072969 + 3 ^ 40 * 350294 * 2
def baseEnd_350294 : Nat := 79941863282736758584015

theorem tailTrace_350294 : CollatzResearch.WordTrace tailWord_350294 prefixEnd_350294 79941863282736758584015 := by
  unfold tailWord_350294
  simp only [CollatzResearch.WordTrace]
  refine ⟨798516987059508643585121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8517514528634758864907957 798516987059508643585121)
  ·
    refine ⟨598887740294631482688841, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 798516987059508643585121 598887740294631482688841)
    ·
      refine ⟨449165805220973612016631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 598887740294631482688841 449165805220973612016631)
      ·
        refine ⟨673748707831460418024947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449165805220973612016631 673748707831460418024947)
        ·
          refine ⟨1010623061747190627037421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 673748707831460418024947 1010623061747190627037421)
          ·
            refine ⟨378983648155196485139033, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1010623061747190627037421 378983648155196485139033)
            ·
              refine ⟨284237736116397363854275, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 378983648155196485139033 284237736116397363854275)
              ·
                refine ⟨426356604174596045781413, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 284237736116397363854275 426356604174596045781413)
                ·
                  refine ⟨79941863282736758584015, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426356604174596045781413 79941863282736758584015)
                  ·
                    rfl

theorem cell21_350294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 2, 1, 1, 3, 2, 1, 4].length) (baseStart_350294 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350294 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350294 prefixEnd_350294 := by exact prefixLift 350294
  have htrace : WordTrace (prefixWord ++ tailWord_350294) baseStart_350294 baseEnd_350294 := by
    simpa [prefixWord, tailWord_350294, baseEnd_350294] using wordTrace_append hprefix tailTrace_350294
  have hstable : (prefixWord ++ tailWord_350294).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350294).length < 2 ^ (prefixWord ++ tailWord_350294).sum := by decide
  have hdescent : baseEnd_350294 < baseStart_350294 := by decide
  rcases family_descends (prefixWord ++ tailWord_350294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350316 : List Nat := [2, 2, 1, 1, 3, 3, 2, 7]
def baseStart_350316 : Nat := 118140960795 + 350316 * 2 ^ 59
def prefixEnd_350316 : Nat := 4983230072969 + 3 ^ 40 * 350316 * 2
def baseEnd_350316 : Nat := 26648961327489869739101

theorem tailTrace_350316 : CollatzResearch.WordTrace tailWord_350316 prefixEnd_350316 26648961327489869739101 := by
  unfold tailWord_350316
  simp only [CollatzResearch.WordTrace]
  refine ⟨6388537099436218027331401, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8518049465914957369775201 6388537099436218027331401)
  ·
    refine ⟨4791402824577163520498551, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6388537099436218027331401 4791402824577163520498551)
    ·
      refine ⟨7187104236865745280747827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4791402824577163520498551 7187104236865745280747827)
      ·
        refine ⟨10780656355298617921121741, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7187104236865745280747827 10780656355298617921121741)
        ·
          refine ⟨4042746133236981720420653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 10780656355298617921121741 4042746133236981720420653)
          ·
            refine ⟨1516029799963868145157745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4042746133236981720420653 1516029799963868145157745)
            ·
              refine ⟨1137022349972901108868309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1516029799963868145157745 1137022349972901108868309)
              ·
                refine ⟨26648961327489869739101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1137022349972901108868309 26648961327489869739101)
                ·
                  rfl

theorem cell21_350316_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 3, 2, 7].length) (baseStart_350316 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350316 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350316 prefixEnd_350316 := by exact prefixLift 350316
  have htrace : WordTrace (prefixWord ++ tailWord_350316) baseStart_350316 baseEnd_350316 := by
    simpa [prefixWord, tailWord_350316, baseEnd_350316] using wordTrace_append hprefix tailTrace_350316
  have hstable : (prefixWord ++ tailWord_350316).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350316).length < 2 ^ (prefixWord ++ tailWord_350316).sum := by decide
  have hdescent : baseEnd_350316 < baseStart_350316 := by decide
  rcases family_descends (prefixWord ++ tailWord_350316) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350350 : List Nat := [4, 1, 1, 3, 3, 2, 1, 6]
def baseStart_350350 : Nat := 118140960795 + 350350 * 2 ^ 59
def prefixEnd_350350 : Nat := 4983230072969 + 3 ^ 40 * 350350 * 2
def baseEnd_350350 : Nat := 26651547748564368550189

theorem tailTrace_350350 : CollatzResearch.WordTrace tailWord_350350 prefixEnd_350350 26651547748564368550189 := by
  unfold tailWord_350350
  simp only [CollatzResearch.WordTrace]
  refine ⟨1597289285093657482675063, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8518876187166173240933669 1597289285093657482675063)
  ·
    refine ⟨2395933927640486224012595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1597289285093657482675063 2395933927640486224012595)
    ·
      refine ⟨3593900891460729336018893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2395933927640486224012595 3593900891460729336018893)
      ·
        refine ⟨1347712834297773501007085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 3593900891460729336018893 1347712834297773501007085)
        ·
          refine ⟨505392312861665062877657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 1347712834297773501007085 505392312861665062877657)
          ·
            refine ⟨379044234646248797158243, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 505392312861665062877657 379044234646248797158243)
            ·
              refine ⟨568566351969373195737365, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379044234646248797158243 568566351969373195737365)
              ·
                refine ⟨26651547748564368550189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 568566351969373195737365 26651547748564368550189)
                ·
                  rfl

theorem cell21_350350_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 3, 3, 2, 1, 6].length) (baseStart_350350 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350350 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350350 prefixEnd_350350 := by exact prefixLift 350350
  have htrace : WordTrace (prefixWord ++ tailWord_350350) baseStart_350350 baseEnd_350350 := by
    simpa [prefixWord, tailWord_350350, baseEnd_350350] using wordTrace_append hprefix tailTrace_350350
  have hstable : (prefixWord ++ tailWord_350350).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350350).length < 2 ^ (prefixWord ++ tailWord_350350).sum := by decide
  have hdescent : baseEnd_350350 < baseStart_350350 := by decide
  rcases family_descends (prefixWord ++ tailWord_350350) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350381 : List Nat := [1, 5, 2, 1, 2, 1, 1, 5, 3]
def baseStart_350381 : Nat := 118140960795 + 350381 * 2 ^ 59
def prefixEnd_350381 : Nat := 4983230072969 + 3 ^ 40 * 350381 * 2
def baseEnd_350381 : Nat := 79961717868043940633837

theorem tailTrace_350381 : CollatzResearch.WordTrace tailWord_350381 prefixEnd_350381 79961717868043940633837 := by
  unfold tailWord_350381
  simp only [CollatzResearch.WordTrace]
  refine ⟨12779444943636952155778997, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8519629962424634770519331 12779444943636952155778997)
  ·
    refine ⟨1198072963465964264604281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 12779444943636952155778997 1198072963465964264604281)
    ·
      refine ⟨898554722599473198453211, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 1198072963465964264604281 898554722599473198453211)
      ·
        refine ⟨1347832083899209797679817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 898554722599473198453211 1347832083899209797679817)
        ·
          refine ⟨1010874062924407348259863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1347832083899209797679817 1010874062924407348259863)
          ·
            refine ⟨1516311094386611022389795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1010874062924407348259863 1516311094386611022389795)
            ·
              refine ⟨2274466641579916533584693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1516311094386611022389795 2274466641579916533584693)
              ·
                refine ⟨213231247648117175023565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 2274466641579916533584693 213231247648117175023565)
                ·
                  refine ⟨79961717868043940633837, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213231247648117175023565 79961717868043940633837)
                  ·
                    rfl

theorem cell21_350381_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 2, 1, 1, 5, 3].length) (baseStart_350381 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350381 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350381 prefixEnd_350381 := by exact prefixLift 350381
  have htrace : WordTrace (prefixWord ++ tailWord_350381) baseStart_350381 baseEnd_350381 := by
    simpa [prefixWord, tailWord_350381, baseEnd_350381] using wordTrace_append hprefix tailTrace_350381
  have hstable : (prefixWord ++ tailWord_350381).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350381).length < 2 ^ (prefixWord ++ tailWord_350381).sum := by decide
  have hdescent : baseEnd_350381 < baseStart_350381 := by decide
  rcases family_descends (prefixWord ++ tailWord_350381) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350454 : List Nat := [5, 1, 1, 1, 1, 1, 4, 1, 6]
def baseStart_350454 : Nat := 118140960795 + 350454 * 2 ^ 59
def prefixEnd_350454 : Nat := 4983230072969 + 3 ^ 40 * 350454 * 2
def baseEnd_350454 : Nat := 79978377462612035917021

theorem tailTrace_350454 : CollatzResearch.WordTrace tailWord_350454 prefixEnd_350454 79978377462612035917021 := by
  unfold tailWord_350454
  simp only [CollatzResearch.WordTrace]
  refine ⟨798881717023280351449151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 8521404981581657082124277 798881717023280351449151)
  ·
    refine ⟨1198322575534920527173727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 798881717023280351449151 1198322575534920527173727)
    ·
      refine ⟨1797483863302380790760591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1198322575534920527173727 1797483863302380790760591)
      ·
        refine ⟨2696225794953571186140887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1797483863302380790760591 2696225794953571186140887)
        ·
          refine ⟨4044338692430356779211331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2696225794953571186140887 4044338692430356779211331)
          ·
            refine ⟨6066508038645535168816997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4044338692430356779211331 6066508038645535168816997)
            ·
              refine ⟨1137470257246037844153187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6066508038645535168816997 1137470257246037844153187)
              ·
                refine ⟨1706205385869056766229781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1137470257246037844153187 1706205385869056766229781)
                ·
                  refine ⟨79978377462612035917021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1706205385869056766229781 79978377462612035917021)
                  ·
                    rfl

theorem cell21_350454_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 4, 1, 6].length) (baseStart_350454 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350454 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350454 prefixEnd_350454 := by exact prefixLift 350454
  have htrace : WordTrace (prefixWord ++ tailWord_350454) baseStart_350454 baseEnd_350454 := by
    simpa [prefixWord, tailWord_350454, baseEnd_350454] using wordTrace_append hprefix tailTrace_350454
  have hstable : (prefixWord ++ tailWord_350454).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350454).length < 2 ^ (prefixWord ++ tailWord_350454).sum := by decide
  have hdescent : baseEnd_350454 < baseStart_350454 := by decide
  rcases family_descends (prefixWord ++ tailWord_350454) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350606 : List Nat := [4, 1, 1, 4, 1, 1, 1, 2, 6]
def baseStart_350606 : Nat := 118140960795 + 350606 * 2 ^ 59
def prefixEnd_350606 : Nat := 4983230072969 + 3 ^ 40 * 350606 * 2
def baseEnd_350606 : Nat := 80013065933493549383377

theorem tailTrace_350606 : CollatzResearch.WordTrace tailWord_350606 prefixEnd_350606 80013065933493549383377 := by
  unfold tailWord_350606
  simp only [CollatzResearch.WordTrace]
  refine ⟨1598456420977726947839959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8525100911881210388479781 1598456420977726947839959)
  ·
    refine ⟨2397684631466590421759939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 1598456420977726947839959 2397684631466590421759939)
    ·
      refine ⟨3596526947199885632639909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2397684631466590421759939 3596526947199885632639909)
      ·
        refine ⟨674348802599978556119983, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 3596526947199885632639909 674348802599978556119983)
        ·
          refine ⟨1011523203899967834179975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674348802599978556119983 1011523203899967834179975)
          ·
            refine ⟨1517284805849951751269963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011523203899967834179975 1517284805849951751269963)
            ·
              refine ⟨2275927208774927626904945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 1517284805849951751269963 2275927208774927626904945)
              ·
                refine ⟨1706945406581195720178709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 2275927208774927626904945 1706945406581195720178709)
                ·
                  refine ⟨80013065933493549383377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1706945406581195720178709 80013065933493549383377)
                  ·
                    rfl

theorem cell21_350606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 4, 1, 1, 1, 2, 6].length) (baseStart_350606 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350606 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350606 prefixEnd_350606 := by exact prefixLift 350606
  have htrace : WordTrace (prefixWord ++ tailWord_350606) baseStart_350606 baseEnd_350606 := by
    simpa [prefixWord, tailWord_350606, baseEnd_350606] using wordTrace_append hprefix tailTrace_350606
  have hstable : (prefixWord ++ tailWord_350606).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350606).length < 2 ^ (prefixWord ++ tailWord_350606).sum := by decide
  have hdescent : baseEnd_350606 < baseStart_350606 := by decide
  rcases family_descends (prefixWord ++ tailWord_350606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350682 : List Nat := [3, 1, 1, 2, 3, 1, 4, 2, 4]
def baseStart_350682 : Nat := 118140960795 + 350682 * 2 ^ 59
def prefixEnd_350682 : Nat := 4983230072969 + 3 ^ 40 * 350682 * 2
def baseEnd_350682 : Nat := 80030410168934306116555

theorem tailTrace_350682 : CollatzResearch.WordTrace tailWord_350682 prefixEnd_350682 80030410168934306116555 := by
  unfold tailWord_350682
  simp only [CollatzResearch.WordTrace]
  refine ⟨3197605828886620140621575, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8526948877030987041657533 3197605828886620140621575)
  ·
    refine ⟨4796408743329930210932363, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3197605828886620140621575 4796408743329930210932363)
    ·
      refine ⟨7194613114994895316398545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4796408743329930210932363 7194613114994895316398545)
      ·
        refine ⟨5395959836246171487298909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7194613114994895316398545 5395959836246171487298909)
        ·
          refine ⟨2023484938592314307737091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5395959836246171487298909 2023484938592314307737091)
          ·
            refine ⟨3035227407888471461605637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023484938592314307737091 3035227407888471461605637)
            ·
              refine ⟨569105138979088399051057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 3035227407888471461605637 569105138979088399051057)
              ·
                refine ⟨426828854234316299288293, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569105138979088399051057 426828854234316299288293)
                ·
                  refine ⟨80030410168934306116555, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426828854234316299288293 80030410168934306116555)
                  ·
                    rfl

theorem cell21_350682_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 3, 1, 4, 2, 4].length) (baseStart_350682 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350682 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350682 prefixEnd_350682 := by exact prefixLift 350682
  have htrace : WordTrace (prefixWord ++ tailWord_350682) baseStart_350682 baseEnd_350682 := by
    simpa [prefixWord, tailWord_350682, baseEnd_350682] using wordTrace_append hprefix tailTrace_350682
  have hstable : (prefixWord ++ tailWord_350682).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350682).length < 2 ^ (prefixWord ++ tailWord_350682).sum := by decide
  have hdescent : baseEnd_350682 < baseStart_350682 := by decide
  rcases family_descends (prefixWord ++ tailWord_350682) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350696 : List Nat := [2, 1, 4, 1, 1, 3, 3, 6]
def baseStart_350696 : Nat := 118140960795 + 350696 * 2 ^ 59
def prefixEnd_350696 : Nat := 4983230072969 + 3 ^ 40 * 350696 * 2
def baseEnd_350696 : Nat := 26677868386557797627731

theorem tailTrace_350696 : CollatzResearch.WordTrace tailWord_350696 prefixEnd_350696 26677868386557797627731 := by
  unfold tailWord_350696
  simp only [CollatzResearch.WordTrace]
  refine ⟨6395466968747880476747971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8527289291663840635663961 6395466968747880476747971)
  ·
    refine ⟨9593200453121820715121957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6395466968747880476747971 9593200453121820715121957)
    ·
      refine ⟨1798725084960341384085367, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 9593200453121820715121957 1798725084960341384085367)
      ·
        refine ⟨2698087627440512076128051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1798725084960341384085367 2698087627440512076128051)
        ·
          refine ⟨4047131441160768114192077, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2698087627440512076128051 4047131441160768114192077)
          ·
            refine ⟨1517674290435288042822029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 4047131441160768114192077 1517674290435288042822029)
            ·
              refine ⟨569127858913233016058261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 1517674290435288042822029 569127858913233016058261)
              ·
                refine ⟨26677868386557797627731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 569127858913233016058261 26677868386557797627731)
                ·
                  rfl

theorem cell21_350696_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 1, 3, 3, 6].length) (baseStart_350696 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350696 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350696 prefixEnd_350696 := by exact prefixLift 350696
  have htrace : WordTrace (prefixWord ++ tailWord_350696) baseStart_350696 baseEnd_350696 := by
    simpa [prefixWord, tailWord_350696, baseEnd_350696] using wordTrace_append hprefix tailTrace_350696
  have hstable : (prefixWord ++ tailWord_350696).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350696).length < 2 ^ (prefixWord ++ tailWord_350696).sum := by decide
  have hdescent : baseEnd_350696 < baseStart_350696 := by decide
  rcases family_descends (prefixWord ++ tailWord_350696) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350733 : List Nat := [1, 7, 1, 1, 1, 3, 1, 2, 4]
def baseStart_350733 : Nat := 118140960795 + 350733 * 2 ^ 59
def prefixEnd_350733 : Nat := 4983230072969 + 3 ^ 40 * 350733 * 2
def baseEnd_350733 : Nat := 80042049063769550766451

theorem tailTrace_350733 : CollatzResearch.WordTrace tailWord_350733 prefixEnd_350733 80042049063769550766451 := by
  unfold tailWord_350733
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792283438361716272592853, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8528188958907810848395235 12792283438361716272592853)
  ·
    refine ⟨299819143086602725138895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 7 12792283438361716272592853 299819143086602725138895)
    ·
      refine ⟨449728714629904087708343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 299819143086602725138895 449728714629904087708343)
      ·
        refine ⟨674593071944856131562515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 449728714629904087708343 674593071944856131562515)
        ·
          refine ⟨1011889607917284197343773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 674593071944856131562515 1011889607917284197343773)
          ·
            refine ⟨379458602968981574003915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 1011889607917284197343773 379458602968981574003915)
            ·
              refine ⟨569187904453472361005873, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 379458602968981574003915 569187904453472361005873)
              ·
                refine ⟨426890928340104270754405, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 569187904453472361005873 426890928340104270754405)
                ·
                  refine ⟨80042049063769550766451, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 426890928340104270754405 80042049063769550766451)
                  ·
                    rfl

theorem cell21_350733_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 7, 1, 1, 1, 3, 1, 2, 4].length) (baseStart_350733 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350733 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350733 prefixEnd_350733 := by exact prefixLift 350733
  have htrace : WordTrace (prefixWord ++ tailWord_350733) baseStart_350733 baseEnd_350733 := by
    simpa [prefixWord, tailWord_350733, baseEnd_350733] using wordTrace_append hprefix tailTrace_350733
  have hstable : (prefixWord ++ tailWord_350733).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350733).length < 2 ^ (prefixWord ++ tailWord_350733).sum := by decide
  have hdescent : baseEnd_350733 < baseStart_350733 := by decide
  rcases family_descends (prefixWord ++ tailWord_350733) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350741 : List Nat := [1, 3, 2, 1, 3, 1, 3, 1, 6]
def baseStart_350741 : Nat := 118140960795 + 350741 * 2 ^ 59
def prefixEnd_350741 : Nat := 4983230072969 + 3 ^ 40 * 350741 * 2
def baseEnd_350741 : Nat := 80043874772763314633101

theorem tailTrace_350741 : CollatzResearch.WordTrace tailWord_350741 prefixEnd_350741 80043874772763314633101 := by
  unfold tailWord_350741
  simp only [CollatzResearch.WordTrace]
  refine ⟨12792575222332733638884077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8528383481555155759256051 12792575222332733638884077)
  ·
    refine ⟨4797215708374775114581529, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12792575222332733638884077 4797215708374775114581529)
    ·
      refine ⟨3597911781281081335936147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4797215708374775114581529 3597911781281081335936147)
      ·
        refine ⟨5396867671921622003904221, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3597911781281081335936147 5396867671921622003904221)
        ·
          refine ⟨2023825376970608251464083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 5396867671921622003904221 2023825376970608251464083)
          ·
            refine ⟨3035738065455912377196125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2023825376970608251464083 3035738065455912377196125)
            ·
              refine ⟨1138401774545967141448547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 3035738065455912377196125 1138401774545967141448547)
              ·
                refine ⟨1707602661818950712172821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1138401774545967141448547 1707602661818950712172821)
                ·
                  refine ⟨80043874772763314633101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1707602661818950712172821 80043874772763314633101)
                  ·
                    rfl

theorem cell21_350741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 3, 1, 6].length) (baseStart_350741 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350741 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350741 prefixEnd_350741 := by exact prefixLift 350741
  have htrace : WordTrace (prefixWord ++ tailWord_350741) baseStart_350741 baseEnd_350741 := by
    simpa [prefixWord, tailWord_350741, baseEnd_350741] using wordTrace_append hprefix tailTrace_350741
  have hstable : (prefixWord ++ tailWord_350741).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350741).length < 2 ^ (prefixWord ++ tailWord_350741).sum := by decide
  have hdescent : baseEnd_350741 < baseStart_350741 := by decide
  rcases family_descends (prefixWord ++ tailWord_350741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350744 : List Nat := [2, 1, 2, 3, 3, 1, 2, 4, 3]
def baseStart_350744 : Nat := 118140960795 + 350744 * 2 ^ 59
def prefixEnd_350744 : Nat := 4983230072969 + 3 ^ 40 * 350744 * 2
def baseEnd_350744 : Nat := 80044559413635976083095

theorem tailTrace_350744 : CollatzResearch.WordTrace tailWord_350744 prefixEnd_350744 80044559413635976083095 := by
  unfold tailWord_350744
  simp only [CollatzResearch.WordTrace]
  refine ⟨6396342320660932575621643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8528456427547910100828857 6396342320660932575621643)
  ·
    refine ⟨9594513480991398863432465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6396342320660932575621643 9594513480991398863432465)
    ·
      refine ⟨7195885110743549147574349, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 9594513480991398863432465 7195885110743549147574349)
      ·
        refine ⟨2698456916528830930340381, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 7195885110743549147574349 2698456916528830930340381)
        ·
          refine ⟨1011921343698311598877643, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 2698456916528830930340381 1011921343698311598877643)
          ·
            refine ⟨1517882015547467398316465, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1011921343698311598877643 1517882015547467398316465)
            ·
              refine ⟨1138411511660600548737349, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 1517882015547467398316465 1138411511660600548737349)
              ·
                refine ⟨213452158436362602888253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1138411511660600548737349 213452158436362602888253)
                ·
                  refine ⟨80044559413635976083095, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213452158436362602888253 80044559413635976083095)
                  ·
                    rfl

theorem cell21_350744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 3, 1, 2, 4, 3].length) (baseStart_350744 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350744 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350744 prefixEnd_350744 := by exact prefixLift 350744
  have htrace : WordTrace (prefixWord ++ tailWord_350744) baseStart_350744 baseEnd_350744 := by
    simpa [prefixWord, tailWord_350744, baseEnd_350744] using wordTrace_append hprefix tailTrace_350744
  have hstable : (prefixWord ++ tailWord_350744).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350744).length < 2 ^ (prefixWord ++ tailWord_350744).sum := by decide
  have hdescent : baseEnd_350744 < baseStart_350744 := by decide
  rcases family_descends (prefixWord ++ tailWord_350744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350831 : List Nat := [1, 1, 2, 1, 3, 2, 4, 7]
def baseStart_350831 : Nat := 118140960795 + 350831 * 2 ^ 59
def prefixEnd_350831 : Nat := 4983230072969 + 3 ^ 40 * 350831 * 2
def baseEnd_350831 : Nat := 26688137999647719377639

theorem tailTrace_350831 : CollatzResearch.WordTrace tailWord_350831 prefixEnd_350831 26688137999647719377639 := by
  unfold tailWord_350831
  simp only [CollatzResearch.WordTrace]
  refine ⟨12795857792006679009660347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8530571861337786006440231 12795857792006679009660347)
  ·
    refine ⟨19193786688010018514490521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12795857792006679009660347 19193786688010018514490521)
    ·
      refine ⟨14395340016007513885867891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19193786688010018514490521 14395340016007513885867891)
      ·
        refine ⟨21593010024011270828801837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14395340016007513885867891 21593010024011270828801837)
        ·
          refine ⟨8097378759004226560800689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 21593010024011270828801837 8097378759004226560800689)
          ·
            refine ⟨6073034069253169920600517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8097378759004226560800689 6073034069253169920600517)
            ·
              refine ⟨1138693887984969360112597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 6073034069253169920600517 1138693887984969360112597)
              ·
                refine ⟨26688137999647719377639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 1138693887984969360112597 26688137999647719377639)
                ·
                  rfl

theorem cell21_350831_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 3, 2, 4, 7].length) (baseStart_350831 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350831 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350831 prefixEnd_350831 := by exact prefixLift 350831
  have htrace : WordTrace (prefixWord ++ tailWord_350831) baseStart_350831 baseEnd_350831 := by
    simpa [prefixWord, tailWord_350831, baseEnd_350831] using wordTrace_append hprefix tailTrace_350831
  have hstable : (prefixWord ++ tailWord_350831).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350831).length < 2 ^ (prefixWord ++ tailWord_350831).sum := by decide
  have hdescent : baseEnd_350831 < baseStart_350831 := by decide
  rcases family_descends (prefixWord ++ tailWord_350831) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350913 : List Nat := [1, 2, 6, 2, 1, 1, 2, 1, 5]
def baseStart_350913 : Nat := 118140960795 + 350913 * 2 ^ 59
def prefixEnd_350913 : Nat := 4983230072969 + 3 ^ 40 * 350913 * 2
def baseEnd_350913 : Nat := 80083127516129237766083

theorem tailTrace_350913 : CollatzResearch.WordTrace tailWord_350913 prefixEnd_350913 80083127516129237766083 := by
  unfold tailWord_350913
  simp only [CollatzResearch.WordTrace]
  refine ⟨12798848577709607014145393, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8532565718473071342763595 12798848577709607014145393)
  ·
    refine ⟨9599136433282205260609045, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12798848577709607014145393 9599136433282205260609045)
    ·
      refine ⟨449959520310103371591049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9599136433282205260609045 449959520310103371591049)
      ·
        refine ⟨337469640232577528693287, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 449959520310103371591049 337469640232577528693287)
        ·
          refine ⟨506204460348866293039931, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337469640232577528693287 506204460348866293039931)
          ·
            refine ⟨759306690523299439559897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506204460348866293039931 759306690523299439559897)
            ·
              refine ⟨569480017892474579669923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 759306690523299439559897 569480017892474579669923)
              ·
                refine ⟨854220026838711869504885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 569480017892474579669923 854220026838711869504885)
                ·
                  refine ⟨80083127516129237766083, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854220026838711869504885 80083127516129237766083)
                  ·
                    rfl

theorem cell21_350913_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 2, 1, 1, 2, 1, 5].length) (baseStart_350913 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350913 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350913 prefixEnd_350913 := by exact prefixLift 350913
  have htrace : WordTrace (prefixWord ++ tailWord_350913) baseStart_350913 baseEnd_350913 := by
    simpa [prefixWord, tailWord_350913, baseEnd_350913] using wordTrace_append hprefix tailTrace_350913
  have hstable : (prefixWord ++ tailWord_350913).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350913).length < 2 ^ (prefixWord ++ tailWord_350913).sum := by decide
  have hdescent : baseEnd_350913 < baseStart_350913 := by decide
  rcases family_descends (prefixWord ++ tailWord_350913) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_350938 : List Nat := [3, 1, 1, 2, 2, 2, 1, 4, 5]
def baseStart_350938 : Nat := 118140960795 + 350938 * 2 ^ 59
def prefixEnd_350938 : Nat := 4983230072969 + 3 ^ 40 * 350938 * 2
def baseEnd_350938 : Nat := 80088832856734749849365

theorem tailTrace_350938 : CollatzResearch.WordTrace tailWord_350938 prefixEnd_350938 80088832856734749849365 := by
  unfold tailWord_350938
  simp only [CollatzResearch.WordTrace]
  refine ⟨3199940100654759070951367, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8533173601746024189203645 3199940100654759070951367)
  ·
    refine ⟨4799910150982138606427051, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 3199940100654759070951367 4799910150982138606427051)
    ·
      refine ⟨7199865226473207909640577, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4799910150982138606427051 7199865226473207909640577)
      ·
        refine ⟨5399898919854905932230433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7199865226473207909640577 5399898919854905932230433)
        ·
          refine ⟨4049924189891179449172825, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5399898919854905932230433 4049924189891179449172825)
          ·
            refine ⟨3037443142418384586879619, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4049924189891179449172825 3037443142418384586879619)
            ·
              refine ⟨4556164713627576880319429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 3037443142418384586879619 4556164713627576880319429)
              ·
                refine ⟨854280883805170665059893, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 4556164713627576880319429 854280883805170665059893)
                ·
                  refine ⟨80088832856734749849365, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854280883805170665059893 80088832856734749849365)
                  ·
                    rfl

theorem cell21_350938_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 1, 4, 5].length) (baseStart_350938 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_350938 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_350938 prefixEnd_350938 := by exact prefixLift 350938
  have htrace : WordTrace (prefixWord ++ tailWord_350938) baseStart_350938 baseEnd_350938 := by
    simpa [prefixWord, tailWord_350938, baseEnd_350938] using wordTrace_append hprefix tailTrace_350938
  have hstable : (prefixWord ++ tailWord_350938).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_350938).length < 2 ^ (prefixWord ++ tailWord_350938).sum := by decide
  have hdescent : baseEnd_350938 < baseStart_350938 := by decide
  rcases family_descends (prefixWord ++ tailWord_350938) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351031 : List Nat := [1, 1, 3, 1, 2, 1, 5, 4, 3]
def baseStart_351031 : Nat := 118140960795 + 351031 * 2 ^ 59
def prefixEnd_351031 : Nat := 4983230072969 + 3 ^ 40 * 351031 * 2
def baseEnd_351031 : Nat := 80110056723787254799175

theorem tailTrace_351031 : CollatzResearch.WordTrace tailWord_351031 prefixEnd_351031 80110056723787254799175 := by
  unfold tailWord_351031
  simp only [CollatzResearch.WordTrace]
  refine ⟨12803152391282113166940947, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8535434927521408777960631 12803152391282113166940947)
  ·
    refine ⟨19204728586923169750411421, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12803152391282113166940947 19204728586923169750411421)
    ·
      refine ⟨7201773220096188656404283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 19204728586923169750411421 7201773220096188656404283)
      ·
        refine ⟨10802659830144282984606425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7201773220096188656404283 10802659830144282984606425)
        ·
          refine ⟨8101994872608212238454819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 10802659830144282984606425 8101994872608212238454819)
          ·
            refine ⟨12152992308912318357682229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8101994872608212238454819 12152992308912318357682229)
            ·
              refine ⟨1139343028960529846032709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 12152992308912318357682229 1139343028960529846032709)
              ·
                refine ⟨213626817930099346131133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 1139343028960529846032709 213626817930099346131133)
                ·
                  refine ⟨80110056723787254799175, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213626817930099346131133 80110056723787254799175)
                  ·
                    rfl

theorem cell21_351031_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 5, 4, 3].length) (baseStart_351031 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351031 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351031 prefixEnd_351031 := by exact prefixLift 351031
  have htrace : WordTrace (prefixWord ++ tailWord_351031) baseStart_351031 baseEnd_351031 := by
    simpa [prefixWord, tailWord_351031, baseEnd_351031] using wordTrace_append hprefix tailTrace_351031
  have hstable : (prefixWord ++ tailWord_351031).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351031).length < 2 ^ (prefixWord ++ tailWord_351031).sum := by decide
  have hdescent : baseEnd_351031 < baseStart_351031 := by decide
  rcases family_descends (prefixWord ++ tailWord_351031) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351090 : List Nat := [3, 2, 1, 2, 1, 1, 3, 3, 5]
def baseStart_351090 : Nat := 118140960795 + 351090 * 2 ^ 59
def prefixEnd_351090 : Nat := 4983230072969 + 3 ^ 40 * 351090 * 2
def baseEnd_351090 : Nat := 80123521327616263315721

theorem tailTrace_351090 : CollatzResearch.WordTrace tailWord_351090 prefixEnd_351090 80123521327616263315721 := by
  unfold tailWord_351090
  simp only [CollatzResearch.WordTrace]
  refine ⟨3201326074517091560834681, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8536869532045577495559149 3201326074517091560834681)
  ·
    refine ⟨2400994555887818670626011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3201326074517091560834681 2400994555887818670626011)
    ·
      refine ⟨3601491833831728005939017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2400994555887818670626011 3601491833831728005939017)
      ·
        refine ⟨2701118875373796004454263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 3601491833831728005939017 2701118875373796004454263)
        ·
          refine ⟨4051678313060694006681395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701118875373796004454263 4051678313060694006681395)
          ·
            refine ⟨6077517469591041010022093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4051678313060694006681395 6077517469591041010022093)
            ·
              refine ⟨2279069051096640378758285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 6077517469591041010022093 2279069051096640378758285)
              ·
                refine ⟨854650894161240142034357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 2279069051096640378758285 854650894161240142034357)
                ·
                  refine ⟨80123521327616263315721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 854650894161240142034357 80123521327616263315721)
                  ·
                    rfl

theorem cell21_351090_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 1, 1, 3, 3, 5].length) (baseStart_351090 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351090 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351090 prefixEnd_351090 := by exact prefixLift 351090
  have htrace : WordTrace (prefixWord ++ tailWord_351090) baseStart_351090 baseEnd_351090 := by
    simpa [prefixWord, tailWord_351090, baseEnd_351090] using wordTrace_append hprefix tailTrace_351090
  have hstable : (prefixWord ++ tailWord_351090).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351090).length < 2 ^ (prefixWord ++ tailWord_351090).sum := by decide
  have hdescent : baseEnd_351090 < baseStart_351090 := by decide
  rcases family_descends (prefixWord ++ tailWord_351090) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351135 : List Nat := [1, 1, 2, 5, 2, 1, 9]
def baseStart_351135 : Nat := 118140960795 + 351135 * 2 ^ 59
def prefixEnd_351135 : Nat := 4983230072969 + 3 ^ 40 * 351135 * 2
def baseEnd_351135 : Nat := 8903754548967353896181

theorem tailTrace_351135 : CollatzResearch.WordTrace tailWord_351135 prefixEnd_351135 8903754548967353896181 := by
  unfold tailWord_351135
  simp only [CollatzResearch.WordTrace]
  refine ⟨12806945582905338928726859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8537963721936892619151239 12806945582905338928726859)
  ·
    refine ⟨19210418374358008393090289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12806945582905338928726859 19210418374358008393090289)
    ·
      refine ⟨14407813780768506294817717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19210418374358008393090289 14407813780768506294817717)
      ·
        refine ⟨1350732541947047465139161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 14407813780768506294817717 1350732541947047465139161)
        ·
          refine ⟨1013049406460285598854371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 1350732541947047465139161 1013049406460285598854371)
          ·
            refine ⟨1519574109690428398281557, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 1013049406460285598854371 1519574109690428398281557)
            ·
              refine ⟨8903754548967353896181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 1519574109690428398281557 8903754548967353896181)
              ·
                rfl

theorem cell21_351135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 5, 2, 1, 9].length) (baseStart_351135 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351135 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351135 prefixEnd_351135 := by exact prefixLift 351135
  have htrace : WordTrace (prefixWord ++ tailWord_351135) baseStart_351135 baseEnd_351135 := by
    simpa [prefixWord, tailWord_351135, baseEnd_351135] using wordTrace_append hprefix tailTrace_351135
  have hstable : (prefixWord ++ tailWord_351135).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351135).length < 2 ^ (prefixWord ++ tailWord_351135).sum := by decide
  have hdescent : baseEnd_351135 < baseStart_351135 := by decide
  rcases family_descends (prefixWord ++ tailWord_351135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351166 : List Nat := [4, 2, 1, 1, 1, 2, 2, 1, 7]
def baseStart_351166 : Nat := 118140960795 + 351166 * 2 ^ 59
def prefixEnd_351166 : Nat := 4983230072969 + 3 ^ 40 * 351166 * 2
def baseEnd_351166 : Nat := 80140865563057020048899

theorem tailTrace_351166 : CollatzResearch.WordTrace tailWord_351166 prefixEnd_351166 80140865563057020048899 := by
  unfold tailWord_351166
  simp only [CollatzResearch.WordTrace]
  refine ⟨1601009530724128902888169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 8538717497195354148736901 1601009530724128902888169)
  ·
    refine ⟨1200757148043096677166127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 1601009530724128902888169 1200757148043096677166127)
    ·
      refine ⟨1801135722064645015749191, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 1200757148043096677166127 1801135722064645015749191)
      ·
        refine ⟨2701703583096967523623787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1801135722064645015749191 2701703583096967523623787)
        ·
          refine ⟨4052555374645451285435681, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 2701703583096967523623787 4052555374645451285435681)
          ·
            refine ⟨3039416530984088464076761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 4052555374645451285435681 3039416530984088464076761)
            ·
              refine ⟨2279562398238066348057571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 3039416530984088464076761 2279562398238066348057571)
              ·
                refine ⟨3419343597357099522086357, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 2279562398238066348057571 3419343597357099522086357)
                ·
                  refine ⟨80140865563057020048899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3419343597357099522086357 80140865563057020048899)
                  ·
                    rfl

theorem cell21_351166_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 1, 2, 2, 1, 7].length) (baseStart_351166 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351166 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351166 prefixEnd_351166 := by exact prefixLift 351166
  have htrace : WordTrace (prefixWord ++ tailWord_351166) baseStart_351166 baseEnd_351166 := by
    simpa [prefixWord, tailWord_351166, baseEnd_351166] using wordTrace_append hprefix tailTrace_351166
  have hstable : (prefixWord ++ tailWord_351166).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351166).length < 2 ^ (prefixWord ++ tailWord_351166).sum := by decide
  have hdescent : baseEnd_351166 < baseStart_351166 := by decide
  rcases family_descends (prefixWord ++ tailWord_351166) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351220 : List Nat := [2, 6, 2, 1, 1, 1, 3, 5]
def baseStart_351220 : Nat := 118140960795 + 351220 * 2 ^ 59
def prefixEnd_351220 : Nat := 4983230072969 + 3 ^ 40 * 351220 * 2
def baseEnd_351220 : Nat := 26717729699588308716263

theorem tailTrace_351220 : CollatzResearch.WordTrace tailWord_351220 prefixEnd_351220 26717729699588308716263 := by
  unfold tailWord_351220
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405022893798699222785557, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8540030525064932297047409 6405022893798699222785557)
  ·
    refine ⟨300235448146814026068073, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 6405022893798699222785557 300235448146814026068073)
    ·
      refine ⟨225176586110110519551055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 300235448146814026068073 225176586110110519551055)
      ·
        refine ⟨337764879165165779326583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 225176586110110519551055 337764879165165779326583)
        ·
          refine ⟨506647318747748668989875, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337764879165165779326583 506647318747748668989875)
          ·
            refine ⟨759970978121623003484813, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506647318747748668989875 759970978121623003484813)
            ·
              refine ⟨284989116795608626306805, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759970978121623003484813 284989116795608626306805)
              ·
                refine ⟨26717729699588308716263, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 284989116795608626306805 26717729699588308716263)
                ·
                  rfl

theorem cell21_351220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 2, 1, 1, 1, 3, 5].length) (baseStart_351220 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351220 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351220 prefixEnd_351220 := by exact prefixLift 351220
  have htrace : WordTrace (prefixWord ++ tailWord_351220) baseStart_351220 baseEnd_351220 := by
    simpa [prefixWord, tailWord_351220, baseEnd_351220] using wordTrace_append hprefix tailTrace_351220
  have hstable : (prefixWord ++ tailWord_351220).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351220).length < 2 ^ (prefixWord ++ tailWord_351220).sum := by decide
  have hdescent : baseEnd_351220 < baseStart_351220 := by decide
  rcases family_descends (prefixWord ++ tailWord_351220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351228 : List Nat := [2, 2, 2, 1, 2, 4, 3, 5]
def baseStart_351228 : Nat := 118140960795 + 351228 * 2 ^ 59
def prefixEnd_351228 : Nat := 4983230072969 + 3 ^ 40 * 351228 * 2
def baseEnd_351228 : Nat := 26718338269252896671813

theorem tailTrace_351228 : CollatzResearch.WordTrace tailWord_351228 prefixEnd_351228 26718338269252896671813 := by
  unfold tailWord_351228
  simp only [CollatzResearch.WordTrace]
  refine ⟨6405168785784207905931169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8540225047712277207908225 6405168785784207905931169)
  ·
    refine ⟨4803876589338155929448377, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 6405168785784207905931169 4803876589338155929448377)
    ·
      refine ⟨3602907442003616947086283, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 4803876589338155929448377 3602907442003616947086283)
      ·
        refine ⟨5404361163005425420629425, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3602907442003616947086283 5404361163005425420629425)
        ·
          refine ⟨4053270872254069065472069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5404361163005425420629425 4053270872254069065472069)
          ·
            refine ⟨759988288547637949776013, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 4053270872254069065472069 759988288547637949776013)
            ·
              refine ⟨284995608205364231166005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 759988288547637949776013 284995608205364231166005)
              ·
                refine ⟨26718338269252896671813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 284995608205364231166005 26718338269252896671813)
                ·
                  rfl

theorem cell21_351228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 4, 3, 5].length) (baseStart_351228 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351228 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351228 prefixEnd_351228 := by exact prefixLift 351228
  have htrace : WordTrace (prefixWord ++ tailWord_351228) baseStart_351228 baseEnd_351228 := by
    simpa [prefixWord, tailWord_351228, baseEnd_351228] using wordTrace_append hprefix tailTrace_351228
  have hstable : (prefixWord ++ tailWord_351228).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351228).length < 2 ^ (prefixWord ++ tailWord_351228).sum := by decide
  have hdescent : baseEnd_351228 < baseStart_351228 := by decide
  rcases family_descends (prefixWord ++ tailWord_351228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351234 : List Nat := [3, 4, 1, 3, 1, 1, 2, 3, 3]
def baseStart_351234 : Nat := 118140960795 + 351234 * 2 ^ 59
def prefixEnd_351234 : Nat := 4983230072969 + 3 ^ 40 * 351234 * 2
def baseEnd_351234 : Nat := 80156384089504012915427

theorem tailTrace_351234 : CollatzResearch.WordTrace tailWord_351234 prefixEnd_351234 80156384089504012915427 := by
  unfold tailWord_351234
  simp only [CollatzResearch.WordTrace]
  refine ⟨3202639102386669709145189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8540370939697785891053837 3202639102386669709145189)
  ·
    refine ⟨600494831697500570464723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 3202639102386669709145189 600494831697500570464723)
    ·
      refine ⟨900742247546250855697085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 600494831697500570464723 900742247546250855697085)
      ·
        refine ⟨337778342829844070886407, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 900742247546250855697085 337778342829844070886407)
        ·
          refine ⟨506667514244766106329611, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 337778342829844070886407 506667514244766106329611)
          ·
            refine ⟨760001271367149159494417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 506667514244766106329611 760001271367149159494417)
            ·
              refine ⟨570000953525361869620813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 760001271367149159494417 570000953525361869620813)
              ·
                refine ⟨213750357572010701107805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 570000953525361869620813 213750357572010701107805)
                ·
                  refine ⟨80156384089504012915427, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 213750357572010701107805 80156384089504012915427)
                  ·
                    rfl

theorem cell21_351234_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 3, 1, 1, 2, 3, 3].length) (baseStart_351234 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351234 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351234 prefixEnd_351234 := by exact prefixLift 351234
  have htrace : WordTrace (prefixWord ++ tailWord_351234) baseStart_351234 baseEnd_351234 := by
    simpa [prefixWord, tailWord_351234, baseEnd_351234] using wordTrace_append hprefix tailTrace_351234
  have hstable : (prefixWord ++ tailWord_351234).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351234).length < 2 ^ (prefixWord ++ tailWord_351234).sum := by decide
  have hdescent : baseEnd_351234 < baseStart_351234 := by decide
  rcases family_descends (prefixWord ++ tailWord_351234) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351301 : List Nat := [1, 3, 1, 1, 1, 3, 2, 2, 7]
def baseStart_351301 : Nat := 118140960795 + 351301 * 2 ^ 59
def prefixEnd_351301 : Nat := 4983230072969 + 3 ^ 40 * 351301 * 2
def baseEnd_351301 : Nat := 80171674402326785298623

theorem tailTrace_351301 : CollatzResearch.WordTrace tailWord_351301 prefixEnd_351301 80171674402326785298623 := by
  unfold tailWord_351301
  simp only [CollatzResearch.WordTrace]
  refine ⟨12813000100303949279269757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8542000066869299519513171 12813000100303949279269757)
  ·
    refine ⟨4804875037613980979726159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 12813000100303949279269757 4804875037613980979726159)
    ·
      refine ⟨7207312556420971469589239, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 4804875037613980979726159 7207312556420971469589239)
      ·
        refine ⟨10810968834631457204383859, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7207312556420971469589239 10810968834631457204383859)
        ·
          refine ⟨16216453251947185806575789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 10810968834631457204383859 16216453251947185806575789)
          ·
            refine ⟨6081169969480194677465921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16216453251947185806575789 6081169969480194677465921)
            ·
              refine ⟨4560877477110146008099441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6081169969480194677465921 4560877477110146008099441)
              ·
                refine ⟨3420658107832609506074581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4560877477110146008099441 3420658107832609506074581)
                ·
                  refine ⟨80171674402326785298623, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 3420658107832609506074581 80171674402326785298623)
                  ·
                    rfl

theorem cell21_351301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 2, 7].length) (baseStart_351301 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351301 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351301 prefixEnd_351301 := by exact prefixLift 351301
  have htrace : WordTrace (prefixWord ++ tailWord_351301) baseStart_351301 baseEnd_351301 := by
    simpa [prefixWord, tailWord_351301, baseEnd_351301] using wordTrace_append hprefix tailTrace_351301
  have hstable : (prefixWord ++ tailWord_351301).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351301).length < 2 ^ (prefixWord ++ tailWord_351301).sum := by decide
  have hdescent : baseEnd_351301 < baseStart_351301 := by decide
  rcases family_descends (prefixWord ++ tailWord_351301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351442 : List Nat := [3, 2, 2, 2, 1, 1, 5, 1, 4]
def baseStart_351442 : Nat := 118140960795 + 351442 * 2 ^ 59
def prefixEnd_351442 : Nat := 4983230072969 + 3 ^ 40 * 351442 * 2
def baseEnd_351442 : Nat := 80203852523341873448335

theorem tailTrace_351442 : CollatzResearch.WordTrace tailWord_351442 prefixEnd_351442 80203852523341873448335 := by
  unfold tailWord_351442
  simp only [CollatzResearch.WordTrace]
  refine ⟨3204535698198282590038145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 8545428528528753573435053 3204535698198282590038145)
  ·
    refine ⟨2403401773648711942528609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 3204535698198282590038145 2403401773648711942528609)
    ·
      refine ⟨1802551330236533956896457, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 2403401773648711942528609 1802551330236533956896457)
      ·
        refine ⟨1351913497677400467672343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 1802551330236533956896457 1351913497677400467672343)
        ·
          refine ⟨2027870246516100701508515, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 1351913497677400467672343 2027870246516100701508515)
          ·
            refine ⟨3041805369774151052262773, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 2027870246516100701508515 3041805369774151052262773)
            ·
              refine ⟨285169253416326661149635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 3041805369774151052262773 285169253416326661149635)
              ·
                refine ⟨427753880124489991724453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 285169253416326661149635 427753880124489991724453)
                ·
                  refine ⟨80203852523341873448335, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 427753880124489991724453 80203852523341873448335)
                  ·
                    rfl

theorem cell21_351442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 1, 5, 1, 4].length) (baseStart_351442 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351442 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351442 prefixEnd_351442 := by exact prefixLift 351442
  have htrace : WordTrace (prefixWord ++ tailWord_351442) baseStart_351442 baseEnd_351442 := by
    simpa [prefixWord, tailWord_351442, baseEnd_351442] using wordTrace_append hprefix tailTrace_351442
  have hstable : (prefixWord ++ tailWord_351442).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351442).length < 2 ^ (prefixWord ++ tailWord_351442).sum := by decide
  have hdescent : baseEnd_351442 < baseStart_351442 := by decide
  rcases family_descends (prefixWord ++ tailWord_351442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351456 : List Nat := [2, 1, 1, 3, 1, 6, 2, 5]
def baseStart_351456 : Nat := 118140960795 + 351456 * 2 ^ 59
def prefixEnd_351456 : Nat := 4983230072969 + 3 ^ 40 * 351456 * 2
def baseEnd_351456 : Nat := 26735682504693653404991

theorem tailTrace_351456 : CollatzResearch.WordTrace tailWord_351456 prefixEnd_351456 26735682504693653404991 := by
  unfold tailWord_351456
  simp only [CollatzResearch.WordTrace]
  refine ⟨6409326707371205375581111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8545768943161607167441481 6409326707371205375581111)
  ·
    refine ⟨9613990061056808063371667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6409326707371205375581111 9613990061056808063371667)
    ·
      refine ⟨14420985091585212095057501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9613990061056808063371667 14420985091585212095057501)
      ·
        refine ⟨5407869409344454535646563, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 14420985091585212095057501 5407869409344454535646563)
        ·
          refine ⟨8111804114016681803469845, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5407869409344454535646563 8111804114016681803469845)
          ·
            refine ⟨380240817844531959537649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 8111804114016681803469845 380240817844531959537649)
            ·
              refine ⟨285180613383398969653237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380240817844531959537649 285180613383398969653237)
              ·
                refine ⟨26735682504693653404991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285180613383398969653237 26735682504693653404991)
                ·
                  rfl

theorem cell21_351456_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 6, 2, 5].length) (baseStart_351456 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351456 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351456 prefixEnd_351456 := by exact prefixLift 351456
  have htrace : WordTrace (prefixWord ++ tailWord_351456) baseStart_351456 baseEnd_351456 := by
    simpa [prefixWord, tailWord_351456, baseEnd_351456] using wordTrace_append hprefix tailTrace_351456
  have hstable : (prefixWord ++ tailWord_351456).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351456).length < 2 ^ (prefixWord ++ tailWord_351456).sum := by decide
  have hdescent : baseEnd_351456 < baseStart_351456 := by decide
  rcases family_descends (prefixWord ++ tailWord_351456) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351549 : List Nat := [1, 4, 1, 5, 1, 2, 1, 6]
def baseStart_351549 : Nat := 118140960795 + 351549 * 2 ^ 59
def prefixEnd_351549 : Nat := 4983230072969 + 3 ^ 40 * 351549 * 2
def baseEnd_351549 : Nat := 26742757127044488388261

theorem tailTrace_351549 : CollatzResearch.WordTrace tailWord_351549 prefixEnd_351549 26742757127044488388261 := by
  unfold tailWord_351549
  simp only [CollatzResearch.WordTrace]
  refine ⟨12822045403405487634297701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8548030268936991756198467 12822045403405487634297701)
  ·
    refine ⟨2404133513138528931430819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 12822045403405487634297701 2404133513138528931430819)
    ·
      refine ⟨3606200269707793397146229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 2404133513138528931430819 3606200269707793397146229)
      ·
        refine ⟨338081275285105630982459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 3606200269707793397146229 338081275285105630982459)
        ·
          refine ⟨507121912927658446473689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 338081275285105630982459 507121912927658446473689)
          ·
            refine ⟨380341434695743834855267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507121912927658446473689 380341434695743834855267)
            ·
              refine ⟨570512152043615752282901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380341434695743834855267 570512152043615752282901)
              ·
                refine ⟨26742757127044488388261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 570512152043615752282901 26742757127044488388261)
                ·
                  rfl

theorem cell21_351549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 5, 1, 2, 1, 6].length) (baseStart_351549 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351549 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351549 prefixEnd_351549 := by exact prefixLift 351549
  have htrace : WordTrace (prefixWord ++ tailWord_351549) baseStart_351549 baseEnd_351549 := by
    simpa [prefixWord, tailWord_351549, baseEnd_351549] using wordTrace_append hprefix tailTrace_351549
  have hstable : (prefixWord ++ tailWord_351549).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351549).length < 2 ^ (prefixWord ++ tailWord_351549).sum := by decide
  have hdescent : baseEnd_351549 < baseStart_351549 := by decide
  rcases family_descends (prefixWord ++ tailWord_351549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351591 : List Nat := [1, 1, 5, 1, 4, 1, 8]
def baseStart_351591 : Nat := 118140960795 + 351591 * 2 ^ 59
def prefixEnd_351591 : Nat := 4983230072969 + 3 ^ 40 * 351591 * 2
def baseEnd_351591 : Nat := 8915317372594525051633

theorem tailTrace_351591 : CollatzResearch.WordTrace tailWord_351591 prefixEnd_351591 8915317372594525051633 := by
  unfold tailWord_351591
  simp only [CollatzResearch.WordTrace]
  refine ⟨12823577269253328807326627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8549051512835552538217751 12823577269253328807326627)
  ·
    refine ⟨19235365903879993210989941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12823577269253328807326627 19235365903879993210989941)
    ·
      refine ⟨1803315553488749363530307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 19235365903879993210989941 1803315553488749363530307)
      ·
        refine ⟨2704973330233124045295461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 1803315553488749363530307 2704973330233124045295461)
        ·
          refine ⟨507182499418710758492899, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 2704973330233124045295461 507182499418710758492899)
          ·
            refine ⟨760773749128066137739349, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 507182499418710758492899 760773749128066137739349)
            ·
              refine ⟨8915317372594525051633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 8 760773749128066137739349 8915317372594525051633)
              ·
                rfl

theorem cell21_351591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 4, 1, 8].length) (baseStart_351591 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351591 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351591 prefixEnd_351591 := by exact prefixLift 351591
  have htrace : WordTrace (prefixWord ++ tailWord_351591) baseStart_351591 baseEnd_351591 := by
    simpa [prefixWord, tailWord_351591, baseEnd_351591] using wordTrace_append hprefix tailTrace_351591
  have hstable : (prefixWord ++ tailWord_351591).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351591).length < 2 ^ (prefixWord ++ tailWord_351591).sum := by decide
  have hdescent : baseEnd_351591 < baseStart_351591 := by decide
  rcases family_descends (prefixWord ++ tailWord_351591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351625 : List Nat := [1, 2, 1, 1, 8, 1, 2, 5]
def baseStart_351625 : Nat := 118140960795 + 351625 * 2 ^ 59
def prefixEnd_351625 : Nat := 4983230072969 + 3 ^ 40 * 351625 * 2
def baseEnd_351625 : Nat := 26748538538858073965987

theorem tailTrace_351625 : CollatzResearch.WordTrace tailWord_351625 prefixEnd_351625 26748538538858073965987 := by
  unfold tailWord_351625
  simp only [CollatzResearch.WordTrace]
  refine ⟨12824817351130152614064329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8549878234086768409376219 12824817351130152614064329)
  ·
    refine ⟨9618613013347614460548247, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 12824817351130152614064329 9618613013347614460548247)
    ·
      refine ⟨14427919520021421690822371, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 9618613013347614460548247 14427919520021421690822371)
      ·
        refine ⟨21641879280032132536233557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14427919520021421690822371 21641879280032132536233557)
        ·
          refine ⟨253615772812876553158987, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 8 21641879280032132536233557 253615772812876553158987)
          ·
            refine ⟨380423659219314829738481, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 253615772812876553158987 380423659219314829738481)
            ·
              refine ⟨285317744414486122303861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 380423659219314829738481 285317744414486122303861)
              ·
                refine ⟨26748538538858073965987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 285317744414486122303861 26748538538858073965987)
                ·
                  rfl

theorem cell21_351625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 8, 1, 2, 5].length) (baseStart_351625 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351625 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351625 prefixEnd_351625 := by exact prefixLift 351625
  have htrace : WordTrace (prefixWord ++ tailWord_351625) baseStart_351625 baseEnd_351625 := by
    simpa [prefixWord, tailWord_351625, baseEnd_351625] using wordTrace_append hprefix tailTrace_351625
  have hstable : (prefixWord ++ tailWord_351625).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351625).length < 2 ^ (prefixWord ++ tailWord_351625).sum := by decide
  have hdescent : baseEnd_351625 < baseStart_351625 := by decide
  rcases family_descends (prefixWord ++ tailWord_351625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351656 : List Nat := [2, 1, 6, 1, 2, 2, 1, 1, 5]
def baseStart_351656 : Nat := 118140960795 + 351656 * 2 ^ 59
def prefixEnd_351656 : Nat := 4983230072969 + 3 ^ 40 * 351656 * 2
def baseEnd_351656 : Nat := 80252690238925056881231

theorem tailTrace_351656 : CollatzResearch.WordTrace tailWord_351656 prefixEnd_351656 80252690238925056881231 := by
  unfold tailWord_351656
  simp only [CollatzResearch.WordTrace]
  refine ⟨6412974007008922454221411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 8550632009345229938961881 6412974007008922454221411)
  ·
    refine ⟨9619461010513383681332117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6412974007008922454221411 9619461010513383681332117)
    ·
      refine ⟨450912234867814860062443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 9619461010513383681332117 450912234867814860062443)
      ·
        refine ⟨676368352301722290093665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 450912234867814860062443 676368352301722290093665)
        ·
          refine ⟨507276264226291717570249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 676368352301722290093665 507276264226291717570249)
          ·
            refine ⟨380457198169718788177687, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 507276264226291717570249 380457198169718788177687)
            ·
              refine ⟨570685797254578182266531, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 380457198169718788177687 570685797254578182266531)
              ·
                refine ⟨856028695881867273399797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 570685797254578182266531 856028695881867273399797)
                ·
                  refine ⟨80252690238925056881231, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 856028695881867273399797 80252690238925056881231)
                  ·
                    rfl

theorem cell21_351656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 2, 2, 1, 1, 5].length) (baseStart_351656 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351656 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351656 prefixEnd_351656 := by exact prefixLift 351656
  have htrace : WordTrace (prefixWord ++ tailWord_351656) baseStart_351656 baseEnd_351656 := by
    simpa [prefixWord, tailWord_351656, baseEnd_351656] using wordTrace_append hprefix tailTrace_351656
  have hstable : (prefixWord ++ tailWord_351656).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351656).length < 2 ^ (prefixWord ++ tailWord_351656).sum := by decide
  have hdescent : baseEnd_351656 < baseStart_351656 := by decide
  rcases family_descends (prefixWord ++ tailWord_351656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_351695 : List Nat := [1, 1, 2, 1, 1, 4, 2, 1, 8]
def baseStart_351695 : Nat := 118140960795 + 351695 * 2 ^ 59
def prefixEnd_351695 : Nat := 4983230072969 + 3 ^ 40 * 351695 * 2
def baseEnd_351695 : Nat := 80261590570269655731151

theorem tailTrace_351695 : CollatzResearch.WordTrace tailWord_351695 prefixEnd_351695 80261590570269655731151 := by
  unfold tailWord_351695
  simp only [CollatzResearch.WordTrace]
  refine ⟨12827370460876554569112539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 8551580307251036379408359 12827370460876554569112539)
  ·
    refine ⟨19241055691314831853668809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 12827370460876554569112539 19241055691314831853668809)
    ·
      refine ⟨14430791768486123890251607, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 19241055691314831853668809 14430791768486123890251607)
      ·
        refine ⟨21646187652729185835377411, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 14430791768486123890251607 21646187652729185835377411)
        ·
          refine ⟨32469281479093778753066117, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 21646187652729185835377411 32469281479093778753066117)
          ·
            refine ⟨6087990277330083516199897, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 32469281479093778753066117 6087990277330083516199897)
            ·
              refine ⟨4565992707997562637149923, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6087990277330083516199897 4565992707997562637149923)
              ·
                refine ⟨6848989061996343955724885, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4565992707997562637149923 6848989061996343955724885)
                ·
                  refine ⟨80261590570269655731151, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 6848989061996343955724885 80261590570269655731151)
                  ·
                    rfl

theorem cell21_351695_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 2, 1, 8].length) (baseStart_351695 + u * 2 ^ 80) = endpoint ∧
      endpoint < baseStart_351695 + u * 2 ^ 80 := by
  have hprefix : WordTrace prefixWord baseStart_351695 prefixEnd_351695 := by exact prefixLift 351695
  have htrace : WordTrace (prefixWord ++ tailWord_351695) baseStart_351695 baseEnd_351695 := by
    simpa [prefixWord, tailWord_351695, baseEnd_351695] using wordTrace_append hprefix tailTrace_351695
  have hstable : (prefixWord ++ tailWord_351695).sum < 80 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_351695).length < 2 ^ (prefixWord ++ tailWord_351695).sum := by decide
  have hdescent : baseEnd_351695 < baseStart_351695 := by decide
  rcases family_descends (prefixWord ++ tailWord_351695) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan21Incremental
