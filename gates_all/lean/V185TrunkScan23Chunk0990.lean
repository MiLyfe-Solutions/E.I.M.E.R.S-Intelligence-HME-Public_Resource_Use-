import V185TrunkScan23Chunk0989

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_5860954 : List Nat := [3, 1, 1, 2, 1, 1, 1, 4, 5, 4]
def baseStart_5860954 : Nat := 118140960795 + 5860954 * 2 ^ 59
def prefixEnd_5860954 : Nat := 4983230072969 + 3 ^ 40 * 5860954 * 2
def baseEnd_5860954 : Nat := 1003162165297189074740323

theorem tailTrace_5860954 : CollatzResearch.WordTrace tailWord_5860954 prefixEnd_5860954 1003162165297189074740323 := by
  unfold tailWord_5860954
  simp only [CollatzResearch.WordTrace]
  refine ⟨53441638502193026024229479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142511036005848069397945277 53441638502193026024229479)
  ·
    refine ⟨80162457753289539036344219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53441638502193026024229479 80162457753289539036344219)
    ·
      refine ⟨120243686629934308554516329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80162457753289539036344219 120243686629934308554516329)
      ·
        refine ⟨90182764972450731415887247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120243686629934308554516329 90182764972450731415887247)
        ·
          refine ⟨135274147458676097123830871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90182764972450731415887247 135274147458676097123830871)
          ·
            refine ⟨202911221188014145685746307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135274147458676097123830871 202911221188014145685746307)
            ·
              refine ⟨304366831782021218528619461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202911221188014145685746307 304366831782021218528619461)
              ·
                refine ⟨57068780959128978474116149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304366831782021218528619461 57068780959128978474116149)
                ·
                  refine ⟨5350198214918341731948389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57068780959128978474116149 5350198214918341731948389)
                  ·
                    refine ⟨1003162165297189074740323, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350198214918341731948389 1003162165297189074740323)
                    ·
                      rfl

theorem cell23_5860954_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 1, 1, 4, 5, 4].length) (baseStart_5860954 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5860954 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5860954 prefixEnd_5860954 := by exact prefixLift 5860954
  have htrace : WordTrace (prefixWord ++ tailWord_5860954) baseStart_5860954 baseEnd_5860954 := by
    simpa [prefixWord, tailWord_5860954, baseEnd_5860954] using wordTrace_append hprefix tailTrace_5860954
  have hstable : (prefixWord ++ tailWord_5860954).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5860954).length < 2 ^ (prefixWord ++ tailWord_5860954).sum := by decide
  have hdescent : baseEnd_5860954 < baseStart_5860954 := by decide
  rcases family_descends (prefixWord ++ tailWord_5860954) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861021 : List Nat := [1, 4, 2, 1, 1, 1, 1, 2, 3, 5, 2]
def baseStart_5861021 : Nat := 118140960795 + 5861021 * 2 ^ 59
def prefixEnd_5861021 : Nat := 4983230072969 + 3 ^ 40 * 5861021 * 2
def baseEnd_5861021 : Nat := 3009520899095418462083161

theorem tailTrace_5861021 : CollatzResearch.WordTrace tailWord_5861021 prefixEnd_5861021 3009520899095418462083161 := by
  unfold tailWord_5861021
  simp only [CollatzResearch.WordTrace]
  refine ⟨213768997699529374539606917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142512665133019583026404611 213768997699529374539606917)
  ·
    refine ⟨40081687068661757726176297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213768997699529374539606917 40081687068661757726176297)
    ·
      refine ⟨30061265301496318294632223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40081687068661757726176297 30061265301496318294632223)
      ·
        refine ⟨45091897952244477441948335, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30061265301496318294632223 45091897952244477441948335)
        ·
          refine ⟨67637846928366716162922503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45091897952244477441948335 67637846928366716162922503)
          ·
            refine ⟨101456770392550074244383755, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67637846928366716162922503 101456770392550074244383755)
            ·
              refine ⟨152185155588825111366575633, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101456770392550074244383755 152185155588825111366575633)
              ·
                refine ⟨114138866691618833524931725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152185155588825111366575633 114138866691618833524931725)
                ·
                  refine ⟨42802075009357062571849397, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114138866691618833524931725 42802075009357062571849397)
                  ·
                    refine ⟨4012694532127224616110881, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42802075009357062571849397 4012694532127224616110881)
                    ·
                      refine ⟨3009520899095418462083161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012694532127224616110881 3009520899095418462083161)
                      ·
                        rfl

theorem cell23_5861021_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 2, 3, 5, 2].length) (baseStart_5861021 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861021 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861021 prefixEnd_5861021 := by exact prefixLift 5861021
  have htrace : WordTrace (prefixWord ++ tailWord_5861021) baseStart_5861021 baseEnd_5861021 := by
    simpa [prefixWord, tailWord_5861021, baseEnd_5861021] using wordTrace_append hprefix tailTrace_5861021
  have hstable : (prefixWord ++ tailWord_5861021).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861021).length < 2 ^ (prefixWord ++ tailWord_5861021).sum := by decide
  have hdescent : baseEnd_5861021 < baseStart_5861021 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861021) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861022 : List Nat := [4, 3, 1, 1, 1, 2, 4, 2, 1, 4]
def baseStart_5861022 : Nat := 118140960795 + 5861022 * 2 ^ 59
def prefixEnd_5861022 : Nat := 4983230072969 + 3 ^ 40 * 5861022 * 2
def baseEnd_5861022 : Nat := 1003173804192024319390219

theorem tailTrace_5861022 : CollatzResearch.WordTrace tailWord_5861022 prefixEnd_5861022 1003173804192024319390219 := by
  unfold tailWord_5861022
  simp only [CollatzResearch.WordTrace]
  refine ⟨26721129271565718963799165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142512689448350501140262213 26721129271565718963799165)
  ·
    refine ⟨10020423476837144611424687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26721129271565718963799165 10020423476837144611424687)
    ·
      refine ⟨15030635215255716917137031, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10020423476837144611424687 15030635215255716917137031)
      ·
        refine ⟨22545952822883575375705547, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15030635215255716917137031 22545952822883575375705547)
        ·
          refine ⟨33818929234325363063558321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22545952822883575375705547 33818929234325363063558321)
          ·
            refine ⟨25364196925744022297668741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33818929234325363063558321 25364196925744022297668741)
            ·
              refine ⟨4755786923577004180812889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25364196925744022297668741 4755786923577004180812889)
              ·
                refine ⟨3566840192682753135609667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4755786923577004180812889 3566840192682753135609667)
                ·
                  refine ⟨5350260289024129703414501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3566840192682753135609667 5350260289024129703414501)
                  ·
                    refine ⟨1003173804192024319390219, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350260289024129703414501 1003173804192024319390219)
                    ·
                      rfl

theorem cell23_5861022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 2, 4, 2, 1, 4].length) (baseStart_5861022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861022 prefixEnd_5861022 := by exact prefixLift 5861022
  have htrace : WordTrace (prefixWord ++ tailWord_5861022) baseStart_5861022 baseEnd_5861022 := by
    simpa [prefixWord, tailWord_5861022, baseEnd_5861022] using wordTrace_append hprefix tailTrace_5861022
  have hstable : (prefixWord ++ tailWord_5861022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861022).length < 2 ^ (prefixWord ++ tailWord_5861022).sum := by decide
  have hdescent : baseEnd_5861022 < baseStart_5861022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861045 : List Nat := [1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 3]
def baseStart_5861045 : Nat := 118140960795 + 5861045 * 2 ^ 59
def prefixEnd_5861045 : Nat := 4983230072969 + 3 ^ 40 * 5861045 * 2
def baseEnd_5861045 : Nat := 3009533222631126368183051

theorem tailTrace_5861045 : CollatzResearch.WordTrace tailWord_5861045 prefixEnd_5861045 3009533222631126368183051 := by
  unfold tailWord_5861045
  simp only [CollatzResearch.WordTrace]
  refine ⟨213769873051442426638480589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142513248700961617758987059 213769873051442426638480589)
  ·
    refine ⟨80163702394290909989430221, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213769873051442426638480589 80163702394290909989430221)
    ·
      refine ⟨30061388397859091246036333, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80163702394290909989430221 30061388397859091246036333)
      ·
        refine ⟨11273020649197159217263625, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30061388397859091246036333 11273020649197159217263625)
        ·
          refine ⟨8454765486897869412947719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11273020649197159217263625 8454765486897869412947719)
          ·
            refine ⟨12682148230346804119421579, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8454765486897869412947719 12682148230346804119421579)
            ·
              refine ⟨19023222345520206179132369, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12682148230346804119421579 19023222345520206179132369)
              ·
                refine ⟨14267416759140154634349277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19023222345520206179132369 14267416759140154634349277)
                ·
                  refine ⟨5350281284677557987880979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14267416759140154634349277 5350281284677557987880979)
                  ·
                    refine ⟨8025421927016336981821469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5350281284677557987880979 8025421927016336981821469)
                    ·
                      refine ⟨3009533222631126368183051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8025421927016336981821469 3009533222631126368183051)
                      ·
                        rfl

theorem cell23_5861045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_5861045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861045 prefixEnd_5861045 := by exact prefixLift 5861045
  have htrace : WordTrace (prefixWord ++ tailWord_5861045) baseStart_5861045 baseEnd_5861045 := by
    simpa [prefixWord, tailWord_5861045, baseEnd_5861045] using wordTrace_append hprefix tailTrace_5861045
  have hstable : (prefixWord ++ tailWord_5861045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861045).length < 2 ^ (prefixWord ++ tailWord_5861045).sum := by decide
  have hdescent : baseEnd_5861045 < baseStart_5861045 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861095 : List Nat := [1, 1, 5, 4, 1, 2, 1, 1, 1, 6]
def baseStart_5861095 : Nat := 118140960795 + 5861095 * 2 ^ 59
def prefixEnd_5861095 : Nat := 4983230072969 + 3 ^ 40 * 5861095 * 2
def baseEnd_5861095 : Nat := 1003186298887950390852607

theorem tailTrace_5861095 : CollatzResearch.WordTrace tailWord_5861095 prefixEnd_5861095 1003186298887950390852607 := by
  unfold tailWord_5861095
  simp only [CollatzResearch.WordTrace]
  refine ⟨213771696701261285177800739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142514464467507523451867159 213771696701261285177800739)
  ·
    refine ⟨320657545051891927766701109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213771696701261285177800739 320657545051891927766701109)
    ·
      refine ⟨30061644848614868228128229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320657545051891927766701109 30061644848614868228128229)
      ·
        refine ⟨5636558409115287792774043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30061644848614868228128229 5636558409115287792774043)
        ·
          refine ⟨8454837613672931689161065, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636558409115287792774043 8454837613672931689161065)
          ·
            refine ⟨6341128210254698766870799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8454837613672931689161065 6341128210254698766870799)
            ·
              refine ⟨9511692315382048150306199, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341128210254698766870799 9511692315382048150306199)
              ·
                refine ⟨14267538473073072225459299, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9511692315382048150306199 14267538473073072225459299)
                ·
                  refine ⟨21401307709609608338188949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14267538473073072225459299 21401307709609608338188949)
                  ·
                    refine ⟨1003186298887950390852607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21401307709609608338188949 1003186298887950390852607)
                    ·
                      rfl

theorem cell23_5861095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 4, 1, 2, 1, 1, 1, 6].length) (baseStart_5861095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861095 prefixEnd_5861095 := by exact prefixLift 5861095
  have htrace : WordTrace (prefixWord ++ tailWord_5861095) baseStart_5861095 baseEnd_5861095 := by
    simpa [prefixWord, tailWord_5861095, baseEnd_5861095] using wordTrace_append hprefix tailTrace_5861095
  have hstable : (prefixWord ++ tailWord_5861095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861095).length < 2 ^ (prefixWord ++ tailWord_5861095).sum := by decide
  have hdescent : baseEnd_5861095 < baseStart_5861095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861192 : List Nat := [2, 1, 3, 1, 1, 5, 2, 2, 2, 2, 2]
def baseStart_5861192 : Nat := 118140960795 + 5861192 * 2 ^ 59
def prefixEnd_5861192 : Nat := 4983230072969 + 3 ^ 40 * 5861192 * 2
def baseEnd_5861192 : Nat := 3009608704287337293044875

theorem tailTrace_5861192 : CollatzResearch.WordTrace tailWord_5861192 prefixEnd_5861192 3009608704287337293044875 := by
  unfold tailWord_5861192
  simp only [CollatzResearch.WordTrace]
  refine ⟨106887617290954935372040915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142516823054606580496054553 106887617290954935372040915)
  ·
    refine ⟨160331425936432403058061373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106887617290954935372040915 160331425936432403058061373)
    ·
      refine ⟨60124284726162151146773015, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160331425936432403058061373 60124284726162151146773015)
      ·
        refine ⟨90186427089243226720159523, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60124284726162151146773015 90186427089243226720159523)
        ·
          refine ⟨135279640633864840080239285, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90186427089243226720159523 135279640633864840080239285)
          ·
            refine ⟨12682466309424828757522433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135279640633864840080239285 12682466309424828757522433)
            ·
              refine ⟨9511849732068621568141825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12682466309424828757522433 9511849732068621568141825)
              ·
                refine ⟨7133887299051466176106369, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9511849732068621568141825 7133887299051466176106369)
                ·
                  refine ⟨5350415474288599632079777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7133887299051466176106369 5350415474288599632079777)
                  ·
                    refine ⟨4012811605716449724059833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5350415474288599632079777 4012811605716449724059833)
                    ·
                      refine ⟨3009608704287337293044875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012811605716449724059833 3009608704287337293044875)
                      ·
                        rfl

theorem cell23_5861192_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 5, 2, 2, 2, 2, 2].length) (baseStart_5861192 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861192 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861192 prefixEnd_5861192 := by exact prefixLift 5861192
  have htrace : WordTrace (prefixWord ++ tailWord_5861192) baseStart_5861192 baseEnd_5861192 := by
    simpa [prefixWord, tailWord_5861192, baseEnd_5861192] using wordTrace_append hprefix tailTrace_5861192
  have hstable : (prefixWord ++ tailWord_5861192).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861192).length < 2 ^ (prefixWord ++ tailWord_5861192).sum := by decide
  have hdescent : baseEnd_5861192 < baseStart_5861192 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861192) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861228 : List Nat := [2, 2, 1, 1, 4, 2, 3, 1, 2, 5]
def baseStart_5861228 : Nat := 118140960795 + 5861228 * 2 ^ 59
def prefixEnd_5861228 : Nat := 4983230072969 + 3 ^ 40 * 5861228 * 2
def baseEnd_5861228 : Nat := 1003209063196966384064903

theorem tailTrace_5861228 : CollatzResearch.WordTrace tailWord_5861228 prefixEnd_5861228 1003209063196966384064903 := by
  unfold tailWord_5861228
  simp only [CollatzResearch.WordTrace]
  refine ⟨106888273804889724446196169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142517698406519632594928225 106888273804889724446196169)
  ·
    refine ⟨80166205353667293334647127, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106888273804889724446196169 80166205353667293334647127)
    ·
      refine ⟨120249308030500940001970691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80166205353667293334647127 120249308030500940001970691)
      ·
        refine ⟨180373962045751410002956037, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120249308030500940001970691 180373962045751410002956037)
        ·
          refine ⟨33820117883578389375554257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180373962045751410002956037 33820117883578389375554257)
          ·
            refine ⟨25365088412683792031665693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33820117883578389375554257 25365088412683792031665693)
            ·
              refine ⟨9511908154756422011874635, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25365088412683792031665693 9511908154756422011874635)
              ·
                refine ⟨14267862232134633017811953, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9511908154756422011874635 14267862232134633017811953)
                ·
                  refine ⟨10700896674100974763358965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14267862232134633017811953 10700896674100974763358965)
                  ·
                    refine ⟨1003209063196966384064903, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10700896674100974763358965 1003209063196966384064903)
                    ·
                      rfl

theorem cell23_5861228_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 2, 5].length) (baseStart_5861228 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861228 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861228 prefixEnd_5861228 := by exact prefixLift 5861228
  have htrace : WordTrace (prefixWord ++ tailWord_5861228) baseStart_5861228 baseEnd_5861228 := by
    simpa [prefixWord, tailWord_5861228, baseEnd_5861228] using wordTrace_append hprefix tailTrace_5861228
  have hstable : (prefixWord ++ tailWord_5861228).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861228).length < 2 ^ (prefixWord ++ tailWord_5861228).sum := by decide
  have hdescent : baseEnd_5861228 < baseStart_5861228 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861228) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861248 : List Nat := [2, 1, 1, 2, 1, 2, 3, 1, 4, 4, 2]
def baseStart_5861248 : Nat := 118140960795 + 5861248 * 2 ^ 59
def prefixEnd_5861248 : Nat := 4983230072969 + 3 ^ 40 * 5861248 * 2
def baseEnd_5861248 : Nat := 3009637459203989073944617

theorem tailTrace_5861248 : CollatzResearch.WordTrace tailWord_5861248 prefixEnd_5861248 3009637459203989073944617 := by
  unfold tailWord_5861248
  simp only [CollatzResearch.WordTrace]
  refine ⟨106888638534853496154060199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142518184713137994872080265 106888638534853496154060199)
  ·
    refine ⟨160332957802280244231090299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106888638534853496154060199 160332957802280244231090299)
    ·
      refine ⟨240499436703420366346635449, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160332957802280244231090299 240499436703420366346635449)
      ·
        refine ⟨180374577527565274759976587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240499436703420366346635449 180374577527565274759976587)
        ·
          refine ⟨270561866291347912139964881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180374577527565274759976587 270561866291347912139964881)
          ·
            refine ⟨202921399718510934104973661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270561866291347912139964881 202921399718510934104973661)
            ·
              refine ⟨76095524894441600289365123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202921399718510934104973661 76095524894441600289365123)
              ·
                refine ⟨114143287341662400434047685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76095524894441600289365123 114143287341662400434047685)
                ·
                  refine ⟨21401866376561700081383941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114143287341662400434047685 21401866376561700081383941)
                  ·
                    refine ⟨4012849945605318765259489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21401866376561700081383941 4012849945605318765259489)
                    ·
                      refine ⟨3009637459203989073944617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012849945605318765259489 3009637459203989073944617)
                      ·
                        rfl

theorem cell23_5861248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 3, 1, 4, 4, 2].length) (baseStart_5861248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861248 prefixEnd_5861248 := by exact prefixLift 5861248
  have htrace : WordTrace (prefixWord ++ tailWord_5861248) baseStart_5861248 baseEnd_5861248 := by
    simpa [prefixWord, tailWord_5861248, baseEnd_5861248] using wordTrace_append hprefix tailTrace_5861248
  have hstable : (prefixWord ++ tailWord_5861248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861248).length < 2 ^ (prefixWord ++ tailWord_5861248).sum := by decide
  have hdescent : baseEnd_5861248 < baseStart_5861248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861309 : List Nat := [1, 4, 1, 2, 3, 2, 3, 2, 1, 4]
def baseStart_5861309 : Nat := 118140960795 + 5861309 * 2 ^ 59
def prefixEnd_5861309 : Nat := 4983230072969 + 3 ^ 40 * 5861309 * 2
def baseEnd_5861309 : Nat := 1003222927174637778427279

theorem tailTrace_5861309 : CollatzResearch.WordTrace tailWord_5861309 prefixEnd_5861309 1003222927174637778427279 := by
  unfold tailWord_5861309
  simp only [CollatzResearch.WordTrace]
  refine ⟨213779501922485999726090981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142519667948323999817393987 213779501922485999726090981)
  ·
    refine ⟨40083656610466124948642059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213779501922485999726090981 40083656610466124948642059)
    ·
      refine ⟨60125484915699187422963089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40083656610466124948642059 60125484915699187422963089)
      ·
        refine ⟨45094113686774390567222317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60125484915699187422963089 45094113686774390567222317)
        ·
          refine ⟨16910292632540396462708369, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45094113686774390567222317 16910292632540396462708369)
          ·
            refine ⟨12682719474405297347031277, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16910292632540396462708369 12682719474405297347031277)
            ·
              refine ⟨4756019802901986505136729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12682719474405297347031277 4756019802901986505136729)
              ·
                refine ⟨3567014852176489878852547, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4756019802901986505136729 3567014852176489878852547)
                ·
                  refine ⟨5350522278264734818278821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567014852176489878852547 5350522278264734818278821)
                  ·
                    refine ⟨1003222927174637778427279, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350522278264734818278821 1003222927174637778427279)
                    ·
                      rfl

theorem cell23_5861309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 2, 3, 2, 1, 4].length) (baseStart_5861309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861309 prefixEnd_5861309 := by exact prefixLift 5861309
  have htrace : WordTrace (prefixWord ++ tailWord_5861309) baseStart_5861309 baseEnd_5861309 := by
    simpa [prefixWord, tailWord_5861309, baseEnd_5861309] using wordTrace_append hprefix tailTrace_5861309
  have hstable : (prefixWord ++ tailWord_5861309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861309).length < 2 ^ (prefixWord ++ tailWord_5861309).sum := by decide
  have hdescent : baseEnd_5861309 < baseStart_5861309 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861348 : List Nat := [2, 3, 1, 1, 1, 1, 5, 2, 1, 6]
def baseStart_5861348 : Nat := 118140960795 + 5861348 * 2 ^ 59
def prefixEnd_5861348 : Nat := 4983230072969 + 3 ^ 40 * 5861348 * 2
def baseEnd_5861348 : Nat := 1003229602423146227564719

theorem tailTrace_5861348 : CollatzResearch.WordTrace tailWord_5861348 prefixEnd_5861348 1003229602423146227564719 := by
  unfold tailWord_5861348
  simp only [CollatzResearch.WordTrace]
  refine ⟨106890462184672354693380349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142520616246229806257840465 106890462184672354693380349)
  ·
    refine ⟨40083923319252133010017631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106890462184672354693380349 40083923319252133010017631)
    ·
      refine ⟨60125884978878199515026447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40083923319252133010017631 60125884978878199515026447)
      ·
        refine ⟨90188827468317299272539671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60125884978878199515026447 90188827468317299272539671)
        ·
          refine ⟨135283241202475948908809507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90188827468317299272539671 135283241202475948908809507)
          ·
            refine ⟨202924861803713923363214261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135283241202475948908809507 202924861803713923363214261)
            ·
              refine ⟨19024205794098180315301337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202924861803713923363214261 19024205794098180315301337)
              ·
                refine ⟨14268154345573635236476003, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19024205794098180315301337 14268154345573635236476003)
                ·
                  refine ⟨21402231518360452854714005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14268154345573635236476003 21402231518360452854714005)
                  ·
                    refine ⟨1003229602423146227564719, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21402231518360452854714005 1003229602423146227564719)
                    ·
                      rfl

theorem cell23_5861348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 1, 5, 2, 1, 6].length) (baseStart_5861348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861348 prefixEnd_5861348 := by exact prefixLift 5861348
  have htrace : WordTrace (prefixWord ++ tailWord_5861348) baseStart_5861348 baseEnd_5861348 := by
    simpa [prefixWord, tailWord_5861348, baseEnd_5861348] using wordTrace_append hprefix tailTrace_5861348
  have hstable : (prefixWord ++ tailWord_5861348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861348).length < 2 ^ (prefixWord ++ tailWord_5861348).sum := by decide
  have hdescent : baseEnd_5861348 < baseStart_5861348 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861361 : List Nat := [1, 2, 2, 2, 16]
def baseStart_5861361 : Nat := 118140960795 + 5861361 * 2 ^ 59
def prefixEnd_5861361 : Nat := 4983230072969 + 3 ^ 40 * 5861361 * 2
def baseEnd_5861361 : Nat := 4128526039119269042293

theorem tailTrace_5861361 : CollatzResearch.WordTrace tailWord_5861361 prefixEnd_5861361 4128526039119269042293 := by
  unfold tailWord_5861361
  simp only [CollatzResearch.WordTrace]
  refine ⟨213781398518297612606983937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142520932345531741737989291 213781398518297612606983937)
  ·
    refine ⟨160336048888723209455237953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213781398518297612606983937 160336048888723209455237953)
    ·
      refine ⟨120252036666542407091428465, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160336048888723209455237953 120252036666542407091428465)
      ·
        refine ⟨90189027499906805318571349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120252036666542407091428465 90189027499906805318571349)
        ·
          refine ⟨4128526039119269042293, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 16 90189027499906805318571349 4128526039119269042293)
          ·
            rfl

theorem cell23_5861361_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 16].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 16].length) (baseStart_5861361 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861361 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861361 prefixEnd_5861361 := by exact prefixLift 5861361
  have htrace : WordTrace (prefixWord ++ tailWord_5861361) baseStart_5861361 baseEnd_5861361 := by
    simpa [prefixWord, tailWord_5861361, baseEnd_5861361] using wordTrace_append hprefix tailTrace_5861361
  have hstable : (prefixWord ++ tailWord_5861361).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861361).length < 2 ^ (prefixWord ++ tailWord_5861361).sum := by decide
  have hdescent : baseEnd_5861361 < baseStart_5861361 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861361) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861366 : List Nat := [5, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3]
def baseStart_5861366 : Nat := 118140960795 + 5861366 * 2 ^ 59
def prefixEnd_5861366 : Nat := 4983230072969 + 3 ^ 40 * 5861366 * 2
def baseEnd_5861366 : Nat := 3009698049921219612269075

theorem tailTrace_5861366 : CollatzResearch.WordTrace tailWord_5861366 prefixEnd_5861366 3009698049921219612269075 := by
  unfold tailWord_5861366
  simp only [CollatzResearch.WordTrace]
  refine ⟨13361348805204968653807247, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142521053922186332307277301 13361348805204968653807247)
  ·
    refine ⟨20042023207807452980710871, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13361348805204968653807247 20042023207807452980710871)
    ·
      refine ⟨30063034811711179471066307, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20042023207807452980710871 30063034811711179471066307)
      ·
        refine ⟨45094552217566769206599461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30063034811711179471066307 45094552217566769206599461)
        ·
          refine ⟨8455228540793769226237399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45094552217566769206599461 8455228540793769226237399)
          ·
            refine ⟨12682842811190653839356099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455228540793769226237399 12682842811190653839356099)
            ·
              refine ⟨19024264216785980759034149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12682842811190653839356099 19024264216785980759034149)
              ·
                refine ⟨3567049540647371392318903, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19024264216785980759034149 3567049540647371392318903)
                ·
                  refine ⟨5350574310971057088478355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567049540647371392318903 5350574310971057088478355)
                  ·
                    refine ⟨8025861466456585632717533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5350574310971057088478355 8025861466456585632717533)
                    ·
                      refine ⟨3009698049921219612269075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8025861466456585632717533 3009698049921219612269075)
                      ·
                        rfl

theorem cell23_5861366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 4, 1, 1, 4, 1, 1, 3].length) (baseStart_5861366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861366 prefixEnd_5861366 := by exact prefixLift 5861366
  have htrace : WordTrace (prefixWord ++ tailWord_5861366) baseStart_5861366 baseEnd_5861366 := by
    simpa [prefixWord, tailWord_5861366, baseEnd_5861366] using wordTrace_append hprefix tailTrace_5861366
  have hstable : (prefixWord ++ tailWord_5861366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861366).length < 2 ^ (prefixWord ++ tailWord_5861366).sum := by decide
  have hdescent : baseEnd_5861366 < baseStart_5861366 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861372 : List Nat := [2, 2, 2, 1, 2, 2, 2, 3, 3, 2, 2]
def baseStart_5861372 : Nat := 118140960795 + 5861372 * 2 ^ 59
def prefixEnd_5861372 : Nat := 4983230072969 + 3 ^ 40 * 5861372 * 2
def baseEnd_5861372 : Nat := 3009701130805146588794047

theorem tailTrace_5861372 : CollatzResearch.WordTrace tailWord_5861372 prefixEnd_5861372 3009701130805146588794047 := by
  unfold tailWord_5861372
  simp only [CollatzResearch.WordTrace]
  refine ⟨106890899860628880742817185, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142521199814171840990422913 106890899860628880742817185)
  ·
    refine ⟨80168174895471660557112889, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106890899860628880742817185 80168174895471660557112889)
    ·
      refine ⟨60126131171603745417834667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80168174895471660557112889 60126131171603745417834667)
      ·
        refine ⟨90189196757405618126752001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60126131171603745417834667 90189196757405618126752001)
        ·
          refine ⟨67641897568054213595064001, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90189196757405618126752001 67641897568054213595064001)
          ·
            refine ⟨50731423176040660196298001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67641897568054213595064001 50731423176040660196298001)
            ·
              refine ⟨38048567382030495147223501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50731423176040660196298001 38048567382030495147223501)
              ·
                refine ⟨14268212768261435680208813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38048567382030495147223501 14268212768261435680208813)
                ·
                  refine ⟨5350579788098038380078305, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14268212768261435680208813 5350579788098038380078305)
                  ·
                    refine ⟨4012934841073528785058729, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5350579788098038380078305 4012934841073528785058729)
                    ·
                      refine ⟨3009701130805146588794047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4012934841073528785058729 3009701130805146588794047)
                      ·
                        rfl

theorem cell23_5861372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 2, 2, 3, 3, 2, 2].length) (baseStart_5861372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861372 prefixEnd_5861372 := by exact prefixLift 5861372
  have htrace : WordTrace (prefixWord ++ tailWord_5861372) baseStart_5861372 baseEnd_5861372 := by
    simpa [prefixWord, tailWord_5861372, baseEnd_5861372] using wordTrace_append hprefix tailTrace_5861372
  have hstable : (prefixWord ++ tailWord_5861372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861372).length < 2 ^ (prefixWord ++ tailWord_5861372).sum := by decide
  have hdescent : baseEnd_5861372 < baseStart_5861372 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861416 : List Nat := [2, 1, 5, 3, 1, 2, 1, 2, 2, 4]
def baseStart_5861416 : Nat := 118140960795 + 5861416 * 2 ^ 59
def prefixEnd_5861416 : Nat := 4983230072969 + 3 ^ 40 * 5861416 * 2
def baseEnd_5861416 : Nat := 1003241241317981472214615

theorem tailTrace_5861416 : CollatzResearch.WordTrace tailWord_5861416 prefixEnd_5861416 1003241241317981472214615 := by
  unfold tailWord_5861416
  simp only [CollatzResearch.WordTrace]
  refine ⟨106891702266549178500118051, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142522269688732238000157401 106891702266549178500118051)
  ·
    refine ⟨160337553399823767750177077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106891702266549178500118051 160337553399823767750177077)
    ·
      refine ⟨15031645631233478226579101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160337553399823767750177077 15031645631233478226579101)
      ·
        refine ⟨5636867111712554334967163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15031645631233478226579101 5636867111712554334967163)
        ·
          refine ⟨8455300667568831502450745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5636867111712554334967163 8455300667568831502450745)
          ·
            refine ⟨6341475500676623626838059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8455300667568831502450745 6341475500676623626838059)
            ·
              refine ⟨9512213251014935440257089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341475500676623626838059 9512213251014935440257089)
              ·
                refine ⟨7134159938261201580192817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9512213251014935440257089 7134159938261201580192817)
                ·
                  refine ⟨5350619953695901185144613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7134159938261201580192817 5350619953695901185144613)
                  ·
                    refine ⟨1003241241317981472214615, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350619953695901185144613 1003241241317981472214615)
                    ·
                      rfl

theorem cell23_5861416_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 3, 1, 2, 1, 2, 2, 4].length) (baseStart_5861416 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861416 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861416 prefixEnd_5861416 := by exact prefixLift 5861416
  have htrace : WordTrace (prefixWord ++ tailWord_5861416) baseStart_5861416 baseEnd_5861416 := by
    simpa [prefixWord, tailWord_5861416, baseEnd_5861416] using wordTrace_append hprefix tailTrace_5861416
  have hstable : (prefixWord ++ tailWord_5861416).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861416).length < 2 ^ (prefixWord ++ tailWord_5861416).sum := by decide
  have hdescent : baseEnd_5861416 < baseStart_5861416 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861416) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861479 : List Nat := [1, 1, 5, 1, 1, 2, 2, 4, 2, 2, 2]
def baseStart_5861479 : Nat := 118140960795 + 5861479 * 2 ^ 59
def prefixEnd_5861479 : Nat := 4983230072969 + 3 ^ 40 * 5861479 * 2
def baseEnd_5861479 : Nat := 3009756073235177670156055

theorem tailTrace_5861479 : CollatzResearch.WordTrace tailWord_5861479 prefixEnd_5861479 3009756073235177670156055 := by
  unfold tailWord_5861479
  simp only [CollatzResearch.WordTrace]
  refine ⟨213785702331870118759779491, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142523801554580079173186327 213785702331870118759779491)
  ·
    refine ⟨320678553497805178139669237, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213785702331870118759779491 320678553497805178139669237)
    ·
      refine ⟨30063614390419235450593991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320678553497805178139669237 30063614390419235450593991)
      ·
        refine ⟨45095421585628853175890987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30063614390419235450593991 45095421585628853175890987)
        ·
          refine ⟨67643132378443279763836481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45095421585628853175890987 67643132378443279763836481)
          ·
            refine ⟨50732349283832459822877361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67643132378443279763836481 50732349283832459822877361)
            ·
              refine ⟨38049261962874344867158021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50732349283832459822877361 38049261962874344867158021)
              ·
                refine ⟨7134236618038939662592129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38049261962874344867158021 7134236618038939662592129)
                ·
                  refine ⟨5350677463529204746944097, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7134236618038939662592129 5350677463529204746944097)
                  ·
                    refine ⟨4013008097646903560208073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5350677463529204746944097 4013008097646903560208073)
                    ·
                      refine ⟨3009756073235177670156055, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013008097646903560208073 3009756073235177670156055)
                      ·
                        rfl

theorem cell23_5861479_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 2, 2, 4, 2, 2, 2].length) (baseStart_5861479 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861479 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861479 prefixEnd_5861479 := by exact prefixLift 5861479
  have htrace : WordTrace (prefixWord ++ tailWord_5861479) baseStart_5861479 baseEnd_5861479 := by
    simpa [prefixWord, tailWord_5861479, baseEnd_5861479] using wordTrace_append hprefix tailTrace_5861479
  have hstable : (prefixWord ++ tailWord_5861479).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861479).length < 2 ^ (prefixWord ++ tailWord_5861479).sum := by decide
  have hdescent : baseEnd_5861479 < baseStart_5861479 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861479) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861555 : List Nat := [1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 3]
def baseStart_5861555 : Nat := 118140960795 + 5861555 * 2 ^ 59
def prefixEnd_5861555 : Nat := 4983230072969 + 3 ^ 40 * 5861555 * 2
def baseEnd_5861555 : Nat := 3009795097764919372805705

theorem tailTrace_5861555 : CollatzResearch.WordTrace tailWord_5861555 prefixEnd_5861555 3009795097764919372805705 := by
  unfold tailWord_5861555
  simp only [CollatzResearch.WordTrace]
  refine ⟨213788474279594783739546119, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142525649519729855826364079 213788474279594783739546119)
  ·
    refine ⟨320682711419392175609319179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213788474279594783739546119 320682711419392175609319179)
    ·
      refine ⟨481024067129088263413978769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320682711419392175609319179 481024067129088263413978769)
      ·
        refine ⟨360768050346816197560484077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481024067129088263413978769 360768050346816197560484077)
        ·
          refine ⟨135288018880056074085181529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360768050346816197560484077 135288018880056074085181529)
          ·
            refine ⟨101466014160042055563886147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135288018880056074085181529 101466014160042055563886147)
            ·
              refine ⟨152199021240063083345829221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101466014160042055563886147 152199021240063083345829221)
              ·
                refine ⟨28537316482511828127342979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152199021240063083345829221 28537316482511828127342979)
                ·
                  refine ⟨42805974723767742191014469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28537316482511828127342979 42805974723767742191014469)
                  ·
                    refine ⟨8026120260706451660815213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 42805974723767742191014469 8026120260706451660815213)
                    ·
                      refine ⟨3009795097764919372805705, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8026120260706451660815213 3009795097764919372805705)
                      ·
                        rfl

theorem cell23_5861555_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 1, 4, 1, 4, 3].length) (baseStart_5861555 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861555 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861555 prefixEnd_5861555 := by exact prefixLift 5861555
  have htrace : WordTrace (prefixWord ++ tailWord_5861555) baseStart_5861555 baseEnd_5861555 := by
    simpa [prefixWord, tailWord_5861555, baseEnd_5861555] using wordTrace_append hprefix tailTrace_5861555
  have hstable : (prefixWord ++ tailWord_5861555).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861555).length < 2 ^ (prefixWord ++ tailWord_5861555).sum := by decide
  have hdescent : baseEnd_5861555 < baseStart_5861555 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861555) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861566 : List Nat := [4, 2, 1, 1, 5, 1, 1, 1, 2, 5]
def baseStart_5861566 : Nat := 118140960795 + 5861566 * 2 ^ 59
def prefixEnd_5861566 : Nat := 4983230072969 + 3 ^ 40 * 5861566 * 2
def baseEnd_5861566 : Nat := 1003266915350706276589385

theorem tailTrace_5861566 : CollatzResearch.WordTrace tailWord_5861566 prefixEnd_5861566 1003266915350706276589385 := by
  unfold tailWord_5861566
  simp only [CollatzResearch.WordTrace]
  refine ⟨26723609435319366577274569, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142525916988369955078797701 26723609435319366577274569)
  ·
    refine ⟨20042707076489524932955927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26723609435319366577274569 20042707076489524932955927)
    ·
      refine ⟨30064060614734287399433891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20042707076489524932955927 30064060614734287399433891)
      ·
        refine ⟨45096090922101431099150837, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30064060614734287399433891 45096090922101431099150837)
        ·
          refine ⟨4227758523947009165545391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45096090922101431099150837 4227758523947009165545391)
          ·
            refine ⟨6341637785920513748318087, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4227758523947009165545391 6341637785920513748318087)
            ·
              refine ⟨9512456678880770622477131, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6341637785920513748318087 9512456678880770622477131)
              ·
                refine ⟨14268685018321155933715697, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9512456678880770622477131 14268685018321155933715697)
                ·
                  refine ⟨10701513763740866950286773, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14268685018321155933715697 10701513763740866950286773)
                  ·
                    refine ⟨1003266915350706276589385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10701513763740866950286773 1003266915350706276589385)
                    ·
                      rfl

theorem cell23_5861566_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 5, 1, 1, 1, 2, 5].length) (baseStart_5861566 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861566 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861566 prefixEnd_5861566 := by exact prefixLift 5861566
  have htrace : WordTrace (prefixWord ++ tailWord_5861566) baseStart_5861566 baseEnd_5861566 := by
    simpa [prefixWord, tailWord_5861566, baseEnd_5861566] using wordTrace_append hprefix tailTrace_5861566
  have hstable : (prefixWord ++ tailWord_5861566).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861566).length < 2 ^ (prefixWord ++ tailWord_5861566).sum := by decide
  have hdescent : baseEnd_5861566 < baseStart_5861566 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861566) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861569 : List Nat := [1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 4]
def baseStart_5861569 : Nat := 118140960795 + 5861569 * 2 ^ 59
def prefixEnd_5861569 : Nat := 4983230072969 + 3 ^ 40 * 5861569 * 2
def baseEnd_5861569 : Nat := 3009802286494082318030641

theorem tailTrace_5861569 : CollatzResearch.WordTrace tailWord_5861569 prefixEnd_5861569 3009802286494082318030641 := by
  unfold tailWord_5861569
  simp only [CollatzResearch.WordTrace]
  refine ⟨213788984901544064130555761, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142525989934362709420370507 213788984901544064130555761)
  ·
    refine ⟨160341738676158048097916821, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213788984901544064130555761 160341738676158048097916821)
    ·
      refine ⟨7516019000444908504589851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 160341738676158048097916821 7516019000444908504589851)
      ·
        refine ⟨11274028500667362756884777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7516019000444908504589851 11274028500667362756884777)
        ·
          refine ⟨8455521375500522067663583, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11274028500667362756884777 8455521375500522067663583)
          ·
            refine ⟨12683282063250783101495375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455521375500522067663583 12683282063250783101495375)
            ·
              refine ⟨19024923094876174652243063, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12683282063250783101495375 19024923094876174652243063)
              ·
                refine ⟨28537384642314261978364595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19024923094876174652243063 28537384642314261978364595)
                ·
                  refine ⟨42806076963471392967546893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28537384642314261978364595 42806076963471392967546893)
                  ·
                    refine ⟨16052278861301772362830085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42806076963471392967546893 16052278861301772362830085)
                    ·
                      refine ⟨3009802286494082318030641, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16052278861301772362830085 3009802286494082318030641)
                      ·
                        rfl

theorem cell23_5861569_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 2, 1, 1, 1, 1, 3, 4].length) (baseStart_5861569 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861569 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861569 prefixEnd_5861569 := by exact prefixLift 5861569
  have htrace : WordTrace (prefixWord ++ tailWord_5861569) baseStart_5861569 baseEnd_5861569 := by
    simpa [prefixWord, tailWord_5861569, baseEnd_5861569] using wordTrace_append hprefix tailTrace_5861569
  have hstable : (prefixWord ++ tailWord_5861569).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861569).length < 2 ^ (prefixWord ++ tailWord_5861569).sum := by decide
  have hdescent : baseEnd_5861569 < baseStart_5861569 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861569) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861579 : List Nat := [1, 1, 1, 1, 3, 2, 6, 3, 1, 4]
def baseStart_5861579 : Nat := 118140960795 + 5861579 * 2 ^ 59
def prefixEnd_5861579 : Nat := 4983230072969 + 3 ^ 40 * 5861579 * 2
def baseEnd_5861579 : Nat := 1003269140433542426301865

theorem tailTrace_5861579 : CollatzResearch.WordTrace tailWord_5861579 prefixEnd_5861579 1003269140433542426301865 := by
  unfold tailWord_5861579
  simp only [CollatzResearch.WordTrace]
  refine ⟨213789349631507835838419791, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142526233087671890558946527 213789349631507835838419791)
  ·
    refine ⟨320684024447261753757629687, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213789349631507835838419791 320684024447261753757629687)
    ·
      refine ⟨481026036670892630636444531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320684024447261753757629687 481026036670892630636444531)
      ·
        refine ⟨721539055006338945954666797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481026036670892630636444531 721539055006338945954666797)
        ·
          refine ⟨270577145627377104733000049, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 721539055006338945954666797 270577145627377104733000049)
          ·
            refine ⟨202932859220532828549750037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270577145627377104733000049 202932859220532828549750037)
            ·
              refine ⟨9512477775962476338269533, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 202932859220532828549750037 9512477775962476338269533)
              ·
                refine ⟨3567179165985928626851075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9512477775962476338269533 3567179165985928626851075)
                ·
                  refine ⟨5350768748978892940276613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567179165985928626851075 5350768748978892940276613)
                  ·
                    refine ⟨1003269140433542426301865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5350768748978892940276613 1003269140433542426301865)
                    ·
                      rfl

theorem cell23_5861579_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 6, 3, 1, 4].length) (baseStart_5861579 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861579 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861579 prefixEnd_5861579 := by exact prefixLift 5861579
  have htrace : WordTrace (prefixWord ++ tailWord_5861579) baseStart_5861579 baseEnd_5861579 := by
    simpa [prefixWord, tailWord_5861579, baseEnd_5861579] using wordTrace_append hprefix tailTrace_5861579
  have hstable : (prefixWord ++ tailWord_5861579).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861579).length < 2 ^ (prefixWord ++ tailWord_5861579).sum := by decide
  have hdescent : baseEnd_5861579 < baseStart_5861579 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861579) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861592 : List Nat := [2, 1, 2, 2, 4, 1, 3, 2, 6]
def baseStart_5861592 : Nat := 118140960795 + 5861592 * 2 ^ 59
def prefixEnd_5861592 : Nat := 4983230072969 + 3 ^ 40 * 5861592 * 2
def baseEnd_5861592 : Nat := 334423788505459525338115

theorem tailTrace_5861592 : CollatzResearch.WordTrace tailWord_5861592 prefixEnd_5861592 334423788505459525338115 := by
  unfold tailWord_5861592
  simp only [CollatzResearch.WordTrace]
  refine ⟨106894911890230369529321515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142526549186973826039095353 106894911890230369529321515)
  ·
    refine ⟨160342367835345554293982273, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106894911890230369529321515 160342367835345554293982273)
    ·
      refine ⟨120256775876509165720486705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160342367835345554293982273 120256775876509165720486705)
      ·
        refine ⟨90192581907381874290365029, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120256775876509165720486705 90192581907381874290365029)
        ·
          refine ⟨16911109107634101429443443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 90192581907381874290365029 16911109107634101429443443)
          ·
            refine ⟨25366663661451152144165165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16911109107634101429443443 25366663661451152144165165)
            ·
              refine ⟨9512498873044182054061937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25366663661451152144165165 9512498873044182054061937)
              ·
                refine ⟨7134374154783136540546453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9512498873044182054061937 7134374154783136540546453)
                ·
                  refine ⟨334423788505459525338115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7134374154783136540546453 334423788505459525338115)
                  ·
                    rfl

theorem cell23_5861592_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 4, 1, 3, 2, 6].length) (baseStart_5861592 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861592 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861592 prefixEnd_5861592 := by exact prefixLift 5861592
  have htrace : WordTrace (prefixWord ++ tailWord_5861592) baseStart_5861592 baseEnd_5861592 := by
    simpa [prefixWord, tailWord_5861592, baseEnd_5861592] using wordTrace_append hprefix tailTrace_5861592
  have hstable : (prefixWord ++ tailWord_5861592).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861592).length < 2 ^ (prefixWord ++ tailWord_5861592).sum := by decide
  have hdescent : baseEnd_5861592 < baseStart_5861592 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861592) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861612 : List Nat := [2, 2, 1, 1, 2, 3, 1, 1, 3, 5, 2]
def baseStart_5861612 : Nat := 118140960795 + 5861612 * 2 ^ 59
def prefixEnd_5861612 : Nat := 4983230072969 + 3 ^ 40 * 5861612 * 2
def baseEnd_5861612 : Nat := 3009824366162225649792943

theorem tailTrace_5861612 : CollatzResearch.WordTrace tailWord_5861612 prefixEnd_5861612 3009824366162225649792943 := by
  unfold tailWord_5861612
  simp only [CollatzResearch.WordTrace]
  refine ⟨106895276620194141237185545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142527035493592188316247393 106895276620194141237185545)
  ·
    refine ⟨80171457465145605927889159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106895276620194141237185545 80171457465145605927889159)
    ·
      refine ⟨120257186197718408891833739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80171457465145605927889159 120257186197718408891833739)
      ·
        refine ⟨180385779296577613337750609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120257186197718408891833739 180385779296577613337750609)
        ·
          refine ⟨135289334472433210003312957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180385779296577613337750609 135289334472433210003312957)
          ·
            refine ⟨50733500427162453751242359, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135289334472433210003312957 50733500427162453751242359)
            ·
              refine ⟨76100250640743680626863539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50733500427162453751242359 76100250640743680626863539)
              ·
                refine ⟨114150375961115520940295309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76100250640743680626863539 114150375961115520940295309)
                ·
                  refine ⟨42806390985418320352610741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114150375961115520940295309 42806390985418320352610741)
                  ·
                    refine ⟨4013099154882967533057257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42806390985418320352610741 4013099154882967533057257)
                    ·
                      refine ⟨3009824366162225649792943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013099154882967533057257 3009824366162225649792943)
                      ·
                        rfl

theorem cell23_5861612_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 5, 2].length) (baseStart_5861612 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861612 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861612 prefixEnd_5861612 := by exact prefixLift 5861612
  have htrace : WordTrace (prefixWord ++ tailWord_5861612) baseStart_5861612 baseEnd_5861612 := by
    simpa [prefixWord, tailWord_5861612, baseEnd_5861612] using wordTrace_append hprefix tailTrace_5861612
  have hstable : (prefixWord ++ tailWord_5861612).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861612).length < 2 ^ (prefixWord ++ tailWord_5861612).sum := by decide
  have hdescent : baseEnd_5861612 < baseStart_5861612 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861612) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861622 : List Nat := [5, 1, 1, 1, 1, 1, 2, 3, 3, 5]
def baseStart_5861622 : Nat := 118140960795 + 5861622 * 2 ^ 59
def prefixEnd_5861622 : Nat := 4983230072969 + 3 ^ 40 * 5861622 * 2
def baseEnd_5861622 : Nat := 1003276500322923536889299

theorem tailTrace_5861622 : CollatzResearch.WordTrace tailWord_5861622 prefixEnd_5861622 1003276500322923536889299 := by
  unfold tailWord_5861622
  simp only [CollatzResearch.WordTrace]
  refine ⟨13361932373147003386389695, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142527278646901369454823413 13361932373147003386389695)
  ·
    refine ⟨20042898559720505079584543, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13361932373147003386389695 20042898559720505079584543)
    ·
      refine ⟨30064347839580757619376815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20042898559720505079584543 30064347839580757619376815)
      ·
        refine ⟨45096521759371136429065223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30064347839580757619376815 45096521759371136429065223)
        ·
          refine ⟨67644782639056704643597835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45096521759371136429065223 67644782639056704643597835)
          ·
            refine ⟨101467173958585056965396753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67644782639056704643597835 101467173958585056965396753)
            ·
              refine ⟨76100380468938792724047565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101467173958585056965396753 76100380468938792724047565)
              ·
                refine ⟨28537642675852047271517837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76100380468938792724047565 28537642675852047271517837)
                ·
                  refine ⟨10701616003444517726819189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28537642675852047271517837 10701616003444517726819189)
                  ·
                    refine ⟨1003276500322923536889299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10701616003444517726819189 1003276500322923536889299)
                    ·
                      rfl

theorem cell23_5861622_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 1, 1, 1, 1, 2, 3, 3, 5].length) (baseStart_5861622 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861622 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861622 prefixEnd_5861622 := by exact prefixLift 5861622
  have htrace : WordTrace (prefixWord ++ tailWord_5861622) baseStart_5861622 baseEnd_5861622 := by
    simpa [prefixWord, tailWord_5861622, baseEnd_5861622] using wordTrace_append hprefix tailTrace_5861622
  have hstable : (prefixWord ++ tailWord_5861622).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861622).length < 2 ^ (prefixWord ++ tailWord_5861622).sum := by decide
  have hdescent : baseEnd_5861622 < baseStart_5861622 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861622) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861635 : List Nat := [1, 1, 1, 3, 2, 3, 2, 1, 3, 6]
def baseStart_5861635 : Nat := 118140960795 + 5861635 * 2 ^ 59
def prefixEnd_5861635 : Nat := 4983230072969 + 3 ^ 40 * 5861635 * 2
def baseEnd_5861635 : Nat := 1003278725405759686601779

theorem tailTrace_5861635 : CollatzResearch.WordTrace tailWord_5861635 prefixEnd_5861635 1003278725405759686601779 := by
  unfold tailWord_5861635
  simp only [CollatzResearch.WordTrace]
  refine ⟨213791392119304957402458359, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142527594746203304934972239 213791392119304957402458359)
  ·
    refine ⟨320687088178957436103687539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213791392119304957402458359 320687088178957436103687539)
    ·
      refine ⟨481030632268436154155531309, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320687088178957436103687539 481030632268436154155531309)
      ·
        refine ⟨180386487100663557808324241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481030632268436154155531309 180386487100663557808324241)
        ·
          refine ⟨135289865325497668356243181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180386487100663557808324241 135289865325497668356243181)
          ·
            refine ⟨50733699497061625633591193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135289865325497668356243181 50733699497061625633591193)
            ·
              refine ⟨38050274622796219225193395, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50733699497061625633591193 38050274622796219225193395)
              ·
                refine ⟨57075411934194328837790093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38050274622796219225193395 57075411934194328837790093)
                ·
                  refine ⟨21403279475322873314171285, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57075411934194328837790093 21403279475322873314171285)
                  ·
                    refine ⟨1003278725405759686601779, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21403279475322873314171285 1003278725405759686601779)
                    ·
                      rfl

theorem cell23_5861635_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 3, 2, 1, 3, 6].length) (baseStart_5861635 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861635 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861635 prefixEnd_5861635 := by exact prefixLift 5861635
  have htrace : WordTrace (prefixWord ++ tailWord_5861635) baseStart_5861635 baseEnd_5861635 := by
    simpa [prefixWord, tailWord_5861635, baseEnd_5861635] using wordTrace_append hprefix tailTrace_5861635
  have hstable : (prefixWord ++ tailWord_5861635).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861635).length < 2 ^ (prefixWord ++ tailWord_5861635).sum := by decide
  have hdescent : baseEnd_5861635 < baseStart_5861635 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861635) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861665 : List Nat := [1, 2, 3, 2, 1, 1, 3, 10]
def baseStart_5861665 : Nat := 118140960795 + 5861665 * 2 ^ 59
def prefixEnd_5861665 : Nat := 4983230072969 + 3 ^ 40 * 5861665 * 2
def baseEnd_5861665 : Nat := 111475984468033849719637

theorem tailTrace_5861665 : CollatzResearch.WordTrace tailWord_5861665 prefixEnd_5861665 111475984468033849719637 := by
  unfold tailWord_5861665
  simp only [CollatzResearch.WordTrace]
  refine ⟨213792486309196272526050449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142528324206130848350700299 213792486309196272526050449)
  ·
    refine ⟨160344364731897204394537837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213792486309196272526050449 160344364731897204394537837)
    ·
      refine ⟨60129136774461451647951689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160344364731897204394537837 60129136774461451647951689)
      ·
        refine ⟨45096852580846088735963767, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60129136774461451647951689 45096852580846088735963767)
        ·
          refine ⟨67645278871269133103945651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45096852580846088735963767 67645278871269133103945651)
          ·
            refine ⟨101467918306903699655918477, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67645278871269133103945651 101467918306903699655918477)
            ·
              refine ⟨38050469365088887370969429, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101467918306903699655918477 38050469365088887370969429)
              ·
                refine ⟨111475984468033849719637, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38050469365088887370969429 111475984468033849719637)
                ·
                  rfl

theorem cell23_5861665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 3, 10].length) (baseStart_5861665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861665 prefixEnd_5861665 := by exact prefixLift 5861665
  have htrace : WordTrace (prefixWord ++ tailWord_5861665) baseStart_5861665 baseEnd_5861665 := by
    simpa [prefixWord, tailWord_5861665, baseEnd_5861665] using wordTrace_append hprefix tailTrace_5861665
  have hstable : (prefixWord ++ tailWord_5861665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861665).length < 2 ^ (prefixWord ++ tailWord_5861665).sum := by decide
  have hdescent : baseEnd_5861665 < baseStart_5861665 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861679 : List Nat := [1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 3]
def baseStart_5861679 : Nat := 118140960795 + 5861679 * 2 ^ 59
def prefixEnd_5861679 : Nat := 4983230072969 + 3 ^ 40 * 5861679 * 2
def baseEnd_5861679 : Nat := 3009858769366076887655135

theorem tailTrace_5861679 : CollatzResearch.WordTrace tailWord_5861679 prefixEnd_5861679 3009858769366076887655135 := by
  unfold tailWord_5861679
  simp only [CollatzResearch.WordTrace]
  refine ⟨213792996931145552917060091, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142528664620763701944706727 213792996931145552917060091)
  ·
    refine ⟨320689495396718329375590137, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213792996931145552917060091 320689495396718329375590137)
    ·
      refine ⟨240517121547538747031692603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320689495396718329375590137 240517121547538747031692603)
      ·
        refine ⟨360775682321308120547538905, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240517121547538747031692603 360775682321308120547538905)
        ·
          refine ⟨270581761740981090410654179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360775682321308120547538905 270581761740981090410654179)
          ·
            refine ⟨405872642611471635615981269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270581761740981090410654179 405872642611471635615981269)
            ·
              refine ⟨9512640061206366459749561, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 7 405872642611471635615981269 9512640061206366459749561)
              ·
                refine ⟨7134480045904774844812171, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9512640061206366459749561 7134480045904774844812171)
                ·
                  refine ⟨10701720068857162267218257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7134480045904774844812171 10701720068857162267218257)
                  ·
                    refine ⟨8026290051642871700413693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10701720068857162267218257 8026290051642871700413693)
                    ·
                      refine ⟨3009858769366076887655135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8026290051642871700413693 3009858769366076887655135)
                      ·
                        rfl

theorem cell23_5861679_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 1, 7, 2, 1, 2, 3].length) (baseStart_5861679 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861679 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861679 prefixEnd_5861679 := by exact prefixLift 5861679
  have htrace : WordTrace (prefixWord ++ tailWord_5861679) baseStart_5861679 baseEnd_5861679 := by
    simpa [prefixWord, tailWord_5861679, baseEnd_5861679] using wordTrace_append hprefix tailTrace_5861679
  have hstable : (prefixWord ++ tailWord_5861679).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861679).length < 2 ^ (prefixWord ++ tailWord_5861679).sum := by decide
  have hdescent : baseEnd_5861679 < baseStart_5861679 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861679) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861689 : List Nat := [1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5861689 : Nat := 118140960795 + 5861689 * 2 ^ 59
def prefixEnd_5861689 : Nat := 4983230072969 + 3 ^ 40 * 5861689 * 2
def baseEnd_5861689 : Nat := 3009863904172621848530089

theorem tailTrace_5861689 : CollatzResearch.WordTrace tailWord_5861689 prefixEnd_5861689 3009863904172621848530089 := by
  unfold tailWord_5861689
  simp only [CollatzResearch.WordTrace]
  refine ⟨213793361661109324624924121, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142528907774072883083282747 213793361661109324624924121)
  ·
    refine ⟨160345021245831993468693091, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213793361661109324624924121 160345021245831993468693091)
    ·
      refine ⟨240517531868747990203039637, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160345021245831993468693091 240517531868747990203039637)
      ·
        refine ⟨11274259306347562040767483, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240517531868747990203039637 11274259306347562040767483)
        ·
          refine ⟨16911388959521343061151225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11274259306347562040767483 16911388959521343061151225)
          ·
            refine ⟨12683541719641007295863419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16911388959521343061151225 12683541719641007295863419)
            ·
              refine ⟨19025312579461510943795129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12683541719641007295863419 19025312579461510943795129)
              ·
                refine ⟨14268984434596133207846347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19025312579461510943795129 14268984434596133207846347)
                ·
                  refine ⟨21403476651894199811769521, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14268984434596133207846347 21403476651894199811769521)
                  ·
                    refine ⟨16052607488920649858827141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21403476651894199811769521 16052607488920649858827141)
                    ·
                      refine ⟨3009863904172621848530089, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16052607488920649858827141 3009863904172621848530089)
                      ·
                        rfl

theorem cell23_5861689_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 6, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5861689 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861689 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861689 prefixEnd_5861689 := by exact prefixLift 5861689
  have htrace : WordTrace (prefixWord ++ tailWord_5861689) baseStart_5861689 baseEnd_5861689 := by
    simpa [prefixWord, tailWord_5861689, baseEnd_5861689] using wordTrace_append hprefix tailTrace_5861689
  have hstable : (prefixWord ++ tailWord_5861689).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861689).length < 2 ^ (prefixWord ++ tailWord_5861689).sum := by decide
  have hdescent : baseEnd_5861689 < baseStart_5861689 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861689) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861719 : List Nat := [1, 1, 3, 2, 3, 1, 1, 1, 5, 3, 2]
def baseStart_5861719 : Nat := 118140960795 + 5861719 * 2 ^ 59
def prefixEnd_5861719 : Nat := 4983230072969 + 3 ^ 40 * 5861719 * 2
def baseEnd_5861719 : Nat := 3009879308592256731154951

theorem tailTrace_5861719 : CollatzResearch.WordTrace tailWord_5861719 prefixEnd_5861719 3009879308592256731154951 := by
  unfold tailWord_5861719
  simp only [CollatzResearch.WordTrace]
  refine ⟨213794455851000639748516211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142529637234000426499010807 213794455851000639748516211)
  ·
    refine ⟨320691683776500959622774317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213794455851000639748516211 320691683776500959622774317)
    ·
      refine ⟨120259381416187859858540369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320691683776500959622774317 120259381416187859858540369)
      ·
        refine ⟨90194536062140894893905277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120259381416187859858540369 90194536062140894893905277)
        ·
          refine ⟨33822951023302835585214479, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90194536062140894893905277 33822951023302835585214479)
          ·
            refine ⟨50734426534954253377821719, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33822951023302835585214479 50734426534954253377821719)
            ·
              refine ⟨76101639802431380066732579, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50734426534954253377821719 76101639802431380066732579)
              ·
                refine ⟨114152459703647070100098869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76101639802431380066732579 114152459703647070100098869)
                ·
                  refine ⟨10701793097216912821884269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114152459703647070100098869 10701793097216912821884269)
                  ·
                    refine ⟨4013172411456342308206601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10701793097216912821884269 4013172411456342308206601)
                    ·
                      refine ⟨3009879308592256731154951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013172411456342308206601 3009879308592256731154951)
                      ·
                        rfl

theorem cell23_5861719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 1, 1, 5, 3, 2].length) (baseStart_5861719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861719 prefixEnd_5861719 := by exact prefixLift 5861719
  have htrace : WordTrace (prefixWord ++ tailWord_5861719) baseStart_5861719 baseEnd_5861719 := by
    simpa [prefixWord, tailWord_5861719, baseEnd_5861719] using wordTrace_append hprefix tailTrace_5861719
  have hstable : (prefixWord ++ tailWord_5861719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861719).length < 2 ^ (prefixWord ++ tailWord_5861719).sum := by decide
  have hdescent : baseEnd_5861719 < baseStart_5861719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861732 : List Nat := [2, 3, 1, 1, 3, 1, 1, 2, 2, 3, 4]
def baseStart_5861732 : Nat := 118140960795 + 5861732 * 2 ^ 59
def prefixEnd_5861732 : Nat := 4983230072969 + 3 ^ 40 * 5861732 * 2
def baseEnd_5861732 : Nat := 3009885983840765180292391

theorem tailTrace_5861732 : CollatzResearch.WordTrace tailWord_5861732 prefixEnd_5861732 3009885983840765180292391 := by
  unfold tailWord_5861732
  simp only [CollatzResearch.WordTrace]
  refine ⟨106897464999976771484369725, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142529953333302361979159633 106897464999976771484369725)
  ·
    refine ⟨40086549374991289306638647, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106897464999976771484369725 40086549374991289306638647)
    ·
      refine ⟨60129824062486933959957971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40086549374991289306638647 60129824062486933959957971)
      ·
        refine ⟨90194736093730400939936957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60129824062486933959957971 90194736093730400939936957)
        ·
          refine ⟨33823026035148900352476359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90194736093730400939936957 33823026035148900352476359)
          ·
            refine ⟨50734539052723350528714539, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33823026035148900352476359 50734539052723350528714539)
            ·
              refine ⟨76101808579085025793071809, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50734539052723350528714539 76101808579085025793071809)
              ·
                refine ⟨57076356434313769344803857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76101808579085025793071809 57076356434313769344803857)
                ·
                  refine ⟨42807267325735327008602893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57076356434313769344803857 42807267325735327008602893)
                  ·
                    refine ⟨16052725247150747628226085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42807267325735327008602893 16052725247150747628226085)
                    ·
                      refine ⟨3009885983840765180292391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16052725247150747628226085 3009885983840765180292391)
                      ·
                        rfl

theorem cell23_5861732_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 3, 1, 1, 2, 2, 3, 4].length) (baseStart_5861732 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861732 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861732 prefixEnd_5861732 := by exact prefixLift 5861732
  have htrace : WordTrace (prefixWord ++ tailWord_5861732) baseStart_5861732 baseEnd_5861732 := by
    simpa [prefixWord, tailWord_5861732, baseEnd_5861732] using wordTrace_append hprefix tailTrace_5861732
  have hstable : (prefixWord ++ tailWord_5861732).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861732).length < 2 ^ (prefixWord ++ tailWord_5861732).sum := by decide
  have hdescent : baseEnd_5861732 < baseStart_5861732 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861732) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861736 : List Nat := [2, 1, 4, 2, 2, 1, 2, 1, 3, 3, 2]
def baseStart_5861736 : Nat := 118140960795 + 5861736 * 2 ^ 59
def prefixEnd_5861736 : Nat := 4983230072969 + 3 ^ 40 * 5861736 * 2
def baseEnd_5861736 : Nat := 3009888037763383164642373

theorem tailTrace_5861736 : CollatzResearch.WordTrace tailWord_5861736 prefixEnd_5861736 3009888037763383164642373 := by
  unfold tailWord_5861736
  simp only [CollatzResearch.WordTrace]
  refine ⟨106897537945969525825942531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142530050594626034434590041 106897537945969525825942531)
  ·
    refine ⟨160346306918954288738913797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106897537945969525825942531 160346306918954288738913797)
    ·
      refine ⟨30064932547303929138546337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160346306918954288738913797 30064932547303929138546337)
      ·
        refine ⟨22548699410477946853909753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30064932547303929138546337 22548699410477946853909753)
        ·
          refine ⟨16911524557858460140432315, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22548699410477946853909753 16911524557858460140432315)
          ·
            refine ⟨25367286836787690210648473, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16911524557858460140432315 25367286836787690210648473)
            ·
              refine ⟨19025465127590767657986355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25367286836787690210648473 19025465127590767657986355)
              ·
                refine ⟨28538197691386151486979533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19025465127590767657986355 28538197691386151486979533)
                ·
                  refine ⟨10701824134269806807617325, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28538197691386151486979533 10701824134269806807617325)
                  ·
                    refine ⟨4013184050351177552856497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10701824134269806807617325 4013184050351177552856497)
                    ·
                      refine ⟨3009888037763383164642373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013184050351177552856497 3009888037763383164642373)
                      ·
                        rfl

theorem cell23_5861736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 2, 1, 2, 1, 3, 3, 2].length) (baseStart_5861736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861736 prefixEnd_5861736 := by exact prefixLift 5861736
  have htrace : WordTrace (prefixWord ++ tailWord_5861736) baseStart_5861736 baseEnd_5861736 := by
    simpa [prefixWord, tailWord_5861736, baseEnd_5861736] using wordTrace_append hprefix tailTrace_5861736
  have hstable : (prefixWord ++ tailWord_5861736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861736).length < 2 ^ (prefixWord ++ tailWord_5861736).sum := by decide
  have hdescent : baseEnd_5861736 < baseStart_5861736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861772 : List Nat := [2, 2, 1, 2, 1, 4, 1, 3, 7]
def baseStart_5861772 : Nat := 118140960795 + 5861772 * 2 ^ 59
def prefixEnd_5861772 : Nat := 4983230072969 + 3 ^ 40 * 5861772 * 2
def baseEnd_5861772 : Nat := 334434058118549447088023

theorem tailTrace_5861772 : CollatzResearch.WordTrace tailWord_5861772 prefixEnd_5861772 334434058118549447088023 := by
  unfold tailWord_5861772
  simp only [CollatzResearch.WordTrace]
  refine ⟨106898194459904314900097785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142530925946539086533463713 106898194459904314900097785)
  ·
    refine ⟨80173645844928236175073339, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106898194459904314900097785 80173645844928236175073339)
    ·
      refine ⟨120260468767392354262610009, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80173645844928236175073339 120260468767392354262610009)
      ·
        refine ⟨90195351575544265696957507, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120260468767392354262610009 90195351575544265696957507)
        ·
          refine ⟨135293027363316398545436261, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90195351575544265696957507 135293027363316398545436261)
          ·
            refine ⟨25367442630621824727269299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135293027363316398545436261 25367442630621824727269299)
            ·
              refine ⟨38051163945932737090903949, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25367442630621824727269299 38051163945932737090903949)
              ·
                refine ⟨14269186479724776409088981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38051163945932737090903949 14269186479724776409088981)
                ·
                  refine ⟨334434058118549447088023, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14269186479724776409088981 334434058118549447088023)
                  ·
                    rfl

theorem cell23_5861772_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 4, 1, 3, 7].length) (baseStart_5861772 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861772 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861772 prefixEnd_5861772 := by exact prefixLift 5861772
  have htrace : WordTrace (prefixWord ++ tailWord_5861772) baseStart_5861772 baseEnd_5861772 := by
    simpa [prefixWord, tailWord_5861772, baseEnd_5861772] using wordTrace_append hprefix tailTrace_5861772
  have hstable : (prefixWord ++ tailWord_5861772).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861772).length < 2 ^ (prefixWord ++ tailWord_5861772).sum := by decide
  have hdescent : baseEnd_5861772 < baseStart_5861772 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861772) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861839 : List Nat := [1, 1, 2, 1, 1, 4, 1, 3, 1, 6, 2]
def baseStart_5861839 : Nat := 118140960795 + 5861839 * 2 ^ 59
def prefixEnd_5861839 : Nat := 4983230072969 + 3 ^ 40 * 5861839 * 2
def baseEnd_5861839 : Nat := 3009940926270796261654399

theorem tailTrace_5861839 : CollatzResearch.WordTrace tailWord_5861839 prefixEnd_5861839 3009940926270796261654399 := by
  unfold tailWord_5861839
  simp only [CollatzResearch.WordTrace]
  refine ⟨213798832610565900242884571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142532555073710600161923047 213798832610565900242884571)
  ·
    refine ⟨320698248915848850364326857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213798832610565900242884571 320698248915848850364326857)
    ·
      refine ⟨240523686686886637773245143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320698248915848850364326857 240523686686886637773245143)
      ·
        refine ⟨360785530030329956659867715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240523686686886637773245143 360785530030329956659867715)
        ·
          refine ⟨541178295045494934989801573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360785530030329956659867715 541178295045494934989801573)
          ·
            refine ⟨101470930321030300310587795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 541178295045494934989801573 101470930321030300310587795)
            ·
              refine ⟨152206395481545450465881693, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101470930321030300310587795 152206395481545450465881693)
              ·
                refine ⟨57077398305579543924705635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152206395481545450465881693 57077398305579543924705635)
                ·
                  refine ⟨85616097458369315887058453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57077398305579543924705635 85616097458369315887058453)
                  ·
                    refine ⟨4013254568361061682205865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85616097458369315887058453 4013254568361061682205865)
                    ·
                      refine ⟨3009940926270796261654399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013254568361061682205865 3009940926270796261654399)
                      ·
                        rfl

theorem cell23_5861839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 4, 1, 3, 1, 6, 2].length) (baseStart_5861839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861839 prefixEnd_5861839 := by exact prefixLift 5861839
  have htrace : WordTrace (prefixWord ++ tailWord_5861839) baseStart_5861839 baseEnd_5861839 := by
    simpa [prefixWord, tailWord_5861839, baseEnd_5861839] using wordTrace_append hprefix tailTrace_5861839
  have hstable : (prefixWord ++ tailWord_5861839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861839).length < 2 ^ (prefixWord ++ tailWord_5861839).sum := by decide
  have hdescent : baseEnd_5861839 < baseStart_5861839 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861849 : List Nat := [1, 2, 1, 2, 4, 1, 2, 1, 5, 4]
def baseStart_5861849 : Nat := 118140960795 + 5861849 * 2 ^ 59
def prefixEnd_5861849 : Nat := 4983230072969 + 3 ^ 40 * 5861849 * 2
def baseEnd_5861849 : Nat := 1003315353692447074176451

theorem tailTrace_5861849 : CollatzResearch.WordTrace tailWord_5861849 prefixEnd_5861849 1003315353692447074176451 := by
  unfold tailWord_5861849
  simp only [CollatzResearch.WordTrace]
  refine ⟨213799197340529671950748601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142532798227019781300499067 213799197340529671950748601)
  ·
    refine ⟨160349398005397253963061451, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213799197340529671950748601 160349398005397253963061451)
    ·
      refine ⟨240524097008095880944592177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160349398005397253963061451 240524097008095880944592177)
      ·
        refine ⟨180393072756071910708444133, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240524097008095880944592177 180393072756071910708444133)
        ·
          refine ⟨33823701141763483257833275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180393072756071910708444133 33823701141763483257833275)
          ·
            refine ⟨50735551712645224886749913, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33823701141763483257833275 50735551712645224886749913)
            ·
              refine ⟨38051663784483918665062435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50735551712645224886749913 38051663784483918665062435)
              ·
                refine ⟨57077495676725877997593653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38051663784483918665062435 57077495676725877997593653)
                ·
                  refine ⟨5351015219693051062274405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57077495676725877997593653 5351015219693051062274405)
                  ·
                    refine ⟨1003315353692447074176451, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351015219693051062274405 1003315353692447074176451)
                    ·
                      rfl

theorem cell23_5861849_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 4, 1, 2, 1, 5, 4].length) (baseStart_5861849 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861849 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861849 prefixEnd_5861849 := by exact prefixLift 5861849
  have htrace : WordTrace (prefixWord ++ tailWord_5861849) baseStart_5861849 baseEnd_5861849 := by
    simpa [prefixWord, tailWord_5861849, baseEnd_5861849] using wordTrace_append hprefix tailTrace_5861849
  have hstable : (prefixWord ++ tailWord_5861849).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861849).length < 2 ^ (prefixWord ++ tailWord_5861849).sum := by decide
  have hdescent : baseEnd_5861849 < baseStart_5861849 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861849) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861890 : List Nat := [3, 4, 1, 2, 2, 1, 1, 1, 2, 4, 2]
def baseStart_5861890 : Nat := 118140960795 + 5861890 * 2 ^ 59
def prefixEnd_5861890 : Nat := 4983230072969 + 3 ^ 40 * 5861890 * 2
def baseEnd_5861890 : Nat := 3009967113784175562116665

theorem tailTrace_5861890 : CollatzResearch.WordTrace tailWord_5861890 prefixEnd_5861890 3009967113784175562116665 := by
  unfold tailWord_5861890
  simp only [CollatzResearch.WordTrace]
  refine ⟨53450173183345283988247781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142533795155587423968660749 53450173183345283988247781)
  ·
    refine ⟨10021907471877240747796459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53450173183345283988247781 10021907471877240747796459)
    ·
      refine ⟨15032861207815861121694689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10021907471877240747796459 15032861207815861121694689)
      ·
        refine ⟨11274645905861895841271017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15032861207815861121694689 11274645905861895841271017)
        ·
          refine ⟨8455984429396421880953263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11274645905861895841271017 8455984429396421880953263)
          ·
            refine ⟨12683976644094632821429895, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8455984429396421880953263 12683976644094632821429895)
            ·
              refine ⟨19025964966141949232144843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12683976644094632821429895 19025964966141949232144843)
              ·
                refine ⟨28538947449212923848217265, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19025964966141949232144843 28538947449212923848217265)
                ·
                  refine ⟨21404210586909692886162949, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28538947449212923848217265 21404210586909692886162949)
                  ·
                    refine ⟨4013289485045567416155553, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21404210586909692886162949 4013289485045567416155553)
                    ·
                      refine ⟨3009967113784175562116665, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013289485045567416155553 3009967113784175562116665)
                      ·
                        rfl

theorem cell23_5861890_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 2, 1, 1, 1, 2, 4, 2].length) (baseStart_5861890 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861890 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861890 prefixEnd_5861890 := by exact prefixLift 5861890
  have htrace : WordTrace (prefixWord ++ tailWord_5861890) baseStart_5861890 baseEnd_5861890 := by
    simpa [prefixWord, tailWord_5861890, baseEnd_5861890] using wordTrace_append hprefix tailTrace_5861890
  have hstable : (prefixWord ++ tailWord_5861890).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861890).length < 2 ^ (prefixWord ++ tailWord_5861890).sum := by decide
  have hdescent : baseEnd_5861890 < baseStart_5861890 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861890) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861909 : List Nat := [1, 3, 2, 1, 3, 1, 1, 3, 3, 5]
def baseStart_5861909 : Nat := 118140960795 + 5861909 * 2 ^ 59
def prefixEnd_5861909 : Nat := 4983230072969 + 3 ^ 40 * 5861909 * 2
def baseEnd_5861909 : Nat := 1003325623305536995926359

theorem tailTrace_5861909 : CollatzResearch.WordTrace tailWord_5861909 prefixEnd_5861909 1003325623305536995926359 := by
  unfold tailWord_5861909
  simp only [CollatzResearch.WordTrace]
  refine ⟨213801385720312302197932781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142534257146874868131955187 213801385720312302197932781)
  ·
    refine ⟨80175519645117113324224793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213801385720312302197932781 80175519645117113324224793)
    ·
      refine ⟨60131639733837834993168595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80175519645117113324224793 60131639733837834993168595)
      ·
        refine ⟨90197459600756752489752893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60131639733837834993168595 90197459600756752489752893)
        ·
          refine ⟨33824047350283782183657335, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90197459600756752489752893 33824047350283782183657335)
          ·
            refine ⟨50736071025425673275486003, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33824047350283782183657335 50736071025425673275486003)
            ·
              refine ⟨76104106538138509913229005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50736071025425673275486003 76104106538138509913229005)
              ·
                refine ⟨28539039951801941217460877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76104106538138509913229005 28539039951801941217460877)
                ·
                  refine ⟨10702139981925727956547829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28539039951801941217460877 10702139981925727956547829)
                  ·
                    refine ⟨1003325623305536995926359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10702139981925727956547829 1003325623305536995926359)
                    ·
                      rfl

theorem cell23_5861909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 3, 1, 1, 3, 3, 5].length) (baseStart_5861909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861909 prefixEnd_5861909 := by exact prefixLift 5861909
  have htrace : WordTrace (prefixWord ++ tailWord_5861909) baseStart_5861909 baseEnd_5861909 := by
    simpa [prefixWord, tailWord_5861909, baseEnd_5861909] using wordTrace_append hprefix tailTrace_5861909
  have hstable : (prefixWord ++ tailWord_5861909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861909).length < 2 ^ (prefixWord ++ tailWord_5861909).sum := by decide
  have hdescent : baseEnd_5861909 < baseStart_5861909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861963 : List Nat := [1, 1, 1, 1, 3, 1, 6, 2, 3, 2, 2]
def baseStart_5861963 : Nat := 118140960795 + 5861963 * 2 ^ 59
def prefixEnd_5861963 : Nat := 4983230072969 + 3 ^ 40 * 5861963 * 2
def baseEnd_5861963 : Nat := 3010004597871953776503829

theorem tailTrace_5861963 : CollatzResearch.WordTrace tailWord_5861963 prefixEnd_5861963 3010004597871953776503829 := by
  unfold tailWord_5861963
  simp only [CollatzResearch.WordTrace]
  refine ⟨213803355262116669420398543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142535570174744446280265695 213803355262116669420398543)
  ·
    refine ⟨320705032893175004130597815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213803355262116669420398543 320705032893175004130597815)
    ·
      refine ⟨481057549339762506195896723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320705032893175004130597815 481057549339762506195896723)
      ·
        refine ⟨721586324009643759293845085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481057549339762506195896723 721586324009643759293845085)
        ·
          refine ⟨270594871503616409735191907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 721586324009643759293845085 270594871503616409735191907)
          ·
            refine ⟨405892307255424614602787861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270594871503616409735191907 405892307255424614602787861)
            ·
              refine ⟨19026201902598028809505681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 405892307255424614602787861 19026201902598028809505681)
              ·
                refine ⟨14269651426948521607129261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19026201902598028809505681 14269651426948521607129261)
                ·
                  refine ⟨5351119285105695602673473, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14269651426948521607129261 5351119285105695602673473)
                  ·
                    refine ⟨4013339463829271702005105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5351119285105695602673473 4013339463829271702005105)
                    ·
                      refine ⟨3010004597871953776503829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013339463829271702005105 3010004597871953776503829)
                      ·
                        rfl

theorem cell23_5861963_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 1, 6, 2, 3, 2, 2].length) (baseStart_5861963 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861963 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861963 prefixEnd_5861963 := by exact prefixLift 5861963
  have htrace : WordTrace (prefixWord ++ tailWord_5861963) baseStart_5861963 baseEnd_5861963 := by
    simpa [prefixWord, tailWord_5861963, baseEnd_5861963] using wordTrace_append hprefix tailTrace_5861963
  have hstable : (prefixWord ++ tailWord_5861963).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861963).length < 2 ^ (prefixWord ++ tailWord_5861963).sum := by decide
  have hdescent : baseEnd_5861963 < baseStart_5861963 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861963) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861966 : List Nat := [4, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3]
def baseStart_5861966 : Nat := 118140960795 + 5861966 * 2 ^ 59
def prefixEnd_5861966 : Nat := 4983230072969 + 3 ^ 40 * 5861966 * 2
def baseEnd_5861966 : Nat := 3010006138313917264766315

theorem tailTrace_5861966 : CollatzResearch.WordTrace tailWord_5861966 prefixEnd_5861966 3010006138313917264766315 := by
  unfold tailWord_5861966
  simp only [CollatzResearch.WordTrace]
  refine ⟨26725433085138225116594719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142535643120737200621838501 26725433085138225116594719)
  ·
    refine ⟨40088149627707337674892079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26725433085138225116594719 40088149627707337674892079)
    ·
      refine ⟨60132224441561006512338119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40088149627707337674892079 60132224441561006512338119)
      ·
        refine ⟨90198336662341509768507179, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60132224441561006512338119 90198336662341509768507179)
        ·
          refine ⟨135297504993512264652760769, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90198336662341509768507179 135297504993512264652760769)
          ·
            refine ⟨101473128745134198489570577, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135297504993512264652760769 101473128745134198489570577)
            ·
              refine ⟨76104846558850648867177933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101473128745134198489570577 76104846558850648867177933)
              ·
                refine ⟨28539317459568993325191725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76104846558850648867177933 28539317459568993325191725)
                ·
                  refine ⟨10702244047338372496946897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28539317459568993325191725 10702244047338372496946897)
                  ·
                    refine ⟨8026683035503779372710173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10702244047338372496946897 8026683035503779372710173)
                    ·
                      refine ⟨3010006138313917264766315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8026683035503779372710173 3010006138313917264766315)
                      ·
                        rfl

theorem cell23_5861966_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 2, 2, 3, 3, 2, 3].length) (baseStart_5861966 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861966 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861966 prefixEnd_5861966 := by exact prefixLift 5861966
  have htrace : WordTrace (prefixWord ++ tailWord_5861966) baseStart_5861966 baseEnd_5861966 := by
    simpa [prefixWord, tailWord_5861966, baseEnd_5861966] using wordTrace_append hprefix tailTrace_5861966
  have hstable : (prefixWord ++ tailWord_5861966).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861966).length < 2 ^ (prefixWord ++ tailWord_5861966).sum := by decide
  have hdescent : baseEnd_5861966 < baseStart_5861966 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861966) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861969 : List Nat := [1, 2, 2, 1, 3, 4, 1, 9]
def baseStart_5861969 : Nat := 118140960795 + 5861969 * 2 ^ 59
def prefixEnd_5861969 : Nat := 4983230072969 + 3 ^ 40 * 5861969 * 2
def baseEnd_5861969 : Nat := 111481765879847435297363

theorem tailTrace_5861969 : CollatzResearch.WordTrace tailWord_5861969 prefixEnd_5861969 111481765879847435297363 := by
  unfold tailWord_5861969
  simp only [CollatzResearch.WordTrace]
  refine ⟨213803574100094932445116961, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142535716066729954963411307 213803574100094932445116961)
  ·
    refine ⟨160352680575071199333837721, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213803574100094932445116961 160352680575071199333837721)
    ·
      refine ⟨120264510431303399500378291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160352680575071199333837721 120264510431303399500378291)
      ·
        refine ⟨180396765646955099250567437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120264510431303399500378291 180396765646955099250567437)
        ·
          refine ⟨67648787117608162218962789, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180396765646955099250567437 67648787117608162218962789)
          ·
            refine ⟨12684147584551530416055523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67648787117608162218962789 12684147584551530416055523)
            ·
              refine ⟨19026221376827295624083285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12684147584551530416055523 19026221376827295624083285)
              ·
                refine ⟨111481765879847435297363, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19026221376827295624083285 111481765879847435297363)
                ·
                  rfl

theorem cell23_5861969_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 3, 4, 1, 9].length) (baseStart_5861969 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861969 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861969 prefixEnd_5861969 := by exact prefixLift 5861969
  have htrace : WordTrace (prefixWord ++ tailWord_5861969) baseStart_5861969 baseEnd_5861969 := by
    simpa [prefixWord, tailWord_5861969, baseEnd_5861969] using wordTrace_append hprefix tailTrace_5861969
  have hstable : (prefixWord ++ tailWord_5861969).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861969).length < 2 ^ (prefixWord ++ tailWord_5861969).sum := by decide
  have hdescent : baseEnd_5861969 < baseStart_5861969 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861969) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5861997 : List Nat := [1, 5, 1, 1, 3, 3, 1, 1, 3, 2, 2]
def baseStart_5861997 : Nat := 118140960795 + 5861997 * 2 ^ 59
def prefixEnd_5861997 : Nat := 4983230072969 + 3 ^ 40 * 5861997 * 2
def baseEnd_5861997 : Nat := 3010022056214206643478673

theorem tailTrace_5861997 : CollatzResearch.WordTrace tailWord_5861997 prefixEnd_5861997 3010022056214206643478673 := by
  unfold tailWord_5861997
  simp only [CollatzResearch.WordTrace]
  refine ⟨213804595343993493227136245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142536396895995662151424163 213804595343993493227136245)
  ·
    refine ⟨20044180813499389990044023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213804595343993493227136245 20044180813499389990044023)
    ·
      refine ⟨30066271220249084985066035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20044180813499389990044023 30066271220249084985066035)
      ·
        refine ⟨45099406830373627477599053, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30066271220249084985066035 45099406830373627477599053)
        ·
          refine ⟨16912277561390110304099645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45099406830373627477599053 16912277561390110304099645)
          ·
            refine ⟨6342104085521291364037367, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16912277561390110304099645 6342104085521291364037367)
            ·
              refine ⟨9513156128281937046056051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342104085521291364037367 9513156128281937046056051)
              ·
                refine ⟨14269734192422905569084077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9513156128281937046056051 14269734192422905569084077)
                ·
                  refine ⟨5351150322158589588406529, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14269734192422905569084077 5351150322158589588406529)
                  ·
                    refine ⟨4013362741618942191304897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5351150322158589588406529 4013362741618942191304897)
                    ·
                      refine ⟨3010022056214206643478673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013362741618942191304897 3010022056214206643478673)
                      ·
                        rfl

theorem cell23_5861997_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 3, 3, 1, 1, 3, 2, 2].length) (baseStart_5861997 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5861997 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5861997 prefixEnd_5861997 := by exact prefixLift 5861997
  have htrace : WordTrace (prefixWord ++ tailWord_5861997) baseStart_5861997 baseEnd_5861997 := by
    simpa [prefixWord, tailWord_5861997, baseEnd_5861997] using wordTrace_append hprefix tailTrace_5861997
  have hstable : (prefixWord ++ tailWord_5861997).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5861997).length < 2 ^ (prefixWord ++ tailWord_5861997).sum := by decide
  have hdescent : baseEnd_5861997 < baseStart_5861997 := by decide
  rcases family_descends (prefixWord ++ tailWord_5861997) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862023 : List Nat := [1, 1, 4, 2, 1, 2, 3, 1, 3, 3, 2]
def baseStart_5862023 : Nat := 118140960795 + 5862023 * 2 ^ 59
def prefixEnd_5862023 : Nat := 4983230072969 + 3 ^ 40 * 5862023 * 2
def baseEnd_5862023 : Nat := 3010035406711223541753553

theorem tailTrace_5862023 : CollatzResearch.WordTrace tailWord_5862023 prefixEnd_5862023 3010035406711223541753553 := by
  unfold tailWord_5862023
  simp only [CollatzResearch.WordTrace]
  refine ⟨213805543641899299667582723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142537029094599533111721815 213805543641899299667582723)
  ·
    refine ⟨320708315462848949501374085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213805543641899299667582723 320708315462848949501374085)
    ·
      refine ⟨60132809149284178031507641, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320708315462848949501374085 60132809149284178031507641)
      ·
        refine ⟨45099606861963133523630731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60132809149284178031507641 45099606861963133523630731)
        ·
          refine ⟨67649410292944700285446097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45099606861963133523630731 67649410292944700285446097)
          ·
            refine ⟨50737057719708525214084573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67649410292944700285446097 50737057719708525214084573)
            ·
              refine ⟨19026396644890696955281715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50737057719708525214084573 19026396644890696955281715)
              ·
                refine ⟨28539594967336045432922573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19026396644890696955281715 28539594967336045432922573)
                ·
                  refine ⟨10702348112751017037345965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28539594967336045432922573 10702348112751017037345965)
                  ·
                    refine ⟨4013380542281631389004737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10702348112751017037345965 4013380542281631389004737)
                    ·
                      refine ⟨3010035406711223541753553, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013380542281631389004737 3010035406711223541753553)
                      ·
                        rfl

theorem cell23_5862023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 1, 2, 3, 1, 3, 3, 2].length) (baseStart_5862023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862023 prefixEnd_5862023 := by exact prefixLift 5862023
  have htrace : WordTrace (prefixWord ++ tailWord_5862023) baseStart_5862023 baseEnd_5862023 := by
    simpa [prefixWord, tailWord_5862023, baseEnd_5862023] using wordTrace_append hprefix tailTrace_5862023
  have hstable : (prefixWord ++ tailWord_5862023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862023).length < 2 ^ (prefixWord ++ tailWord_5862023).sum := by decide
  have hdescent : baseEnd_5862023 < baseStart_5862023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862076 : List Nat := [2, 2, 2, 3, 1, 1, 3, 2, 7]
def baseStart_5862076 : Nat := 118140960795 + 5862076 * 2 ^ 59
def prefixEnd_5862076 : Nat := 4983230072969 + 3 ^ 40 * 5862076 * 2
def baseEnd_5862076 : Nat := 334451402353990203821201

theorem tailTrace_5862076 : CollatzResearch.WordTrace tailWord_5862076 prefixEnd_5862076 334451402353990203821201 := by
  unfold tailWord_5862076
  simp only [CollatzResearch.WordTrace]
  refine ⟨106903738355353644859631041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142538317807138193146174721 106903738355353644859631041)
  ·
    refine ⟨80177803766515233644723281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106903738355353644859631041 80177803766515233644723281)
    ·
      refine ⟨60133352824886425233542461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80177803766515233644723281 60133352824886425233542461)
      ·
        refine ⟨22550007309332409462578423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60133352824886425233542461 22550007309332409462578423)
        ·
          refine ⟨33825010963998614193867635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22550007309332409462578423 33825010963998614193867635)
          ·
            refine ⟨50737516445997921290801453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33825010963998614193867635 50737516445997921290801453)
            ·
              refine ⟨19026568667249220484050545, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50737516445997921290801453 19026568667249220484050545)
              ·
                refine ⟨14269926500436915363037909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19026568667249220484050545 14269926500436915363037909)
                ·
                  refine ⟨334451402353990203821201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14269926500436915363037909 334451402353990203821201)
                  ·
                    rfl

theorem cell23_5862076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 3, 1, 1, 3, 2, 7].length) (baseStart_5862076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862076 prefixEnd_5862076 := by exact prefixLift 5862076
  have htrace : WordTrace (prefixWord ++ tailWord_5862076) baseStart_5862076 baseEnd_5862076 := by
    simpa [prefixWord, tailWord_5862076, baseEnd_5862076] using wordTrace_append hprefix tailTrace_5862076
  have hstable : (prefixWord ++ tailWord_5862076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862076).length < 2 ^ (prefixWord ++ tailWord_5862076).sum := by decide
  have hdescent : baseEnd_5862076 < baseStart_5862076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862106 : List Nat := [3, 1, 1, 2, 2, 2, 2, 1, 4, 5]
def baseStart_5862106 : Nat := 118140960795 + 5862106 * 2 ^ 59
def prefixEnd_5862106 : Nat := 4983230072969 + 3 ^ 40 * 5862106 * 2
def baseEnd_5862106 : Nat := 1003359341868515572338557

theorem tailTrace_5862106 : CollatzResearch.WordTrace tailWord_5862106 prefixEnd_5862106 1003359341868515572338557 := by
  unfold tailWord_5862106
  simp only [CollatzResearch.WordTrace]
  refine ⟨53452142725149651210713543, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142539047267065736561902781 53452142725149651210713543)
  ·
    refine ⟨80178214087724476816070315, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53452142725149651210713543 80178214087724476816070315)
    ·
      refine ⟨120267321131586715224105473, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80178214087724476816070315 120267321131586715224105473)
      ·
        refine ⟨90200490848690036418079105, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120267321131586715224105473 90200490848690036418079105)
        ·
          refine ⟨67650368136517527313559329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90200490848690036418079105 67650368136517527313559329)
          ·
            refine ⟨50737776102388145485169497, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67650368136517527313559329 50737776102388145485169497)
            ·
              refine ⟨38053332076791109113877123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50737776102388145485169497 38053332076791109113877123)
              ·
                refine ⟨57079998115186663670815685, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38053332076791109113877123 57079998115186663670815685)
                ·
                  refine ⟨10702499646597499438277941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57079998115186663670815685 10702499646597499438277941)
                  ·
                    refine ⟨1003359341868515572338557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10702499646597499438277941 1003359341868515572338557)
                    ·
                      rfl

theorem cell23_5862106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 2, 2, 1, 4, 5].length) (baseStart_5862106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862106 prefixEnd_5862106 := by exact prefixLift 5862106
  have htrace : WordTrace (prefixWord ++ tailWord_5862106) baseStart_5862106 baseEnd_5862106 := by
    simpa [prefixWord, tailWord_5862106, baseEnd_5862106] using wordTrace_append hprefix tailTrace_5862106
  have hstable : (prefixWord ++ tailWord_5862106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862106).length < 2 ^ (prefixWord ++ tailWord_5862106).sum := by decide
  have hdescent : baseEnd_5862106 < baseStart_5862106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862163 : List Nat := [1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 3]
def baseStart_5862163 : Nat := 118140960795 + 5862163 * 2 ^ 59
def prefixEnd_5862163 : Nat := 4983230072969 + 3 ^ 40 * 5862163 * 2
def baseEnd_5862163 : Nat := 3010107294002852994002909

theorem tailTrace_5862163 : CollatzResearch.WordTrace tailWord_5862163 prefixEnd_5862163 3010107294002852994002909 := by
  unfold tailWord_5862163
  simp only [CollatzResearch.WordTrace]
  refine ⟨213810649861392103577679143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142540433240928069051786095 213810649861392103577679143)
  ·
    refine ⟨320715974792088155366518715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213810649861392103577679143 320715974792088155366518715)
    ·
      refine ⟨481073962188132233049778073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320715974792088155366518715 481073962188132233049778073)
      ·
        refine ⟨360805471641099174787333555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481073962188132233049778073 360805471641099174787333555)
        ·
          refine ⟨541208207461648762181000333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360805471641099174787333555 541208207461648762181000333)
          ·
            refine ⟨202953077798118285817875125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541208207461648762181000333 202953077798118285817875125)
            ·
              refine ⟨19026851043573589295425793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 202953077798118285817875125 19026851043573589295425793)
              ·
                refine ⟨14270138282680191971569345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19026851043573589295425793 14270138282680191971569345)
                ·
                  refine ⟨10702603712010143978677009, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14270138282680191971569345 10702603712010143978677009)
                  ·
                    refine ⟨8026952784007607984007757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10702603712010143978677009 8026952784007607984007757)
                    ·
                      refine ⟨3010107294002852994002909, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8026952784007607984007757 3010107294002852994002909)
                      ·
                        rfl

theorem cell23_5862163_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 5, 2, 2, 2, 3].length) (baseStart_5862163 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862163 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862163 prefixEnd_5862163 := by exact prefixLift 5862163
  have htrace : WordTrace (prefixWord ++ tailWord_5862163) baseStart_5862163 baseEnd_5862163 := by
    simpa [prefixWord, tailWord_5862163, baseEnd_5862163] using wordTrace_append hprefix tailTrace_5862163
  have hstable : (prefixWord ++ tailWord_5862163).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862163).length < 2 ^ (prefixWord ++ tailWord_5862163).sum := by decide
  have hdescent : baseEnd_5862163 < baseStart_5862163 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862163) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862233 : List Nat := [1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 4]
def baseStart_5862233 : Nat := 118140960795 + 5862233 * 2 ^ 59
def prefixEnd_5862233 : Nat := 4983230072969 + 3 ^ 40 * 5862233 * 2
def baseEnd_5862233 : Nat := 3010143237648667720127587

theorem tailTrace_5862233 : CollatzResearch.WordTrace tailWord_5862233 prefixEnd_5862233 3010143237648667720127587 := by
  unfold tailWord_5862233
  simp only [CollatzResearch.WordTrace]
  refine ⟨213813202971138505532727353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142542135314092337021818235 213813202971138505532727353)
  ·
    refine ⟨160359902228353879149545515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213813202971138505532727353 160359902228353879149545515)
    ·
      refine ⟨240539853342530818724318273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160359902228353879149545515 240539853342530818724318273)
      ·
        refine ⟨180404890006898114043238705, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240539853342530818724318273 180404890006898114043238705)
        ·
          refine ⟨135303667505173585532429029, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180404890006898114043238705 135303667505173585532429029)
          ·
            refine ⟨25369437657220047287330443, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135303667505173585532429029 25369437657220047287330443)
            ·
              refine ⟨38054156485830070930995665, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25369437657220047287330443 38054156485830070930995665)
              ·
                refine ⟨28540617364372553198246749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38054156485830070930995665 28540617364372553198246749)
                ·
                  refine ⟨10702731511639707449342531, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28540617364372553198246749 10702731511639707449342531)
                  ·
                    refine ⟨16054097267459561174013797, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10702731511639707449342531 16054097267459561174013797)
                    ·
                      refine ⟨3010143237648667720127587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16054097267459561174013797 3010143237648667720127587)
                      ·
                        rfl

theorem cell23_5862233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 4, 1, 2, 3, 1, 4].length) (baseStart_5862233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862233 prefixEnd_5862233 := by exact prefixLift 5862233
  have htrace : WordTrace (prefixWord ++ tailWord_5862233) baseStart_5862233 baseEnd_5862233 := by
    simpa [prefixWord, tailWord_5862233, baseEnd_5862233] using wordTrace_append hprefix tailTrace_5862233
  have hstable : (prefixWord ++ tailWord_5862233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862233).length < 2 ^ (prefixWord ++ tailWord_5862233).sum := by decide
  have hdescent : baseEnd_5862233 < baseStart_5862233 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862243 : List Nat := [1, 1, 1, 5, 3, 1, 1, 3, 1, 6]
def baseStart_5862243 : Nat := 118140960795 + 5862243 * 2 ^ 59
def prefixEnd_5862243 : Nat := 4983230072969 + 3 ^ 40 * 5862243 * 2
def baseEnd_5862243 : Nat := 1003382790818404227000847

theorem tailTrace_5862243 : CollatzResearch.WordTrace tailWord_5862243 prefixEnd_5862243 1003382790818404227000847 := by
  unfold tailWord_5862243
  simp only [CollatzResearch.WordTrace]
  refine ⟨213813567701102277240591383, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142542378467401518160394255 213813567701102277240591383)
  ·
    refine ⟨320720351551653415860887075, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213813567701102277240591383 320720351551653415860887075)
    ·
      refine ⟨481080527327480123791330613, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320720351551653415860887075 481080527327480123791330613)
      ·
        refine ⟨45101299436951261605437245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 481080527327480123791330613 45101299436951261605437245)
        ·
          refine ⟨16912987288856723102038967, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45101299436951261605437245 16912987288856723102038967)
          ·
            refine ⟨25369480933285084653058451, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16912987288856723102038967 25369480933285084653058451)
            ·
              refine ⟨38054221399927626979587677, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25369480933285084653058451 38054221399927626979587677)
              ·
                refine ⟨14270333024972860117345379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38054221399927626979587677 14270333024972860117345379)
                ·
                  refine ⟨21405499537459290176018069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14270333024972860117345379 21405499537459290176018069)
                  ·
                    refine ⟨1003382790818404227000847, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21405499537459290176018069 1003382790818404227000847)
                    ·
                      rfl

theorem cell23_5862243_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 3, 1, 1, 3, 1, 6].length) (baseStart_5862243 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862243 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862243 prefixEnd_5862243 := by exact prefixLift 5862243
  have htrace : WordTrace (prefixWord ++ tailWord_5862243) baseStart_5862243 baseEnd_5862243 := by
    simpa [prefixWord, tailWord_5862243, baseEnd_5862243] using wordTrace_append hprefix tailTrace_5862243
  have hstable : (prefixWord ++ tailWord_5862243).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862243).length < 2 ^ (prefixWord ++ tailWord_5862243).sum := by decide
  have hdescent : baseEnd_5862243 < baseStart_5862243 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862243) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862256 : List Nat := [2, 1, 1, 1, 4, 1, 2, 11]
def baseStart_5862256 : Nat := 118140960795 + 5862256 * 2 ^ 59
def prefixEnd_5862256 : Nat := 4983230072969 + 3 ^ 40 * 5862256 * 2
def baseEnd_5862256 : Nat := 111487223989026708523703

theorem tailTrace_5862256 : CollatzResearch.WordTrace tailWord_5862256 prefixEnd_5862256 111487223989026708523703 := by
  unfold tailWord_5862256
  simp only [CollatzResearch.WordTrace]
  refine ⟨106907020925027590230407311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142542694566703453640543081 106907020925027590230407311)
  ·
    refine ⟨160360531387541385345610967, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106907020925027590230407311 160360531387541385345610967)
    ·
      refine ⟨240540797081312078018416451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160360531387541385345610967 240540797081312078018416451)
      ·
        refine ⟨360811195621968117027624677, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240540797081312078018416451 360811195621968117027624677)
        ·
          refine ⟨67652099179119021942679627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360811195621968117027624677 67652099179119021942679627)
          ·
            refine ⟨101478148768678532914019441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67652099179119021942679627 101478148768678532914019441)
            ·
              refine ⟨76108611576508899685514581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101478148768678532914019441 76108611576508899685514581)
              ·
                refine ⟨111487223989026708523703, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 11 76108611576508899685514581 111487223989026708523703)
                ·
                  rfl

theorem cell23_5862256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 11].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 4, 1, 2, 11].length) (baseStart_5862256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862256 prefixEnd_5862256 := by exact prefixLift 5862256
  have htrace : WordTrace (prefixWord ++ tailWord_5862256) baseStart_5862256 baseEnd_5862256 := by
    simpa [prefixWord, tailWord_5862256, baseEnd_5862256] using wordTrace_append hprefix tailTrace_5862256
  have hstable : (prefixWord ++ tailWord_5862256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862256).length < 2 ^ (prefixWord ++ tailWord_5862256).sum := by decide
  have hdescent : baseEnd_5862256 < baseStart_5862256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862277 : List Nat := [1, 3, 1, 1, 3, 5, 1, 2, 2, 4]
def baseStart_5862277 : Nat := 118140960795 + 5862277 * 2 ^ 59
def prefixEnd_5862277 : Nat := 4983230072969 + 3 ^ 40 * 5862277 * 2
def baseEnd_5862277 : Nat := 1003388610265821849325795

theorem tailTrace_5862277 : CollatzResearch.WordTrace tailWord_5862277 prefixEnd_5862277 1003388610265821849325795 := by
  unfold tailWord_5862277
  simp only [CollatzResearch.WordTrace]
  refine ⟨213814807782979101047329085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142543205188652734031552723 213814807782979101047329085)
  ·
    refine ⟨80180552918617162892748407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213814807782979101047329085 80180552918617162892748407)
    ·
      refine ⟨120270829377925744339122611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80180552918617162892748407 120270829377925744339122611)
      ·
        refine ⟨180406244066888616508683917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120270829377925744339122611 180406244066888616508683917)
        ·
          refine ⟨67652341525083231190756469, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180406244066888616508683917 67652341525083231190756469)
          ·
            refine ⟨6342407017976552924133419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 67652341525083231190756469 6342407017976552924133419)
            ·
              refine ⟨9513610526964829386200129, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342407017976552924133419 9513610526964829386200129)
              ·
                refine ⟨7135207895223622039650097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9513610526964829386200129 7135207895223622039650097)
                ·
                  refine ⟨5351405921417716529737573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7135207895223622039650097 5351405921417716529737573)
                  ·
                    refine ⟨1003388610265821849325795, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351405921417716529737573 1003388610265821849325795)
                    ·
                      rfl

theorem cell23_5862277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 3, 5, 1, 2, 2, 4].length) (baseStart_5862277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862277 prefixEnd_5862277 := by exact prefixLift 5862277
  have htrace : WordTrace (prefixWord ++ tailWord_5862277) baseStart_5862277 baseEnd_5862277 := by
    simpa [prefixWord, tailWord_5862277, baseEnd_5862277] using wordTrace_append hprefix tailTrace_5862277
  have hstable : (prefixWord ++ tailWord_5862277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862277).length < 2 ^ (prefixWord ++ tailWord_5862277).sum := by decide
  have hdescent : baseEnd_5862277 < baseStart_5862277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862283 : List Nat := [1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 3]
def baseStart_5862283 : Nat := 118140960795 + 5862283 * 2 ^ 59
def prefixEnd_5862283 : Nat := 4983230072969 + 3 ^ 40 * 5862283 * 2
def baseEnd_5862283 : Nat := 3010168911681392524502357

theorem tailTrace_5862283 : CollatzResearch.WordTrace tailWord_5862283 prefixEnd_5862283 3010168911681392524502357 := by
  unfold tailWord_5862283
  simp only [CollatzResearch.WordTrace]
  refine ⟨213815026620957364072047503, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142543351080638242714698335 213815026620957364072047503)
  ·
    refine ⟨320722539931436046108071255, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213815026620957364072047503 320722539931436046108071255)
    ·
      refine ⟨481083809897154069162106883, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320722539931436046108071255 481083809897154069162106883)
      ·
        refine ⟨721625714845731103743160325, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481083809897154069162106883 721625714845731103743160325)
        ·
          refine ⟨135304821533574581951842561, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 721625714845731103743160325 135304821533574581951842561)
          ·
            refine ⟨101478616150180936463881921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135304821533574581951842561 101478616150180936463881921)
            ·
              refine ⟨76108962112635702347911441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101478616150180936463881921 76108962112635702347911441)
              ·
                refine ⟨57081721584476776760933581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76108962112635702347911441 57081721584476776760933581)
                ·
                  refine ⟨21405645594178791285350093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57081721584476776760933581 21405645594178791285350093)
                  ·
                    refine ⟨8027117097817046732006285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21405645594178791285350093 8027117097817046732006285)
                    ·
                      refine ⟨3010168911681392524502357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8027117097817046732006285 3010168911681392524502357)
                      ·
                        rfl

theorem cell23_5862283_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 2, 2, 2, 3, 3, 3].length) (baseStart_5862283 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862283 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862283 prefixEnd_5862283 := by exact prefixLift 5862283
  have htrace : WordTrace (prefixWord ++ tailWord_5862283) baseStart_5862283 baseEnd_5862283 := by
    simpa [prefixWord, tailWord_5862283, baseEnd_5862283] using wordTrace_append hprefix tailTrace_5862283
  have hstable : (prefixWord ++ tailWord_5862283).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862283).length < 2 ^ (prefixWord ++ tailWord_5862283).sum := by decide
  have hdescent : baseEnd_5862283 < baseStart_5862283 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862283) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862284 : List Nat := [2, 2, 1, 2, 1, 2, 4, 4, 1, 2, 2]
def baseStart_5862284 : Nat := 118140960795 + 5862284 * 2 ^ 59
def prefixEnd_5862284 : Nat := 4983230072969 + 3 ^ 40 * 5862284 * 2
def baseEnd_5862284 : Nat := 3010169425162047020589853

theorem tailTrace_5862284 : CollatzResearch.WordTrace tailWord_5862284 prefixEnd_5862284 3010169425162047020589853 := by
  unfold tailWord_5862284
  simp only [CollatzResearch.WordTrace]
  refine ⟨106907531546976870621416953, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142543375395969160828555937 106907531546976870621416953)
  ·
    refine ⟨80180648660232652966062715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106907531546976870621416953 80180648660232652966062715)
    ·
      refine ⟨120270972990348979449094073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80180648660232652966062715 120270972990348979449094073)
      ·
        refine ⟨90203229742761734586820555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120270972990348979449094073 90203229742761734586820555)
        ·
          refine ⟨135304844614142601880230833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90203229742761734586820555 135304844614142601880230833)
          ·
            refine ⟨101478633460606951410173125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135304844614142601880230833 101478633460606951410173125)
            ·
              refine ⟨19027243773863803389407461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101478633460606951410173125 19027243773863803389407461)
              ·
                refine ⟨3567608207599463135513899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19027243773863803389407461 3567608207599463135513899)
                ·
                  refine ⟨5351412311399194703270849, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567608207599463135513899 5351412311399194703270849)
                  ·
                    refine ⟨4013559233549396027453137, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5351412311399194703270849 4013559233549396027453137)
                    ·
                      refine ⟨3010169425162047020589853, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013559233549396027453137 3010169425162047020589853)
                      ·
                        rfl

theorem cell23_5862284_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 4, 4, 1, 2, 2].length) (baseStart_5862284 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862284 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862284 prefixEnd_5862284 := by exact prefixLift 5862284
  have htrace : WordTrace (prefixWord ++ tailWord_5862284) baseStart_5862284 baseEnd_5862284 := by
    simpa [prefixWord, tailWord_5862284, baseEnd_5862284] using wordTrace_append hprefix tailTrace_5862284
  have hstable : (prefixWord ++ tailWord_5862284).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862284).length < 2 ^ (prefixWord ++ tailWord_5862284).sum := by decide
  have hdescent : baseEnd_5862284 < baseStart_5862284 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862284) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862294 : List Nat := [5, 3, 1, 1, 1, 1, 3, 1, 1, 6]
def baseStart_5862294 : Nat := 118140960795 + 5862294 * 2 ^ 59
def prefixEnd_5862294 : Nat := 4983230072969 + 3 ^ 40 * 5862294 * 2
def baseEnd_5862294 : Nat := 1003391519989530660488269

theorem tailTrace_5862294 : CollatzResearch.WordTrace tailWord_5862294 prefixEnd_5862294 1003391519989530660488269 := by
  unfold tailWord_5862294
  simp only [CollatzResearch.WordTrace]
  refine ⟨13363464238994844559418621, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142543618549278341967131957 13363464238994844559418621)
  ·
    refine ⟨5011299089623066709781983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 13363464238994844559418621 5011299089623066709781983)
    ·
      refine ⟨7516948634434600064672975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011299089623066709781983 7516948634434600064672975)
      ·
        refine ⟨11275422951651900097009463, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7516948634434600064672975 11275422951651900097009463)
        ·
          refine ⟨16913134427477850145514195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11275422951651900097009463 16913134427477850145514195)
          ·
            refine ⟨25369701641216775218271293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16913134427477850145514195 25369701641216775218271293)
            ·
              refine ⟨9513638115456290706851735, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25369701641216775218271293 9513638115456290706851735)
              ·
                refine ⟨14270457173184436060277603, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9513638115456290706851735 14270457173184436060277603)
                ·
                  refine ⟨21405685759776654090416405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14270457173184436060277603 21405685759776654090416405)
                  ·
                    refine ⟨1003391519989530660488269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21405685759776654090416405 1003391519989530660488269)
                    ·
                      rfl

theorem cell23_5862294_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 3, 1, 1, 1, 1, 3, 1, 1, 6].length) (baseStart_5862294 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862294 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862294 prefixEnd_5862294 := by exact prefixLift 5862294
  have htrace : WordTrace (prefixWord ++ tailWord_5862294) baseStart_5862294 baseEnd_5862294 := by
    simpa [prefixWord, tailWord_5862294, baseEnd_5862294] using wordTrace_append hprefix tailTrace_5862294
  have hstable : (prefixWord ++ tailWord_5862294).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862294).length < 2 ^ (prefixWord ++ tailWord_5862294).sum := by decide
  have hdescent : baseEnd_5862294 < baseStart_5862294 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862294) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862327 : List Nat := [1, 1, 3, 1, 3, 1, 4, 3, 1, 3, 2]
def baseStart_5862327 : Nat := 118140960795 + 5862327 * 2 ^ 59
def prefixEnd_5862327 : Nat := 4983230072969 + 3 ^ 40 * 5862327 * 2
def baseEnd_5862327 : Nat := 3010191504830190352352155

theorem tailTrace_5862327 : CollatzResearch.WordTrace tailWord_5862327 prefixEnd_5862327 3010191504830190352352155 := by
  unfold tailWord_5862327
  simp only [CollatzResearch.WordTrace]
  refine ⟨213816631432797959586649235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142544420955198639724432823 213816631432797959586649235)
  ·
    refine ⟨320724947149196939379973853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213816631432797959586649235 320724947149196939379973853)
    ·
      refine ⟨120271855180948852267490195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320724947149196939379973853 120271855180948852267490195)
      ·
        refine ⟨180407782771423278401235293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120271855180948852267490195 180407782771423278401235293)
        ·
          refine ⟨67652918539283729400463235, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180407782771423278401235293 67652918539283729400463235)
          ·
            refine ⟨101479377808925594100694853, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67652918539283729400463235 101479377808925594100694853)
            ·
              refine ⟨19027383339173548893880285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101479377808925594100694853 19027383339173548893880285)
              ·
                refine ⟨7135268752190080835205107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19027383339173548893880285 7135268752190080835205107)
                ·
                  refine ⟨10702903128285121252807661, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7135268752190080835205107 10702903128285121252807661)
                  ·
                    refine ⟨4013588673106920469802873, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10702903128285121252807661 4013588673106920469802873)
                    ·
                      refine ⟨3010191504830190352352155, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013588673106920469802873 3010191504830190352352155)
                      ·
                        rfl

theorem cell23_5862327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 1, 4, 3, 1, 3, 2].length) (baseStart_5862327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862327 prefixEnd_5862327 := by exact prefixLift 5862327
  have htrace : WordTrace (prefixWord ++ tailWord_5862327) baseStart_5862327 baseEnd_5862327 := by
    simpa [prefixWord, tailWord_5862327, baseEnd_5862327] using wordTrace_append hprefix tailTrace_5862327
  have hstable : (prefixWord ++ tailWord_5862327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862327).length < 2 ^ (prefixWord ++ tailWord_5862327).sum := by decide
  have hdescent : baseEnd_5862327 < baseStart_5862327 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862353 : List Nat := [1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 4]
def baseStart_5862353 : Nat := 118140960795 + 5862353 * 2 ^ 59
def prefixEnd_5862353 : Nat := 4983230072969 + 3 ^ 40 * 5862353 * 2
def baseEnd_5862353 : Nat := 3010204855327207250627035

theorem tailTrace_5862353 : CollatzResearch.WordTrace tailWord_5862353 prefixEnd_5862353 3010204855327207250627035 := by
  unfold tailWord_5862353
  simp only [CollatzResearch.WordTrace]
  refine ⟨213817579730703766027095713, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142545053153802510684730475 213817579730703766027095713)
  ·
    refine ⟨160363184798027824520321785, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213817579730703766027095713 160363184798027824520321785)
    ·
      refine ⟨120272388598520868390241339, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160363184798027824520321785 120272388598520868390241339)
      ·
        refine ⟨180408582897781302585362009, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120272388598520868390241339 180408582897781302585362009)
        ·
          refine ⟨135306437173335976939021507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180408582897781302585362009 135306437173335976939021507)
          ·
            refine ⟨202959655760003965408532261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135306437173335976939021507 202959655760003965408532261)
            ·
              refine ⟨38054935455000743514099799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202959655760003965408532261 38054935455000743514099799)
              ·
                refine ⟨57082403182501115271149699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38054935455000743514099799 57082403182501115271149699)
                ·
                  refine ⟨85623604773751672906724549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57082403182501115271149699 85623604773751672906724549)
                  ·
                    refine ⟨16054425895078438670010853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85623604773751672906724549 16054425895078438670010853)
                    ·
                      refine ⟨3010204855327207250627035, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16054425895078438670010853 3010204855327207250627035)
                      ·
                        rfl

theorem cell23_5862353_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 1, 4, 1, 1, 4, 4].length) (baseStart_5862353 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862353 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862353 prefixEnd_5862353 := by exact prefixLift 5862353
  have htrace : WordTrace (prefixWord ++ tailWord_5862353) baseStart_5862353 baseEnd_5862353 := by
    simpa [prefixWord, tailWord_5862353, baseEnd_5862353] using wordTrace_append hprefix tailTrace_5862353
  have hstable : (prefixWord ++ tailWord_5862353).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862353).length < 2 ^ (prefixWord ++ tailWord_5862353).sum := by decide
  have hdescent : baseEnd_5862353 < baseStart_5862353 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862353) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862443 : List Nat := [1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6]
def baseStart_5862443 : Nat := 118140960795 + 5862443 * 2 ^ 59
def prefixEnd_5862443 : Nat := 4983230072969 + 3 ^ 40 * 5862443 * 2
def baseEnd_5862443 : Nat := 3010251068586111898501621

theorem tailTrace_5862443 : CollatzResearch.WordTrace tailWord_5862443 prefixEnd_5862443 3010251068586111898501621 := by
  unfold tailWord_5862443
  simp only [CollatzResearch.WordTrace]
  refine ⟨213820862300377711397871983, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142547241533585140931914655 213820862300377711397871983)
  ·
    refine ⟨320731293450566567096807975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213820862300377711397871983 320731293450566567096807975)
    ·
      refine ⟨481096940175849850645211963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320731293450566567096807975 481096940175849850645211963)
      ·
        refine ⟨721645410263774775967817945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481096940175849850645211963 721645410263774775967817945)
        ·
          refine ⟨541234057697831081975863459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721645410263774775967817945 541234057697831081975863459)
          ·
            refine ⟨811851086546746622963795189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541234057697831081975863459 811851086546746622963795189)
            ·
              refine ⟨76111039363757495902855799, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 811851086546746622963795189 76111039363757495902855799)
              ·
                refine ⟨114166559045636243854283699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76111039363757495902855799 114166559045636243854283699)
                ·
                  refine ⟨171249838568454365781425549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114166559045636243854283699 171249838568454365781425549)
                  ·
                    refine ⟨64218689463170387168034581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 171249838568454365781425549 64218689463170387168034581)
                    ·
                      refine ⟨3010251068586111898501621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64218689463170387168034581 3010251068586111898501621)
                      ·
                        rfl

theorem cell23_5862443_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 1, 5, 1, 1, 3, 6].length) (baseStart_5862443 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862443 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862443 prefixEnd_5862443 := by exact prefixLift 5862443
  have htrace : WordTrace (prefixWord ++ tailWord_5862443) baseStart_5862443 baseEnd_5862443 := by
    simpa [prefixWord, tailWord_5862443, baseEnd_5862443] using wordTrace_append hprefix tailTrace_5862443
  have hstable : (prefixWord ++ tailWord_5862443).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862443).length < 2 ^ (prefixWord ++ tailWord_5862443).sum := by decide
  have hdescent : baseEnd_5862443 < baseStart_5862443 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862443) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862457 : List Nat := [1, 2, 1, 5, 2, 1, 1, 3, 3, 4]
def baseStart_5862457 : Nat := 118140960795 + 5862457 * 2 ^ 59
def prefixEnd_5862457 : Nat := 4983230072969 + 3 ^ 40 * 5862457 * 2
def baseEnd_5862457 : Nat := 1003419419105091614575519

theorem tailTrace_5862457 : CollatzResearch.WordTrace tailWord_5862457 prefixEnd_5862457 1003419419105091614575519 := by
  unfold tailWord_5862457
  simp only [CollatzResearch.WordTrace]
  refine ⟨213821372922326991788881625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142547581948217994525921083 213821372922326991788881625)
  ·
    refine ⟨160366029691745243841661219, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213821372922326991788881625 160366029691745243841661219)
    ·
      refine ⟨240549044537617865762491829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160366029691745243841661219 240549044537617865762491829)
      ·
        refine ⟨22551472925401674915233609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 240549044537617865762491829 22551472925401674915233609)
        ·
          refine ⟨16913604694051256186425207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22551472925401674915233609 16913604694051256186425207)
          ·
            refine ⟨25370407041076884279637811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16913604694051256186425207 25370407041076884279637811)
            ·
              refine ⟨38055610561615326419456717, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25370407041076884279637811 38055610561615326419456717)
              ·
                refine ⟨14270853960605747407296269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38055610561615326419456717 14270853960605747407296269)
                ·
                  refine ⟨5351570235227155277736101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14270853960605747407296269 5351570235227155277736101)
                  ·
                    refine ⟨1003419419105091614575519, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351570235227155277736101 1003419419105091614575519)
                    ·
                      rfl

theorem cell23_5862457_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 2, 1, 1, 3, 3, 4].length) (baseStart_5862457 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862457 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862457 prefixEnd_5862457 := by exact prefixLift 5862457
  have htrace : WordTrace (prefixWord ++ tailWord_5862457) baseStart_5862457 baseEnd_5862457 := by
    simpa [prefixWord, tailWord_5862457, baseEnd_5862457] using wordTrace_append hprefix tailTrace_5862457
  have hstable : (prefixWord ++ tailWord_5862457).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862457).length < 2 ^ (prefixWord ++ tailWord_5862457).sum := by decide
  have hdescent : baseEnd_5862457 < baseStart_5862457 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862457) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862497 : List Nat := [1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 3]
def baseStart_5862497 : Nat := 118140960795 + 5862497 * 2 ^ 59
def prefixEnd_5862497 : Nat := 4983230072969 + 3 ^ 40 * 5862497 * 2
def baseEnd_5862497 : Nat := 3010278796541454687226373

theorem tailTrace_5862497 : CollatzResearch.WordTrace tailWord_5862497 prefixEnd_5862497 3010278796541454687226373 := by
  unfold tailWord_5862497
  simp only [CollatzResearch.WordTrace]
  refine ⟨213822831842182078620337745, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142548554561454719080225163 213822831842182078620337745)
  ·
    refine ⟨160367123881636558965253309, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213822831842182078620337745 160367123881636558965253309)
    ·
      refine ⟨60137671455613709611969991, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160367123881636558965253309 60137671455613709611969991)
      ·
        refine ⟨90206507183420564417954987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60137671455613709611969991 90206507183420564417954987)
        ·
          refine ⟨135309760775130846626932481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90206507183420564417954987 135309760775130846626932481)
          ·
            refine ⟨101482320581348134970199361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135309760775130846626932481 101482320581348134970199361)
            ·
              refine ⟨76111740436011101227649521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101482320581348134970199361 76111740436011101227649521)
              ·
                refine ⟨57083805327008325920737141, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76111740436011101227649521 57083805327008325920737141)
                ·
                  refine ⟨5351606749407030555069107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57083805327008325920737141 5351606749407030555069107)
                  ·
                    refine ⟨8027410124110545832603661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5351606749407030555069107 8027410124110545832603661)
                    ·
                      refine ⟨3010278796541454687226373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8027410124110545832603661 3010278796541454687226373)
                      ·
                        rfl

theorem cell23_5862497_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 2, 2, 2, 5, 1, 3].length) (baseStart_5862497 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862497 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862497 prefixEnd_5862497 := by exact prefixLift 5862497
  have htrace : WordTrace (prefixWord ++ tailWord_5862497) baseStart_5862497 baseEnd_5862497 := by
    simpa [prefixWord, tailWord_5862497, baseEnd_5862497] using wordTrace_append hprefix tailTrace_5862497
  have hstable : (prefixWord ++ tailWord_5862497).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862497).length < 2 ^ (prefixWord ++ tailWord_5862497).sum := by decide
  have hdescent : baseEnd_5862497 < baseStart_5862497 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862497) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862500 : List Nat := [2, 3, 1, 1, 2, 1, 1, 2, 5, 5]
def baseStart_5862500 : Nat := 118140960795 + 5862500 * 2 ^ 59
def prefixEnd_5862500 : Nat := 4983230072969 + 3 ^ 40 * 5862500 * 2
def baseEnd_5862500 : Nat := 1003426778994472725162953

theorem tailTrace_5862500 : CollatzResearch.WordTrace tailWord_5862500 prefixEnd_5862500 1003426778994472725162953 := by
  unfold tailWord_5862500
  simp only [CollatzResearch.WordTrace]
  refine ⟨106911470630585605066348477, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142548627507447473421797969 106911470630585605066348477)
  ·
    refine ⟨40091801486469601899880679, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106911470630585605066348477 40091801486469601899880679)
    ·
      refine ⟨60137702229704402849821019, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40091801486469601899880679 60137702229704402849821019)
      ·
        refine ⟨90206553344556604274731529, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60137702229704402849821019 90206553344556604274731529)
        ·
          refine ⟨67654915008417453206048647, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90206553344556604274731529 67654915008417453206048647)
          ·
            refine ⟨101482372512626179809072971, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67654915008417453206048647 101482372512626179809072971)
            ·
              refine ⟨152223558768939269713609457, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101482372512626179809072971 152223558768939269713609457)
              ·
                refine ⟨114167669076704452285207093, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152223558768939269713609457 114167669076704452285207093)
                ·
                  refine ⟨10703218975941042401738165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114167669076704452285207093 10703218975941042401738165)
                  ·
                    refine ⟨1003426778994472725162953, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10703218975941042401738165 1003426778994472725162953)
                    ·
                      rfl

theorem cell23_5862500_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 2, 1, 1, 2, 5, 5].length) (baseStart_5862500 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862500 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862500 prefixEnd_5862500 := by exact prefixLift 5862500
  have htrace : WordTrace (prefixWord ++ tailWord_5862500) baseStart_5862500 baseEnd_5862500 := by
    simpa [prefixWord, tailWord_5862500, baseEnd_5862500] using wordTrace_append hprefix tailTrace_5862500
  have hstable : (prefixWord ++ tailWord_5862500).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862500).length < 2 ^ (prefixWord ++ tailWord_5862500).sum := by decide
  have hdescent : baseEnd_5862500 < baseStart_5862500 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862500) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862521 : List Nat := [1, 2, 1, 3, 6, 1, 2, 1, 6]
def baseStart_5862521 : Nat := 118140960795 + 5862521 * 2 ^ 59
def prefixEnd_5862521 : Nat := 4983230072969 + 3 ^ 40 * 5862521 * 2
def baseEnd_5862521 : Nat := 334476791119684732591807

theorem tailTrace_5862521 : CollatzResearch.WordTrace tailWord_5862521 prefixEnd_5862521 334476791119684732591807 := by
  unfold tailWord_5862521
  simp only [CollatzResearch.WordTrace]
  refine ⟨213823707194095130719211417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142549138129396753812807611 213823707194095130719211417)
  ·
    refine ⟨160367780395571348039408563, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213823707194095130719211417 160367780395571348039408563)
    ·
      refine ⟨240551670593357022059112845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160367780395571348039408563 240551670593357022059112845)
      ·
        refine ⟨90206876472508883272167317, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240551670593357022059112845 90206876472508883272167317)
        ·
          refine ⟨4228447334648853903382843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 90206876472508883272167317 4228447334648853903382843)
          ·
            refine ⟨6342671001973280855074265, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4228447334648853903382843 6342671001973280855074265)
            ·
              refine ⟨4757003251479960641305699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6342671001973280855074265 4757003251479960641305699)
              ·
                refine ⟨7135504877219940961958549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757003251479960641305699 7135504877219940961958549)
                ·
                  refine ⟨334476791119684732591807, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7135504877219940961958549 334476791119684732591807)
                  ·
                    rfl

theorem cell23_5862521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 6, 1, 2, 1, 6].length) (baseStart_5862521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862521 prefixEnd_5862521 := by exact prefixLift 5862521
  have htrace : WordTrace (prefixWord ++ tailWord_5862521) baseStart_5862521 baseEnd_5862521 := by
    simpa [prefixWord, tailWord_5862521, baseEnd_5862521] using wordTrace_append hprefix tailTrace_5862521
  have hstable : (prefixWord ++ tailWord_5862521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862521).length < 2 ^ (prefixWord ++ tailWord_5862521).sum := by decide
  have hdescent : baseEnd_5862521 < baseStart_5862521 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862537 : List Nat := [1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 4]
def baseStart_5862537 : Nat := 118140960795 + 5862537 * 2 ^ 59
def prefixEnd_5862537 : Nat := 4983230072969 + 3 ^ 40 * 5862537 * 2
def baseEnd_5862537 : Nat := 3010299335767634530726189

theorem tailTrace_5862537 : CollatzResearch.WordTrace tailWord_5862537 prefixEnd_5862537 3010299335767634530726189 := by
  unfold tailWord_5862537
  simp only [CollatzResearch.WordTrace]
  refine ⟨213824290762037165451793865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142549527174691443634529243 213824290762037165451793865)
  ·
    refine ⟨160368218071527874088845399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213824290762037165451793865 160368218071527874088845399)
    ·
      refine ⟨240552327107291811133268099, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160368218071527874088845399 240552327107291811133268099)
      ·
        refine ⟨360828490660937716699902149, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240552327107291811133268099 360828490660937716699902149)
        ·
          refine ⟨67655341998925821881231653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360828490660937716699902149 67655341998925821881231653)
          ·
            refine ⟨12685376624798591602730935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67655341998925821881231653 12685376624798591602730935)
            ·
              refine ⟨19028064937197887404096403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12685376624798591602730935 19028064937197887404096403)
              ·
                refine ⟨28542097405796831106144605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19028064937197887404096403 28542097405796831106144605)
                ·
                  refine ⟨10703286527173811664804227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28542097405796831106144605 10703286527173811664804227)
                  ·
                    refine ⟨16054929790760717497206341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10703286527173811664804227 16054929790760717497206341)
                    ·
                      refine ⟨3010299335767634530726189, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16054929790760717497206341 3010299335767634530726189)
                      ·
                        rfl

theorem cell23_5862537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 4, 1, 1, 3, 1, 4].length) (baseStart_5862537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862537 prefixEnd_5862537 := by exact prefixLift 5862537
  have htrace : WordTrace (prefixWord ++ tailWord_5862537) baseStart_5862537 baseEnd_5862537 := by
    simpa [prefixWord, tailWord_5862537, baseEnd_5862537] using wordTrace_append hprefix tailTrace_5862537
  have hstable : (prefixWord ++ tailWord_5862537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862537).length < 2 ^ (prefixWord ++ tailWord_5862537).sum := by decide
  have hdescent : baseEnd_5862537 < baseStart_5862537 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862540 : List Nat := [2, 2, 1, 2, 1, 1, 1, 4, 3, 1, 5]
def baseStart_5862540 : Nat := 118140960795 + 5862540 * 2 ^ 59
def prefixEnd_5862540 : Nat := 4983230072969 + 3 ^ 40 * 5862540 * 2
def baseEnd_5862540 : Nat := 3010300876209598018988675

theorem tailTrace_5862540 : CollatzResearch.WordTrace tailWord_5862540 prefixEnd_5862540 3010300876209598018988675 := by
  unfold tailWord_5862540
  simp only [CollatzResearch.WordTrace]
  refine ⟨106912200090513148482076537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142549600120684197976102049 106912200090513148482076537)
  ·
    refine ⟨80184150067884861361557403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106912200090513148482076537 80184150067884861361557403)
    ·
      refine ⟨120276225101827292042336105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80184150067884861361557403 120276225101827292042336105)
      ·
        refine ⟨90207168826370469031752079, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120276225101827292042336105 90207168826370469031752079)
        ·
          refine ⟨135310753239555703547628119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90207168826370469031752079 135310753239555703547628119)
          ·
            refine ⟨202966129859333555321442179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135310753239555703547628119 202966129859333555321442179)
            ·
              refine ⟨304449194789000332982163269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202966129859333555321442179 304449194789000332982163269)
              ·
                refine ⟨57084224022937562434155613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 304449194789000332982163269 57084224022937562434155613)
                ·
                  refine ⟨21406584008601585912808355, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57084224022937562434155613 21406584008601585912808355)
                  ·
                    refine ⟨32109876012902378869212533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21406584008601585912808355 32109876012902378869212533)
                    ·
                      refine ⟨3010300876209598018988675, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32109876012902378869212533 3010300876209598018988675)
                      ·
                        rfl

theorem cell23_5862540_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 1, 4, 3, 1, 5].length) (baseStart_5862540 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862540 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862540 prefixEnd_5862540 := by exact prefixLift 5862540
  have htrace : WordTrace (prefixWord ++ tailWord_5862540) baseStart_5862540 baseEnd_5862540 := by
    simpa [prefixWord, tailWord_5862540, baseEnd_5862540] using wordTrace_append hprefix tailTrace_5862540
  have hstable : (prefixWord ++ tailWord_5862540).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862540).length < 2 ^ (prefixWord ++ tailWord_5862540).sum := by decide
  have hdescent : baseEnd_5862540 < baseStart_5862540 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862540) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862564 : List Nat := [2, 3, 1, 2, 3, 1, 1, 4, 2, 4]
def baseStart_5862564 : Nat := 118140960795 + 5862564 * 2 ^ 59
def prefixEnd_5862564 : Nat := 4983230072969 + 3 ^ 40 * 5862564 * 2
def baseEnd_5862564 : Nat := 1003437733248435308362855

theorem tailTrace_5862564 : CollatzResearch.WordTrace tailWord_5862564 prefixEnd_5862564 1003437733248435308362855 := by
  unfold tailWord_5862564
  simp only [CollatzResearch.WordTrace]
  refine ⟨106912637766469674531513373, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142550183688626232708684497 106912637766469674531513373)
  ·
    refine ⟨40092239162426127949317515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106912637766469674531513373 40092239162426127949317515)
    ·
      refine ⟨60138358743639191923976273, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40092239162426127949317515 60138358743639191923976273)
      ·
        refine ⟨45103769057729393942982205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60138358743639191923976273 45103769057729393942982205)
        ·
          refine ⟨16913913396648522728618327, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45103769057729393942982205 16913913396648522728618327)
          ·
            refine ⟨25370870094972784092927491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16913913396648522728618327 25370870094972784092927491)
            ·
              refine ⟨38056305142459176139391237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25370870094972784092927491 38056305142459176139391237)
              ·
                refine ⟨7135557214211095526135857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38056305142459176139391237 7135557214211095526135857)
                ·
                  refine ⟨5351667910658321644601893, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7135557214211095526135857 5351667910658321644601893)
                  ·
                    refine ⟨1003437733248435308362855, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351667910658321644601893 1003437733248435308362855)
                    ·
                      rfl

theorem cell23_5862564_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 3, 1, 1, 4, 2, 4].length) (baseStart_5862564 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862564 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862564 prefixEnd_5862564 := by exact prefixLift 5862564
  have htrace : WordTrace (prefixWord ++ tailWord_5862564) baseStart_5862564 baseEnd_5862564 := by
    simpa [prefixWord, tailWord_5862564, baseEnd_5862564] using wordTrace_append hprefix tailTrace_5862564
  have hstable : (prefixWord ++ tailWord_5862564).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862564).length < 2 ^ (prefixWord ++ tailWord_5862564).sum := by decide
  have hdescent : baseEnd_5862564 < baseStart_5862564 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862564) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862577 : List Nat := [1, 2, 2, 5, 1, 1, 3, 8]
def baseStart_5862577 : Nat := 118140960795 + 5862577 * 2 ^ 59
def prefixEnd_5862577 : Nat := 4983230072969 + 3 ^ 40 * 5862577 * 2
def baseEnd_5862577 : Nat := 111493328703474606452815

theorem tailTrace_5862577 : CollatzResearch.WordTrace tailWord_5862577 prefixEnd_5862577 111493328703474606452815 := by
  unfold tailWord_5862577
  simp only [CollatzResearch.WordTrace]
  refine ⟨213825749681892252283249985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142550499787928168188833323 213825749681892252283249985)
  ·
    refine ⟨160369312261419189212437489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213825749681892252283249985 160369312261419189212437489)
    ·
      refine ⟨120276984196064391909328117, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160369312261419189212437489 120276984196064391909328117)
      ·
        refine ⟨11275967268381036741499511, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120276984196064391909328117 11275967268381036741499511)
        ·
          refine ⟨16913950902571555112249267, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11275967268381036741499511 16913950902571555112249267)
          ·
            refine ⟨25370926353857332668373901, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16913950902571555112249267 25370926353857332668373901)
            ·
              refine ⟨9514097382696499750640213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25370926353857332668373901 9514097382696499750640213)
              ·
                refine ⟨111493328703474606452815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9514097382696499750640213 111493328703474606452815)
                ·
                  rfl

theorem cell23_5862577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 1, 3, 8].length) (baseStart_5862577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862577 prefixEnd_5862577 := by exact prefixLift 5862577
  have htrace : WordTrace (prefixWord ++ tailWord_5862577) baseStart_5862577 baseEnd_5862577 := by
    simpa [prefixWord, tailWord_5862577, baseEnd_5862577] using wordTrace_append hprefix tailTrace_5862577
  have hstable : (prefixWord ++ tailWord_5862577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862577).length < 2 ^ (prefixWord ++ tailWord_5862577).sum := by decide
  have hdescent : baseEnd_5862577 < baseStart_5862577 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862664 : List Nat := [2, 1, 3, 2, 4, 1, 1, 1, 2, 1, 5]
def baseStart_5862664 : Nat := 118140960795 + 5862664 * 2 ^ 59
def prefixEnd_5862664 : Nat := 4983230072969 + 3 ^ 40 * 5862664 * 2
def baseEnd_5862664 : Nat := 3010364547810755533838105

theorem tailTrace_5862664 : CollatzResearch.WordTrace tailWord_5862664 prefixEnd_5862664 3010364547810755533838105 := by
  unfold tailWord_5862664
  simp only [CollatzResearch.WordTrace]
  refine ⟨106914461416288533070833523, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142552615221718044094444697 106914461416288533070833523)
  ·
    refine ⟨160371692124432799606250285, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106914461416288533070833523 160371692124432799606250285)
    ·
      refine ⟨60139384546662299852343857, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160371692124432799606250285 60139384546662299852343857)
      ·
        refine ⟨45104538409996724889257893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60139384546662299852343857 45104538409996724889257893)
        ·
          refine ⟨8457100951874385916735855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45104538409996724889257893 8457100951874385916735855)
          ·
            refine ⟨12685651427811578875103783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457100951874385916735855 12685651427811578875103783)
            ·
              refine ⟨19028477141717368312655675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12685651427811578875103783 19028477141717368312655675)
              ·
                refine ⟨28542715712576052468983513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19028477141717368312655675 28542715712576052468983513)
                ·
                  refine ⟨21407036784432039351737635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28542715712576052468983513 21407036784432039351737635)
                  ·
                    refine ⟨32110555176648059027606453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21407036784432039351737635 32110555176648059027606453)
                    ·
                      refine ⟨3010364547810755533838105, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32110555176648059027606453 3010364547810755533838105)
                      ·
                        rfl

theorem cell23_5862664_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 4, 1, 1, 1, 2, 1, 5].length) (baseStart_5862664 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862664 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862664 prefixEnd_5862664 := by exact prefixLift 5862664
  have htrace : WordTrace (prefixWord ++ tailWord_5862664) baseStart_5862664 baseEnd_5862664 := by
    simpa [prefixWord, tailWord_5862664, baseEnd_5862664] using wordTrace_append hprefix tailTrace_5862664
  have hstable : (prefixWord ++ tailWord_5862664).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862664).length < 2 ^ (prefixWord ++ tailWord_5862664).sum := by decide
  have hdescent : baseEnd_5862664 < baseStart_5862664 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862664) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862684 : List Nat := [2, 2, 3, 1, 1, 1, 2, 6, 5]
def baseStart_5862684 : Nat := 118140960795 + 5862684 * 2 ^ 59
def prefixEnd_5862684 : Nat := 4983230072969 + 3 ^ 40 * 5862684 * 2
def baseEnd_5862684 : Nat := 334486090824871717287557

theorem tailTrace_5862684 : CollatzResearch.WordTrace tailWord_5862684 prefixEnd_5862684 334486090824871717287557 := by
  unfold tailWord_5862684
  simp only [CollatzResearch.WordTrace]
  refine ⟨106914826146252304778697553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142553101528336406371596737 106914826146252304778697553)
  ·
    refine ⟨80186119609689228584023165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106914826146252304778697553 80186119609689228584023165)
    ·
      refine ⟨30069794853633460719008687, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80186119609689228584023165 30069794853633460719008687)
      ·
        refine ⟨45104692280450191078513031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30069794853633460719008687 45104692280450191078513031)
        ·
          refine ⟨67657038420675286617769547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45104692280450191078513031 67657038420675286617769547)
          ·
            refine ⟨101485557631012929926654321, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67657038420675286617769547 101485557631012929926654321)
            ·
              refine ⟨76114168223259697444990741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101485557631012929926654321 76114168223259697444990741)
              ·
                refine ⟨3567851635465298317733941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76114168223259697444990741 3567851635465298317733941)
                ·
                  refine ⟨334486090824871717287557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3567851635465298317733941 334486090824871717287557)
                  ·
                    rfl

theorem cell23_5862684_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 2, 6, 5].length) (baseStart_5862684 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862684 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862684 prefixEnd_5862684 := by exact prefixLift 5862684
  have htrace : WordTrace (prefixWord ++ tailWord_5862684) baseStart_5862684 baseEnd_5862684 := by
    simpa [prefixWord, tailWord_5862684, baseEnd_5862684] using wordTrace_append hprefix tailTrace_5862684
  have hstable : (prefixWord ++ tailWord_5862684).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862684).length < 2 ^ (prefixWord ++ tailWord_5862684).sum := by decide
  have hdescent : baseEnd_5862684 < baseStart_5862684 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862684) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862714 : List Nat := [3, 1, 1, 1, 4, 1, 4, 1, 2, 5]
def baseStart_5862714 : Nat := 118140960795 + 5862714 * 2 ^ 59
def prefixEnd_5862714 : Nat := 4983230072969 + 3 ^ 40 * 5862714 * 2
def baseEnd_5862714 : Nat := 1003463407281160112737625

theorem tailTrace_5862714 : CollatzResearch.WordTrace tailWord_5862714 prefixEnd_5862714 1003463407281160112737625 := by
  unfold tailWord_5862714
  simp only [CollatzResearch.WordTrace]
  refine ⟨53457686620598981170246799, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142553830988263949787324797 53457686620598981170246799)
  ·
    refine ⟨80186529930898471755370199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53457686620598981170246799 80186529930898471755370199)
    ·
      refine ⟨120279794896347707633055299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80186529930898471755370199 120279794896347707633055299)
      ·
        refine ⟨180419692344521561449582949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120279794896347707633055299 180419692344521561449582949)
        ·
          refine ⟨33828692314597792771796803, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180419692344521561449582949 33828692314597792771796803)
          ·
            refine ⟨50743038471896689157695205, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33828692314597792771796803 50743038471896689157695205)
            ·
              refine ⟨9514319713480629217067851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50743038471896689157695205 9514319713480629217067851)
              ·
                refine ⟨14271479570220943825601777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9514319713480629217067851 14271479570220943825601777)
                ·
                  refine ⟨10703609677665707869201333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14271479570220943825601777 10703609677665707869201333)
                  ·
                    refine ⟨1003463407281160112737625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10703609677665707869201333 1003463407281160112737625)
                    ·
                      rfl

theorem cell23_5862714_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 4, 1, 4, 1, 2, 5].length) (baseStart_5862714 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862714 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862714 prefixEnd_5862714 := by exact prefixLift 5862714
  have htrace : WordTrace (prefixWord ++ tailWord_5862714) baseStart_5862714 baseEnd_5862714 := by
    simpa [prefixWord, tailWord_5862714, baseEnd_5862714] using wordTrace_append hprefix tailTrace_5862714
  have hstable : (prefixWord ++ tailWord_5862714).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862714).length < 2 ^ (prefixWord ++ tailWord_5862714).sum := by decide
  have hdescent : baseEnd_5862714 < baseStart_5862714 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862714) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862734 : List Nat := [4, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4]
def baseStart_5862734 : Nat := 118140960795 + 5862734 * 2 ^ 59
def prefixEnd_5862734 : Nat := 4983230072969 + 3 ^ 40 * 5862734 * 2
def baseEnd_5862734 : Nat := 3010400491456570259962783

theorem tailTrace_5862734 : CollatzResearch.WordTrace tailWord_5862734 prefixEnd_5862734 3010400491456570259962783 := by
  unfold tailWord_5862734
  simp only [CollatzResearch.WordTrace]
  refine ⟨26728934492790433512089407, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142554317294882312064476837 26728934492790433512089407)
  ·
    refine ⟨40093401739185650268134111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26728934492790433512089407 40093401739185650268134111)
    ·
      refine ⟨60140102608778475402201167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40093401739185650268134111 60140102608778475402201167)
      ·
        refine ⟨90210153913167713103301751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60140102608778475402201167 90210153913167713103301751)
        ·
          refine ⟨135315230869751569654952627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90210153913167713103301751 135315230869751569654952627)
          ·
            refine ⟨202972846304627354482428941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135315230869751569654952627 202972846304627354482428941)
            ·
              refine ⟨76114817364235257930910853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 202972846304627354482428941 76114817364235257930910853)
              ·
                refine ⟨14271528255794110862045785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76114817364235257930910853 14271528255794110862045785)
                ·
                  refine ⟨10703646191845583146534339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14271528255794110862045785 10703646191845583146534339)
                  ·
                    refine ⟨16055469287768374719801509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10703646191845583146534339 16055469287768374719801509)
                    ·
                      refine ⟨3010400491456570259962783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16055469287768374719801509 3010400491456570259962783)
                      ·
                        rfl

theorem cell23_5862734_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 1, 3, 4, 2, 1, 4].length) (baseStart_5862734 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862734 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862734 prefixEnd_5862734 := by exact prefixLift 5862734
  have htrace : WordTrace (prefixWord ++ tailWord_5862734) baseStart_5862734 baseEnd_5862734 := by
    simpa [prefixWord, tailWord_5862734, baseEnd_5862734] using wordTrace_append hprefix tailTrace_5862734
  have hstable : (prefixWord ++ tailWord_5862734).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862734).length < 2 ^ (prefixWord ++ tailWord_5862734).sum := by decide
  have hdescent : baseEnd_5862734 < baseStart_5862734 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862734) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862737 : List Nat := [1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 5]
def baseStart_5862737 : Nat := 118140960795 + 5862737 * 2 ^ 59
def prefixEnd_5862737 : Nat := 4983230072969 + 3 ^ 40 * 5862737 * 2
def baseEnd_5862737 : Nat := 3010402031898533748225269

theorem tailTrace_5862737 : CollatzResearch.WordTrace tailWord_5862737 prefixEnd_5862737 3010402031898533748225269 := by
  unfold tailWord_5862737
  simp only [CollatzResearch.WordTrace]
  refine ⟨213831585361312599609074465, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142554390240875066406049643 213831585361312599609074465)
  ·
    refine ⟨160373689020984449706805849, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213831585361312599609074465 160373689020984449706805849)
    ·
      refine ⟨120280266765738337280104387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160373689020984449706805849 120280266765738337280104387)
      ·
        refine ⟨180420400148607505920156581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120280266765738337280104387 180420400148607505920156581)
        ·
          refine ⟨33828825027863907360029359, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 180420400148607505920156581 33828825027863907360029359)
          ·
            refine ⟨50743237541795861040044039, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33828825027863907360029359 50743237541795861040044039)
            ·
              refine ⟨76114856312693791560066059, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50743237541795861040044039 76114856312693791560066059)
              ·
                refine ⟨114172284469040687340099089, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76114856312693791560066059 114172284469040687340099089)
                ·
                  refine ⟨85629213351780515505074317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114172284469040687340099089 85629213351780515505074317)
                  ·
                    refine ⟨32110955006917693314402869, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 85629213351780515505074317 32110955006917693314402869)
                    ·
                      refine ⟨3010402031898533748225269, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32110955006917693314402869 3010402031898533748225269)
                      ·
                        rfl

theorem cell23_5862737_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 4, 1, 1, 1, 2, 3, 5].length) (baseStart_5862737 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862737 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862737 prefixEnd_5862737 := by exact prefixLift 5862737
  have htrace : WordTrace (prefixWord ++ tailWord_5862737) baseStart_5862737 baseEnd_5862737 := by
    simpa [prefixWord, tailWord_5862737, baseEnd_5862737] using wordTrace_append hprefix tailTrace_5862737
  have hstable : (prefixWord ++ tailWord_5862737).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862737).length < 2 ^ (prefixWord ++ tailWord_5862737).sum := by decide
  have hdescent : baseEnd_5862737 < baseStart_5862737 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862737) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862744 : List Nat := [2, 1, 2, 2, 1, 1, 4, 3, 3, 4]
def baseStart_5862744 : Nat := 118140960795 + 5862744 * 2 ^ 59
def prefixEnd_5862744 : Nat := 4983230072969 + 3 ^ 40 * 5862744 * 2
def baseEnd_5862744 : Nat := 1003468542087705073612579

theorem tailTrace_5862744 : CollatzResearch.WordTrace tailWord_5862744 prefixEnd_5862744 1003468542087705073612579 := by
  unfold tailWord_5862744
  simp only [CollatzResearch.WordTrace]
  refine ⟨106915920336143619902289643, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142554560448191493203052857 106915920336143619902289643)
  ·
    refine ⟨160373880504215429853434465, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106915920336143619902289643 160373880504215429853434465)
    ·
      refine ⟨120280410378161572390075849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160373880504215429853434465 120280410378161572390075849)
      ·
        refine ⟨90210307783621179292556887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120280410378161572390075849 90210307783621179292556887)
        ·
          refine ⟨135315461675431768938835331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90210307783621179292556887 135315461675431768938835331)
          ·
            refine ⟨202973192513147653408252997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135315461675431768938835331 202973192513147653408252997)
            ·
              refine ⟨38057473596215185014047437, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 202973192513147653408252997 38057473596215185014047437)
              ·
                refine ⟨14271552598580694380267789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38057473596215185014047437 14271552598580694380267789)
                ·
                  refine ⟨5351832224467760392600421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14271552598580694380267789 5351832224467760392600421)
                  ·
                    refine ⟨1003468542087705073612579, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5351832224467760392600421 1003468542087705073612579)
                    ·
                      rfl

theorem cell23_5862744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 4, 3, 3, 4].length) (baseStart_5862744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862744 prefixEnd_5862744 := by exact prefixLift 5862744
  have htrace : WordTrace (prefixWord ++ tailWord_5862744) baseStart_5862744 baseEnd_5862744 := by
    simpa [prefixWord, tailWord_5862744, baseEnd_5862744] using wordTrace_append hprefix tailTrace_5862744
  have hstable : (prefixWord ++ tailWord_5862744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862744).length < 2 ^ (prefixWord ++ tailWord_5862744).sum := by decide
  have hdescent : baseEnd_5862744 < baseStart_5862744 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862791 : List Nat := [1, 1, 4, 2, 2, 4, 1, 2, 6]
def baseStart_5862791 : Nat := 118140960795 + 5862791 * 2 ^ 59
def prefixEnd_5862791 : Nat := 4983230072969 + 3 ^ 40 * 5862791 * 2
def baseEnd_5862791 : Nat := 334492195539319615216669

theorem tailTrace_5862791 : CollatzResearch.WordTrace tailWord_5862791 prefixEnd_5862791 334492195539319615216669 := by
  unfold tailWord_5862791
  simp only [CollatzResearch.WordTrace]
  refine ⟨213833554903116966831540227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142555703268744644554360151 213833554903116966831540227)
  ·
    refine ⟨320750332354675450247310341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213833554903116966831540227 320750332354675450247310341)
    ·
      refine ⟨60140687316501646921370689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320750332354675450247310341 60140687316501646921370689)
      ·
        refine ⟨45105515487376235191028017, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60140687316501646921370689 45105515487376235191028017)
        ·
          refine ⟨33829136615532176393271013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45105515487376235191028017 33829136615532176393271013)
          ·
            refine ⟨6342963115412283073738315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33829136615532176393271013 6342963115412283073738315)
            ·
              refine ⟨9514444673118424610607473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6342963115412283073738315 9514444673118424610607473)
              ·
                refine ⟨7135833504838818457955605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9514444673118424610607473 7135833504838818457955605)
                ·
                  refine ⟨334492195539319615216669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7135833504838818457955605 334492195539319615216669)
                  ·
                    rfl

theorem cell23_5862791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 4, 1, 2, 6].length) (baseStart_5862791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862791 prefixEnd_5862791 := by exact prefixLift 5862791
  have htrace : WordTrace (prefixWord ++ tailWord_5862791) baseStart_5862791 baseEnd_5862791 := by
    simpa [prefixWord, tailWord_5862791, baseEnd_5862791] using wordTrace_append hprefix tailTrace_5862791
  have hstable : (prefixWord ++ tailWord_5862791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862791).length < 2 ^ (prefixWord ++ tailWord_5862791).sum := by decide
  have hdescent : baseEnd_5862791 < baseStart_5862791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862808 : List Nat := [2, 1, 2, 5, 2, 1, 3, 1, 6]
def baseStart_5862808 : Nat := 118140960795 + 5862808 * 2 ^ 59
def prefixEnd_5862808 : Nat := 4983230072969 + 3 ^ 40 * 5862808 * 2
def baseEnd_5862808 : Nat := 334493165447222552270827

theorem tailTrace_5862808 : CollatzResearch.WordTrace tailWord_5862808 prefixEnd_5862808 334493165447222552270827 := by
  unfold tailWord_5862808
  simp only [CollatzResearch.WordTrace]
  refine ⟨106917087472027689367454539, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142556116629370252489939385 106917087472027689367454539)
  ·
    refine ⟨160375631208041534051181809, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106917087472027689367454539 160375631208041534051181809)
    ·
      refine ⟨120281723406031150538386357, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160375631208041534051181809 120281723406031150538386357)
      ·
        refine ⟨11276411569315420362973721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120281723406031150538386357 11276411569315420362973721)
        ·
          refine ⟨8457308676986565272230291, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11276411569315420362973721 8457308676986565272230291)
          ·
            refine ⟨12685963015479847908345437, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457308676986565272230291 12685963015479847908345437)
            ·
              refine ⟨4757236130804942965629539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12685963015479847908345437 4757236130804942965629539)
              ·
                refine ⟨7135854196207414448444309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757236130804942965629539 7135854196207414448444309)
                ·
                  refine ⟨334493165447222552270827, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7135854196207414448444309 334493165447222552270827)
                  ·
                    rfl

theorem cell23_5862808_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 5, 2, 1, 3, 1, 6].length) (baseStart_5862808 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862808 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862808 prefixEnd_5862808 := by exact prefixLift 5862808
  have htrace : WordTrace (prefixWord ++ tailWord_5862808) baseStart_5862808 baseEnd_5862808 := by
    simpa [prefixWord, tailWord_5862808, baseEnd_5862808] using wordTrace_append hprefix tailTrace_5862808
  have hstable : (prefixWord ++ tailWord_5862808).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862808).length < 2 ^ (prefixWord ++ tailWord_5862808).sum := by decide
  have hdescent : baseEnd_5862808 < baseStart_5862808 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862808) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862818 : List Nat := [3, 3, 1, 2, 1, 2, 2, 2, 3, 1, 3]
def baseStart_5862818 : Nat := 118140960795 + 5862818 * 2 ^ 59
def prefixEnd_5862818 : Nat := 4983230072969 + 3 ^ 40 * 5862818 * 2
def baseEnd_5862818 : Nat := 3010443623831547931312397

theorem tailTrace_5862818 : CollatzResearch.WordTrace tailWord_5862818 prefixEnd_5862818 3010443623831547931312397 := by
  unfold tailWord_5862818
  simp only [CollatzResearch.WordTrace]
  refine ⟨53458634918504787610693277, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142556359782679433628515405 53458634918504787610693277)
  ·
    refine ⟨20046988094439295354009979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53458634918504787610693277 20046988094439295354009979)
    ·
      refine ⟨30070482141658943031014969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20046988094439295354009979 30070482141658943031014969)
      ·
        refine ⟨22552861606244207273261227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30070482141658943031014969 22552861606244207273261227)
        ·
          refine ⟨33829292409366310909891841, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22552861606244207273261227 33829292409366310909891841)
          ·
            refine ⟨25371969307024733182418881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33829292409366310909891841 25371969307024733182418881)
            ·
              refine ⟨19028976980268549886814161, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25371969307024733182418881 19028976980268549886814161)
              ·
                refine ⟨14271732735201412415110621, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19028976980268549886814161 14271732735201412415110621)
                ·
                  refine ⟨5351899775700529655666483, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14271732735201412415110621 5351899775700529655666483)
                  ·
                    refine ⟨8027849663550794483499725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5351899775700529655666483 8027849663550794483499725)
                    ·
                      refine ⟨3010443623831547931312397, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8027849663550794483499725 3010443623831547931312397)
                      ·
                        rfl

theorem cell23_5862818_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 1, 2, 2, 2, 3, 1, 3].length) (baseStart_5862818 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862818 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862818 prefixEnd_5862818 := by exact prefixLift 5862818
  have htrace : WordTrace (prefixWord ++ tailWord_5862818) baseStart_5862818 baseEnd_5862818 := by
    simpa [prefixWord, tailWord_5862818, baseEnd_5862818] using wordTrace_append hprefix tailTrace_5862818
  have hstable : (prefixWord ++ tailWord_5862818).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862818).length < 2 ^ (prefixWord ++ tailWord_5862818).sum := by decide
  have hdescent : baseEnd_5862818 < baseStart_5862818 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862818) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862891 : List Nat := [1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 3]
def baseStart_5862891 : Nat := 118140960795 + 5862891 * 2 ^ 59
def prefixEnd_5862891 : Nat := 4983230072969 + 3 ^ 40 * 5862891 * 2
def baseEnd_5862891 : Nat := 3010481107919326145699561

theorem tailTrace_5862891 : CollatzResearch.WordTrace tailWord_5862891 prefixEnd_5862891 3010481107919326145699561 := by
  unfold tailWord_5862891
  simp only [CollatzResearch.WordTrace]
  refine ⟨213837202202754683910180527, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142558134801836455940120351 213837202202754683910180527)
  ·
    refine ⟨320755803304132025865270791, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213837202202754683910180527 320755803304132025865270791)
    ·
      refine ⟨481133704956198038797906187, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320755803304132025865270791 481133704956198038797906187)
      ·
        refine ⟨721700557434297058196859281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481133704956198038797906187 721700557434297058196859281)
        ·
          refine ⟨541275418075722793647644461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 721700557434297058196859281 541275418075722793647644461)
          ·
            refine ⟨202978281778396047617866673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541275418075722793647644461 202978281778396047617866673)
            ·
              refine ⟨152233711333797035713400005, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 202978281778396047617866673 152233711333797035713400005)
              ·
                refine ⟨28543820875086944196262501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152233711333797035713400005 28543820875086944196262501)
                ·
                  refine ⟨5351966414078802036799219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28543820875086944196262501 5351966414078802036799219)
                  ·
                    refine ⟨8027949621118203055198829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5351966414078802036799219 8027949621118203055198829)
                    ·
                      refine ⟨3010481107919326145699561, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8027949621118203055198829 3010481107919326145699561)
                      ·
                        rfl

theorem cell23_5862891_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 3, 2, 4, 4, 1, 3].length) (baseStart_5862891 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862891 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862891 prefixEnd_5862891 := by exact prefixLift 5862891
  have htrace : WordTrace (prefixWord ++ tailWord_5862891) baseStart_5862891 baseEnd_5862891 := by
    simpa [prefixWord, tailWord_5862891, baseEnd_5862891] using wordTrace_append hprefix tailTrace_5862891
  have hstable : (prefixWord ++ tailWord_5862891).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862891).length < 2 ^ (prefixWord ++ tailWord_5862891).sum := by decide
  have hdescent : baseEnd_5862891 < baseStart_5862891 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862891) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862908 : List Nat := [2, 2, 2, 1, 2, 1, 3, 4, 2, 1, 3]
def baseStart_5862908 : Nat := 118140960795 + 5862908 * 2 ^ 59
def prefixEnd_5862908 : Nat := 4983230072969 + 3 ^ 40 * 5862908 * 2
def baseEnd_5862908 : Nat := 3010489837090452579186983

theorem tailTrace_5862908 : CollatzResearch.WordTrace tailWord_5862908 prefixEnd_5862908 3010489837090452579186983 := by
  unfold tailWord_5862908
  simp only [CollatzResearch.WordTrace]
  refine ⟨106918911121846547906774689, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142558548162462063875699585 106918911121846547906774689)
  ·
    refine ⟨80189183341384910930081017, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106918911121846547906774689 80189183341384910930081017)
    ·
      refine ⟨60141887506038683197560763, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80189183341384910930081017 60141887506038683197560763)
      ·
        refine ⟨90212831259058024796341145, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60141887506038683197560763 90212831259058024796341145)
        ·
          refine ⟨67659623444293518597255859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90212831259058024796341145 67659623444293518597255859)
          ·
            refine ⟨101489435166440277895883789, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67659623444293518597255859 101489435166440277895883789)
            ·
              refine ⟨38058538187415104210956421, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101489435166440277895883789 38058538187415104210956421)
              ·
                refine ⟨7135975910140332039554329, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38058538187415104210956421 7135975910140332039554329)
                ·
                  refine ⟨5351981932605249029665747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7135975910140332039554329 5351981932605249029665747)
                  ·
                    refine ⟨8027972898907873544498621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5351981932605249029665747 8027972898907873544498621)
                    ·
                      refine ⟨3010489837090452579186983, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8027972898907873544498621 3010489837090452579186983)
                      ·
                        rfl

theorem cell23_5862908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 2, 1, 3, 4, 2, 1, 3].length) (baseStart_5862908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862908 prefixEnd_5862908 := by exact prefixLift 5862908
  have htrace : WordTrace (prefixWord ++ tailWord_5862908) baseStart_5862908 baseEnd_5862908 := by
    simpa [prefixWord, tailWord_5862908, baseEnd_5862908] using wordTrace_append hprefix tailTrace_5862908
  have hstable : (prefixWord ++ tailWord_5862908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862908).length < 2 ^ (prefixWord ++ tailWord_5862908).sum := by decide
  have hdescent : baseEnd_5862908 < baseStart_5862908 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862909 : List Nat := [1, 4, 1, 1, 1, 6, 2, 2, 1, 2, 2]
def baseStart_5862909 : Nat := 118140960795 + 5862909 * 2 ^ 59
def prefixEnd_5862909 : Nat := 4983230072969 + 3 ^ 40 * 5862909 * 2
def baseEnd_5862909 : Nat := 3010490350571107075274479

theorem tailTrace_5862909 : CollatzResearch.WordTrace tailWord_5862909 prefixEnd_5862909 3010490350571107075274479 := by
  unfold tailWord_5862909
  simp only [CollatzResearch.WordTrace]
  refine ⟨213837858716689472984335781, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142558572477792981989557187 213837858716689472984335781)
  ·
    refine ⟨40094598509379276184562959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213837858716689472984335781 40094598509379276184562959)
    ·
      refine ⟨60141897764068914276844439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40094598509379276184562959 60141897764068914276844439)
      ·
        refine ⟨90212846646103371415266659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60141897764068914276844439 90212846646103371415266659)
        ·
          refine ⟨135319269969155057122899989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90212846646103371415266659 135319269969155057122899989)
          ·
            refine ⟨6343090779804143302635937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135319269969155057122899989 6343090779804143302635937)
            ·
              refine ⟨4757318084853107476976953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6343090779804143302635937 4757318084853107476976953)
              ·
                refine ⟨3567988563639830607732715, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4757318084853107476976953 3567988563639830607732715)
                ·
                  refine ⟨5351982845459745911599073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3567988563639830607732715 5351982845459745911599073)
                  ·
                    refine ⟨4013987134094809433699305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5351982845459745911599073 4013987134094809433699305)
                    ·
                      refine ⟨3010490350571107075274479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4013987134094809433699305 3010490350571107075274479)
                      ·
                        rfl

theorem cell23_5862909_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 6, 2, 2, 1, 2, 2].length) (baseStart_5862909 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862909 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862909 prefixEnd_5862909 := by exact prefixLift 5862909
  have htrace : WordTrace (prefixWord ++ tailWord_5862909) baseStart_5862909 baseEnd_5862909 := by
    simpa [prefixWord, tailWord_5862909, baseEnd_5862909] using wordTrace_append hprefix tailTrace_5862909
  have hstable : (prefixWord ++ tailWord_5862909).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862909).length < 2 ^ (prefixWord ++ tailWord_5862909).sum := by decide
  have hdescent : baseEnd_5862909 < baseStart_5862909 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862909) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862952 : List Nat := [2, 1, 5, 2, 2, 1, 1, 3, 1, 3, 2]
def baseStart_5862952 : Nat := 118140960795 + 5862952 * 2 ^ 59
def prefixEnd_5862952 : Nat := 4983230072969 + 3 ^ 40 * 5862952 * 2
def baseEnd_5862952 : Nat := 3010512430239250407036781

theorem tailTrace_5862952 : CollatzResearch.WordTrace tailWord_5862952 prefixEnd_5862952 3010512430239250407036781 := by
  unfold tailWord_5862952
  simp only [CollatzResearch.WordTrace]
  refine ⟨106919713527766845664075555, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142559618037022460885434073 106919713527766845664075555)
  ·
    refine ⟨160379570291650268496113333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106919713527766845664075555 160379570291650268496113333)
    ·
      refine ⟨15035584714842212671510625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160379570291650268496113333 15035584714842212671510625)
      ·
        refine ⟨11276688536131659503632969, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15035584714842212671510625 11276688536131659503632969)
        ·
          refine ⟨8457516402098744627724727, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11276688536131659503632969 8457516402098744627724727)
          ·
            refine ⟨12686274603148116941587091, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457516402098744627724727 12686274603148116941587091)
            ·
              refine ⟨19029411904722175412380637, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686274603148116941587091 19029411904722175412380637)
              ·
                refine ⟨7136029464270815779642739, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19029411904722175412380637 7136029464270815779642739)
                ·
                  refine ⟨10704044196406223669464109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7136029464270815779642739 10704044196406223669464109)
                  ·
                    refine ⟨4014016573652333876049041, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10704044196406223669464109 4014016573652333876049041)
                    ·
                      refine ⟨3010512430239250407036781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014016573652333876049041 3010512430239250407036781)
                      ·
                        rfl

theorem cell23_5862952_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 2, 1, 1, 3, 1, 3, 2].length) (baseStart_5862952 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862952 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862952 prefixEnd_5862952 := by exact prefixLift 5862952
  have htrace : WordTrace (prefixWord ++ tailWord_5862952) baseStart_5862952 baseEnd_5862952 := by
    simpa [prefixWord, tailWord_5862952, baseEnd_5862952] using wordTrace_append hprefix tailTrace_5862952
  have hstable : (prefixWord ++ tailWord_5862952).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862952).length < 2 ^ (prefixWord ++ tailWord_5862952).sum := by decide
  have hdescent : baseEnd_5862952 < baseStart_5862952 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862952) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862965 : List Nat := [1, 3, 3, 1, 1, 4, 1, 1, 4, 2, 2]
def baseStart_5862965 : Nat := 118140960795 + 5862965 * 2 ^ 59
def prefixEnd_5862965 : Nat := 4983230072969 + 3 ^ 40 * 5862965 * 2
def baseEnd_5862965 : Nat := 3010519105487758856174221

theorem tailTrace_5862965 : CollatzResearch.WordTrace tailWord_5862965 prefixEnd_5862965 3010519105487758856174221 := by
  unfold tailWord_5862965
  simp only [CollatzResearch.WordTrace]
  refine ⟨213839901204486594548374349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142559934136324396365582899 213839901204486594548374349)
  ·
    refine ⟨80189962951682472955640381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213839901204486594548374349 80189962951682472955640381)
    ·
      refine ⟨30071236106880927358365143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80189962951682472955640381 30071236106880927358365143)
      ·
        refine ⟨45106854160321391037547715, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30071236106880927358365143 45106854160321391037547715)
        ·
          refine ⟨67660281240482086556321573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45106854160321391037547715 67660281240482086556321573)
          ·
            refine ⟨12686302732590391229310295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67660281240482086556321573 12686302732590391229310295)
            ·
              refine ⟨19029454098885586843965443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686302732590391229310295 19029454098885586843965443)
              ·
                refine ⟨28544181148328380265948165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19029454098885586843965443 28544181148328380265948165)
                ·
                  refine ⟨5352033965311571299865281, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28544181148328380265948165 5352033965311571299865281)
                  ·
                    refine ⟨4014025473983678474898961, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352033965311571299865281 4014025473983678474898961)
                    ·
                      refine ⟨3010519105487758856174221, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014025473983678474898961 3010519105487758856174221)
                      ·
                        rfl

theorem cell23_5862965_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 1, 1, 4, 1, 1, 4, 2, 2].length) (baseStart_5862965 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862965 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862965 prefixEnd_5862965 := by exact prefixLift 5862965
  have htrace : WordTrace (prefixWord ++ tailWord_5862965) baseStart_5862965 baseEnd_5862965 := by
    simpa [prefixWord, tailWord_5862965, baseEnd_5862965] using wordTrace_append hprefix tailTrace_5862965
  have hstable : (prefixWord ++ tailWord_5862965).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862965).length < 2 ^ (prefixWord ++ tailWord_5862965).sum := by decide
  have hdescent : baseEnd_5862965 < baseStart_5862965 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862965) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5862981 : List Nat := [1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 3]
def baseStart_5862981 : Nat := 118140960795 + 5862981 * 2 ^ 59
def prefixEnd_5862981 : Nat := 4983230072969 + 3 ^ 40 * 5862981 * 2
def baseEnd_5862981 : Nat := 3010527321178230793574147

theorem tailTrace_5862981 : CollatzResearch.WordTrace tailWord_5862981 prefixEnd_5862981 3010527321178230793574147 := by
  unfold tailWord_5862981
  simp only [CollatzResearch.WordTrace]
  refine ⟨213840484772428629280956797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142560323181619086187304531 213840484772428629280956797)
  ·
    refine ⟨80190181789660735980358799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213840484772428629280956797 80190181789660735980358799)
    ·
      refine ⟨120285272684491103970538199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80190181789660735980358799 120285272684491103970538199)
      ·
        refine ⟨180427909026736655955807299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120285272684491103970538199 180427909026736655955807299)
        ·
          refine ⟨270641863540104983933710949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180427909026736655955807299 270641863540104983933710949)
          ·
            refine ⟨50745349413769684487570803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270641863540104983933710949 50745349413769684487570803)
            ·
              refine ⟨76118024120654526731356205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50745349413769684487570803 76118024120654526731356205)
              ·
                refine ⟨28544259045245447524258577, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76118024120654526731356205 28544259045245447524258577)
                ·
                  refine ⟨21408194283934085643193933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28544259045245447524258577 21408194283934085643193933)
                  ·
                    refine ⟨8028072856475282116197725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21408194283934085643193933 8028072856475282116197725)
                    ·
                      refine ⟨3010527321178230793574147, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8028072856475282116197725 3010527321178230793574147)
                      ·
                        rfl

theorem cell23_5862981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 4, 1, 3, 2, 3, 3].length) (baseStart_5862981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5862981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5862981 prefixEnd_5862981 := by exact prefixLift 5862981
  have htrace : WordTrace (prefixWord ++ tailWord_5862981) baseStart_5862981 baseEnd_5862981 := by
    simpa [prefixWord, tailWord_5862981, baseEnd_5862981] using wordTrace_append hprefix tailTrace_5862981
  have hstable : (prefixWord ++ tailWord_5862981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5862981).length < 2 ^ (prefixWord ++ tailWord_5862981).sum := by decide
  have hdescent : baseEnd_5862981 < baseStart_5862981 := by decide
  rcases family_descends (prefixWord ++ tailWord_5862981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863018 : List Nat := [3, 1, 3, 2, 1, 3, 1, 2, 2, 5]
def baseStart_5863018 : Nat := 118140960795 + 5863018 * 2 ^ 59
def prefixEnd_5863018 : Nat := 4983230072969 + 3 ^ 40 * 5863018 * 2
def baseEnd_5863018 : Nat := 1003515439987482382937159

theorem tailTrace_5863018 : CollatzResearch.WordTrace tailWord_5863018 prefixEnd_5863018 1003515439987482382937159 := by
  unfold tailWord_5863018
  simp only [CollatzResearch.WordTrace]
  refine ⟨53460458568323646150013427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142561222848863056400035805 53460458568323646150013427)
  ·
    refine ⟨80190687852485469225020141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53460458568323646150013427 80190687852485469225020141)
    ·
      refine ⟨30071507944682050959382553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80190687852485469225020141 30071507944682050959382553)
      ·
        refine ⟨22553630958511538219536915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30071507944682050959382553 22553630958511538219536915)
        ·
          refine ⟨33830446437767307329305373, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22553630958511538219536915 33830446437767307329305373)
          ·
            refine ⟨12686417414162740248489515, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33830446437767307329305373 12686417414162740248489515)
            ·
              refine ⟨19029626121244110372734273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686417414162740248489515 19029626121244110372734273)
              ·
                refine ⟨14272219590933082779550705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19029626121244110372734273 14272219590933082779550705)
                ·
                  refine ⟨10704164693199812084663029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14272219590933082779550705 10704164693199812084663029)
                  ·
                    refine ⟨1003515439987482382937159, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10704164693199812084663029 1003515439987482382937159)
                    ·
                      rfl

theorem cell23_5863018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 2, 2, 5].length) (baseStart_5863018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863018 prefixEnd_5863018 := by exact prefixLift 5863018
  have htrace : WordTrace (prefixWord ++ tailWord_5863018) baseStart_5863018 baseEnd_5863018 := by
    simpa [prefixWord, tailWord_5863018, baseEnd_5863018] using wordTrace_append hprefix tailTrace_5863018
  have hstable : (prefixWord ++ tailWord_5863018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863018).length < 2 ^ (prefixWord ++ tailWord_5863018).sum := by decide
  have hdescent : baseEnd_5863018 < baseStart_5863018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863022 : List Nat := [4, 1, 2, 2, 3, 1, 3, 2, 5]
def baseStart_5863022 : Nat := 118140960795 + 5863022 * 2 ^ 59
def prefixEnd_5863022 : Nat := 4983230072969 + 3 ^ 40 * 5863022 * 2
def baseEnd_5863022 : Nat := 334505374876118348129051

theorem tailTrace_5863022 : CollatzResearch.WordTrace tailWord_5863022 prefixEnd_5863022 334505374876118348129051 := by
  unfold tailWord_5863022
  simp only [CollatzResearch.WordTrace]
  refine ⟨26730247520660011660399915, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142561320110186728855466213 26730247520660011660399915)
  ·
    refine ⟨40095371280990017490599873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26730247520660011660399915 40095371280990017490599873)
    ·
      refine ⟨30071528460742513117949905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40095371280990017490599873 30071528460742513117949905)
      ·
        refine ⟨22553646345556884838462429, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30071528460742513117949905 22553646345556884838462429)
        ·
          refine ⟨8457617379583831814423411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22553646345556884838462429 8457617379583831814423411)
          ·
            refine ⟨12686426069375747721635117, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8457617379583831814423411 12686426069375747721635117)
            ·
              refine ⟨4757409776015905395613169, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12686426069375747721635117 4757409776015905395613169)
              ·
                refine ⟨3568057332011929046709877, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4757409776015905395613169 3568057332011929046709877)
                ·
                  refine ⟨334505374876118348129051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3568057332011929046709877 334505374876118348129051)
                  ·
                    rfl

theorem cell23_5863022_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 3, 2, 5].length) (baseStart_5863022 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863022 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863022 prefixEnd_5863022 := by exact prefixLift 5863022
  have htrace : WordTrace (prefixWord ++ tailWord_5863022) baseStart_5863022 baseEnd_5863022 := by
    simpa [prefixWord, tailWord_5863022, baseEnd_5863022] using wordTrace_append hprefix tailTrace_5863022
  have hstable : (prefixWord ++ tailWord_5863022).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863022).length < 2 ^ (prefixWord ++ tailWord_5863022).sum := by decide
  have hdescent : baseEnd_5863022 < baseStart_5863022 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863022) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863091 : List Nat := [1, 1, 1, 2, 3, 3, 1, 1, 5, 5]
def baseStart_5863091 : Nat := 118140960795 + 5863091 * 2 ^ 59
def prefixEnd_5863091 : Nat := 4983230072969 + 3 ^ 40 * 5863091 * 2
def baseEnd_5863091 : Nat := 1003527934683408454399547

theorem tailTrace_5863091 : CollatzResearch.WordTrace tailWord_5863091 prefixEnd_5863091 1003527934683408454399547 := by
  unfold tailWord_5863091
  simp only [CollatzResearch.WordTrace]
  refine ⟨213844496802030118067461127, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142562997868020078711640751 213844496802030118067461127)
  ·
    refine ⟨320766745203045177101191691, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213844496802030118067461127 320766745203045177101191691)
    ·
      refine ⟨481150117804567765651787537, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320766745203045177101191691 481150117804567765651787537)
      ·
        refine ⟨360862588353425824238840653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481150117804567765651787537 360862588353425824238840653)
        ·
          refine ⟨135323470632534684089565245, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360862588353425824238840653 135323470632534684089565245)
          ·
            refine ⟨50746301487200506533586967, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135323470632534684089565245 50746301487200506533586967)
            ·
              refine ⟨76119452230800759800380451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50746301487200506533586967 76119452230800759800380451)
              ·
                refine ⟨114179178346201139700570677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76119452230800759800380451 114179178346201139700570677)
                ·
                  refine ⟨10704297969956356846928501, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114179178346201139700570677 10704297969956356846928501)
                  ·
                    refine ⟨1003527934683408454399547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10704297969956356846928501 1003527934683408454399547)
                    ·
                      rfl

theorem cell23_5863091_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 3, 1, 1, 5, 5].length) (baseStart_5863091 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863091 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863091 prefixEnd_5863091 := by exact prefixLift 5863091
  have htrace : WordTrace (prefixWord ++ tailWord_5863091) baseStart_5863091 baseEnd_5863091 := by
    simpa [prefixWord, tailWord_5863091, baseEnd_5863091] using wordTrace_append hprefix tailTrace_5863091
  have hstable : (prefixWord ++ tailWord_5863091).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863091).length < 2 ^ (prefixWord ++ tailWord_5863091).sum := by decide
  have hdescent : baseEnd_5863091 < baseStart_5863091 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863091) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863101 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 7]
def baseStart_5863101 : Nat := 118140960795 + 5863101 * 2 ^ 59
def prefixEnd_5863101 : Nat := 4983230072969 + 3 ^ 40 * 5863101 * 2
def baseEnd_5863101 : Nat := 3010588938856770324073595

theorem tailTrace_5863101 : CollatzResearch.WordTrace tailWord_5863101 prefixEnd_5863101 3010588938856770324073595 := by
  unfold tailWord_5863101
  simp only [CollatzResearch.WordTrace]
  refine ⟨213844861531993889775325157, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142563241021329259850216771 213844861531993889775325157)
  ·
    refine ⟨40095911537248854332873467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213844861531993889775325157 40095911537248854332873467)
    ·
      refine ⟨60143867305873281499310201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40095911537248854332873467 60143867305873281499310201)
      ·
        refine ⟨45107900479404961124482651, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60143867305873281499310201 45107900479404961124482651)
        ·
          refine ⟨67661850719107441686723977, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45107900479404961124482651 67661850719107441686723977)
          ·
            refine ⟨50746388039330581265042983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67661850719107441686723977 50746388039330581265042983)
            ·
              refine ⟨76119582058995871897564475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50746388039330581265042983 76119582058995871897564475)
              ·
                refine ⟨114179373088493807846346713, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76119582058995871897564475 114179373088493807846346713)
                ·
                  refine ⟨85634529816370355884760035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114179373088493807846346713 85634529816370355884760035)
                  ·
                    refine ⟨128451794724555533827140053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85634529816370355884760035 128451794724555533827140053)
                    ·
                      refine ⟨3010588938856770324073595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128451794724555533827140053 3010588938856770324073595)
                      ·
                        rfl

theorem cell23_5863101_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 2, 1, 7].length) (baseStart_5863101 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863101 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863101 prefixEnd_5863101 := by exact prefixLift 5863101
  have htrace : WordTrace (prefixWord ++ tailWord_5863101) baseStart_5863101 baseEnd_5863101 := by
    simpa [prefixWord, tailWord_5863101, baseEnd_5863101] using wordTrace_append hprefix tailTrace_5863101
  have hstable : (prefixWord ++ tailWord_5863101).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863101).length < 2 ^ (prefixWord ++ tailWord_5863101).sum := by decide
  have hdescent : baseEnd_5863101 < baseStart_5863101 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863101) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863106 : List Nat := [3, 5, 1, 2, 1, 2, 1, 1, 2, 1, 4]
def baseStart_5863106 : Nat := 118140960795 + 5863106 * 2 ^ 59
def prefixEnd_5863106 : Nat := 4983230072969 + 3 ^ 40 * 5863106 * 2
def baseEnd_5863106 : Nat := 3010591506260042804511073

theorem tailTrace_5863106 : CollatzResearch.WordTrace tailWord_5863106 prefixEnd_5863106 3010591506260042804511073 := by
  unfold tailWord_5863106
  simp only [CollatzResearch.WordTrace]
  refine ⟨53461260974243943907314293, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142563362597983850419504781 53461260974243943907314293)
  ·
    refine ⟨5011993216335369741310715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53461260974243943907314293 5011993216335369741310715)
    ·
      refine ⟨7517989824503054611966073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5011993216335369741310715 7517989824503054611966073)
      ·
        refine ⟨5638492368377290958974555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7517989824503054611966073 5638492368377290958974555)
        ·
          refine ⟨8457738552565936438461833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5638492368377290958974555 8457738552565936438461833)
          ·
            refine ⟨6343303914424452328846375, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8457738552565936438461833 6343303914424452328846375)
            ·
              refine ⟨9514955871636678493269563, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343303914424452328846375 9514955871636678493269563)
              ·
                refine ⟨14272433807455017739904345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9514955871636678493269563 14272433807455017739904345)
                ·
                  refine ⟨10704325355591263304928259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14272433807455017739904345 10704325355591263304928259)
                  ·
                    refine ⟨16056488033386894957392389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10704325355591263304928259 16056488033386894957392389)
                    ·
                      refine ⟨3010591506260042804511073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16056488033386894957392389 3010591506260042804511073)
                      ·
                        rfl

theorem cell23_5863106_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 2, 1, 2, 1, 1, 2, 1, 4].length) (baseStart_5863106 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863106 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863106 prefixEnd_5863106 := by exact prefixLift 5863106
  have htrace : WordTrace (prefixWord ++ tailWord_5863106) baseStart_5863106 baseEnd_5863106 := by
    simpa [prefixWord, tailWord_5863106, baseEnd_5863106] using wordTrace_append hprefix tailTrace_5863106
  have hstable : (prefixWord ++ tailWord_5863106).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863106).length < 2 ^ (prefixWord ++ tailWord_5863106).sum := by decide
  have hdescent : baseEnd_5863106 < baseStart_5863106 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863106) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863108 : List Nat := [2, 3, 3, 1, 1, 1, 1, 3, 3, 5]
def baseStart_5863108 : Nat := 118140960795 + 5863108 * 2 ^ 59
def prefixEnd_5863108 : Nat := 4983230072969 + 3 ^ 40 * 5863108 * 2
def baseEnd_5863108 : Nat := 1003530844407117265562021

theorem tailTrace_5863108 : CollatzResearch.WordTrace tailWord_5863108 prefixEnd_5863108 1003530844407117265562021 := by
  unfold tailWord_5863108
  simp only [CollatzResearch.WordTrace]
  refine ⟨106922558421484264985414989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142563411228645686647219985 106922558421484264985414989)
  ·
    refine ⟨40095959408056599369530621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106922558421484264985414989 40095959408056599369530621)
    ·
      refine ⟨15035984778021224763573983, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 40095959408056599369530621 15035984778021224763573983)
      ·
        refine ⟨22553977167031837145360975, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15035984778021224763573983 22553977167031837145360975)
        ·
          refine ⟨33830965750547755718041463, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22553977167031837145360975 33830965750547755718041463)
          ·
            refine ⟨50746448625821633577062195, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33830965750547755718041463 50746448625821633577062195)
            ·
              refine ⟨76119672938732450365593293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50746448625821633577062195 76119672938732450365593293)
              ·
                refine ⟨28544877352024668887097485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76119672938732450365593293 28544877352024668887097485)
                ·
                  refine ⟨10704329007009250832661557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28544877352024668887097485 10704329007009250832661557)
                  ·
                    refine ⟨1003530844407117265562021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10704329007009250832661557 1003530844407117265562021)
                    ·
                      rfl

theorem cell23_5863108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 1, 1, 1, 3, 3, 5].length) (baseStart_5863108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863108 prefixEnd_5863108 := by exact prefixLift 5863108
  have htrace : WordTrace (prefixWord ++ tailWord_5863108) baseStart_5863108 baseEnd_5863108 := by
    simpa [prefixWord, tailWord_5863108, baseEnd_5863108] using wordTrace_append hprefix tailTrace_5863108
  have hstable : (prefixWord ++ tailWord_5863108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863108).length < 2 ^ (prefixWord ++ tailWord_5863108).sum := by decide
  have hdescent : baseEnd_5863108 < baseStart_5863108 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863148 : List Nat := [2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 3]
def baseStart_5863148 : Nat := 118140960795 + 5863148 * 2 ^ 59
def prefixEnd_5863148 : Nat := 4983230072969 + 3 ^ 40 * 5863148 * 2
def baseEnd_5863148 : Nat := 3010613072447531640185879

theorem tailTrace_5863148 : CollatzResearch.WordTrace tailWord_5863148 prefixEnd_5863148 3010613072447531640185879 := by
  unfold tailWord_5863148
  simp only [CollatzResearch.WordTrace]
  refine ⟨106923287881411808401143049, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142564383841882411201524065 106923287881411808401143049)
  ·
    refine ⟨80192465911058856300857287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106923287881411808401143049 80192465911058856300857287)
    ·
      refine ⟨120288698866588284451285931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80192465911058856300857287 120288698866588284451285931)
      ·
        refine ⟨180433048299882426676928897, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120288698866588284451285931 180433048299882426676928897)
        ·
          refine ⟨135324786224911820007696673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180433048299882426676928897 135324786224911820007696673)
          ·
            refine ⟨101493589668683865005772505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135324786224911820007696673 101493589668683865005772505)
            ·
              refine ⟨76120192251512898754329379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101493589668683865005772505 76120192251512898754329379)
              ·
                refine ⟨114180288377269348131494069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76120192251512898754329379 114180288377269348131494069)
                ·
                  refine ⟨10704402035369001387327569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114180288377269348131494069 10704402035369001387327569)
                  ·
                    refine ⟨8028301526526751040495677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10704402035369001387327569 8028301526526751040495677)
                    ·
                      refine ⟨3010613072447531640185879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8028301526526751040495677 3010613072447531640185879)
                      ·
                        rfl

theorem cell23_5863148_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 5, 2, 3].length) (baseStart_5863148 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863148 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863148 prefixEnd_5863148 := by exact prefixLift 5863148
  have htrace : WordTrace (prefixWord ++ tailWord_5863148) baseStart_5863148 baseEnd_5863148 := by
    simpa [prefixWord, tailWord_5863148, baseEnd_5863148] using wordTrace_append hprefix tailTrace_5863148
  have hstable : (prefixWord ++ tailWord_5863148).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863148).length < 2 ^ (prefixWord ++ tailWord_5863148).sum := by decide
  have hdescent : baseEnd_5863148 < baseStart_5863148 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863148) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863151 : List Nat := [1, 1, 2, 1, 5, 1, 2, 10]
def baseStart_5863151 : Nat := 118140960795 + 5863151 * 2 ^ 59
def prefixEnd_5863151 : Nat := 4983230072969 + 3 ^ 40 * 5863151 * 2
def baseEnd_5863151 : Nat := 111504244921833152905495

theorem tailTrace_5863151 : CollatzResearch.WordTrace tailWord_5863151 prefixEnd_5863151 111504244921833152905495 := by
  unfold tailWord_5863151
  simp only [CollatzResearch.WordTrace]
  refine ⟨213846685181812748314645307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142564456787875165543096871 213846685181812748314645307)
  ·
    refine ⟨320770027772719122471967961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213846685181812748314645307 320770027772719122471967961)
    ·
      refine ⟨240577520829539341853975971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320770027772719122471967961 240577520829539341853975971)
      ·
        refine ⟨360866281244309012780963957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240577520829539341853975971 360866281244309012780963957)
        ·
          refine ⟨33831213866653969948215371, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 360866281244309012780963957 33831213866653969948215371)
          ·
            refine ⟨50746820799980954922323057, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33831213866653969948215371 50746820799980954922323057)
            ·
              refine ⟨38060115599985716191742293, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50746820799980954922323057 38060115599985716191742293)
              ·
                refine ⟨111504244921833152905495, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38060115599985716191742293 111504244921833152905495)
                ·
                  rfl

theorem cell23_5863151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 2, 10].length) (baseStart_5863151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863151 prefixEnd_5863151 := by exact prefixLift 5863151
  have htrace : WordTrace (prefixWord ++ tailWord_5863151) baseStart_5863151 baseEnd_5863151 := by
    simpa [prefixWord, tailWord_5863151, baseEnd_5863151] using wordTrace_append hprefix tailTrace_5863151
  have hstable : (prefixWord ++ tailWord_5863151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863151).length < 2 ^ (prefixWord ++ tailWord_5863151).sum := by decide
  have hdescent : baseEnd_5863151 < baseStart_5863151 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863179 : List Nat := [1, 1, 1, 1, 5, 1, 5, 3, 1, 2, 2]
def baseStart_5863179 : Nat := 118140960795 + 5863179 * 2 ^ 59
def prefixEnd_5863179 : Nat := 4983230072969 + 3 ^ 40 * 5863179 * 2
def baseEnd_5863179 : Nat := 3010628990347821018898237

theorem tailTrace_5863179 : CollatzResearch.WordTrace tailWord_5863179 prefixEnd_5863179 3010628990347821018898237 := by
  unfold tailWord_5863179
  simp only [CollatzResearch.WordTrace]
  refine ⟨213847706425711309096664591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142565137617140872731109727 213847706425711309096664591)
  ·
    refine ⟨320771559638566963644996887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213847706425711309096664591 320771559638566963644996887)
    ·
      refine ⟨481157339457850445467495331, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320771559638566963644996887 481157339457850445467495331)
      ·
        refine ⟨721736009186775668201242997, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481157339457850445467495331 721736009186775668201242997)
        ·
          refine ⟨67662750861260218893866531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 721736009186775668201242997 67662750861260218893866531)
          ·
            refine ⟨101494126291890328340799797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67662750861260218893866531 101494126291890328340799797)
            ·
              refine ⟨9515074339864718281949981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101494126291890328340799797 9515074339864718281949981)
              ·
                refine ⟨3568152877449269355731243, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9515074339864718281949981 3568152877449269355731243)
                ·
                  refine ⟨5352229316173904033596865, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568152877449269355731243 5352229316173904033596865)
                  ·
                    refine ⟨4014171987130428025197649, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352229316173904033596865 4014171987130428025197649)
                    ·
                      refine ⟨3010628990347821018898237, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014171987130428025197649 3010628990347821018898237)
                      ·
                        rfl

theorem cell23_5863179_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 5, 3, 1, 2, 2].length) (baseStart_5863179 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863179 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863179 prefixEnd_5863179 := by exact prefixLift 5863179
  have htrace : WordTrace (prefixWord ++ tailWord_5863179) baseStart_5863179 baseEnd_5863179 := by
    simpa [prefixWord, tailWord_5863179, baseEnd_5863179] using wordTrace_append hprefix tailTrace_5863179
  have hstable : (prefixWord ++ tailWord_5863179).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863179).length < 2 ^ (prefixWord ++ tailWord_5863179).sum := by decide
  have hdescent : baseEnd_5863179 < baseStart_5863179 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863179) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863196 : List Nat := [2, 2, 3, 1, 1, 2, 5, 2, 1, 2, 2]
def baseStart_5863196 : Nat := 118140960795 + 5863196 * 2 ^ 59
def prefixEnd_5863196 : Nat := 4983230072969 + 3 ^ 40 * 5863196 * 2
def baseEnd_5863196 : Nat := 3010637719518947452385659

theorem tailTrace_5863196 : CollatzResearch.WordTrace tailWord_5863196 prefixEnd_5863196 3010637719518947452385659 := by
  unfold tailWord_5863196
  simp only [CollatzResearch.WordTrace]
  refine ⟨106924163233324860500016721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142565550977766480666688961 106924163233324860500016721)
  ·
    refine ⟨80193122424993645375012541, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106924163233324860500016721 80193122424993645375012541)
    ·
      refine ⟨30072420909372617015629703, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80193122424993645375012541 30072420909372617015629703)
      ·
        refine ⟨45108631364058925523444555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30072420909372617015629703 45108631364058925523444555)
        ·
          refine ⟨67662947046088388285166833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45108631364058925523444555 67662947046088388285166833)
          ·
            refine ⟨50747210284566291213875125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67662947046088388285166833 50747210284566291213875125)
            ·
              refine ⟨4757550964178089801300793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50747210284566291213875125 4757550964178089801300793)
              ·
                refine ⟨3568163223133567350975595, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4757550964178089801300793 3568163223133567350975595)
                ·
                  refine ⟨5352244834700351026463393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568163223133567350975595 5352244834700351026463393)
                  ·
                    refine ⟨4014183626025263269847545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352244834700351026463393 4014183626025263269847545)
                    ·
                      refine ⟨3010637719518947452385659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014183626025263269847545 3010637719518947452385659)
                      ·
                        rfl

theorem cell23_5863196_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 5, 2, 1, 2, 2].length) (baseStart_5863196 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863196 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863196 prefixEnd_5863196 := by exact prefixLift 5863196
  have htrace : WordTrace (prefixWord ++ tailWord_5863196) baseStart_5863196 baseEnd_5863196 := by
    simpa [prefixWord, tailWord_5863196, baseEnd_5863196] using wordTrace_append hprefix tailTrace_5863196
  have hstable : (prefixWord ++ tailWord_5863196).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863196).length < 2 ^ (prefixWord ++ tailWord_5863196).sum := by decide
  have hdescent : baseEnd_5863196 < baseStart_5863196 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863196) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863212 : List Nat := [2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 3]
def baseStart_5863212 : Nat := 118140960795 + 5863212 * 2 ^ 59
def prefixEnd_5863212 : Nat := 4983230072969 + 3 ^ 40 * 5863212 * 2
def baseEnd_5863212 : Nat := 3010645935209419389785585

theorem tailTrace_5863212 : CollatzResearch.WordTrace tailWord_5863212 prefixEnd_5863212 3010645935209419389785585 := by
  unfold tailWord_5863212
  simp only [CollatzResearch.WordTrace]
  refine ⟨106924455017295877866307945, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142565940023061170488410593 106924455017295877866307945)
  ·
    refine ⟨80193341262971908399730959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106924455017295877866307945 80193341262971908399730959)
    ·
      refine ⟨120290011894457862599596439, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80193341262971908399730959 120290011894457862599596439)
      ·
        refine ⟨180435017841686793899394659, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120290011894457862599596439 180435017841686793899394659)
        ·
          refine ⟨270652526762530190849091989, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180435017841686793899394659 270652526762530190849091989)
          ·
            refine ⟨12686837191993602696051187, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 270652526762530190849091989 12686837191993602696051187)
            ·
              refine ⟨19030255787990404044076781, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12686837191993602696051187 19030255787990404044076781)
              ·
                refine ⟨7136345920496401516528793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19030255787990404044076781 7136345920496401516528793)
                ·
                  refine ⟨5352259440372301137396595, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7136345920496401516528793 5352259440372301137396595)
                  ·
                    refine ⟨8028389160558451706094893, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5352259440372301137396595 8028389160558451706094893)
                    ·
                      refine ⟨3010645935209419389785585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8028389160558451706094893 3010645935209419389785585)
                      ·
                        rfl

theorem cell23_5863212_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 2, 1, 3].length) (baseStart_5863212 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863212 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863212 prefixEnd_5863212 := by exact prefixLift 5863212
  have htrace : WordTrace (prefixWord ++ tailWord_5863212) baseStart_5863212 baseEnd_5863212 := by
    simpa [prefixWord, tailWord_5863212, baseEnd_5863212] using wordTrace_append hprefix tailTrace_5863212
  have hstable : (prefixWord ++ tailWord_5863212).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863212).length < 2 ^ (prefixWord ++ tailWord_5863212).sum := by decide
  have hdescent : baseEnd_5863212 < baseStart_5863212 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863212) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863235 : List Nat := [1, 1, 1, 3, 1, 5, 1, 1, 3, 4, 2]
def baseStart_5863235 : Nat := 118140960795 + 5863235 * 2 ^ 59
def prefixEnd_5863235 : Nat := 4983230072969 + 3 ^ 40 * 5863235 * 2
def baseEnd_5863235 : Nat := 3010657745264472799797979

theorem tailTrace_5863235 : CollatzResearch.WordTrace tailWord_5863235 prefixEnd_5863235 3010657745264472799797979 := by
  unfold tailWord_5863235
  simp only [CollatzResearch.WordTrace]
  refine ⟨213849748913508430660703159, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142566499275672287107135439 213849748913508430660703159)
  ·
    refine ⟨320774623370262645991054739, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213849748913508430660703159 320774623370262645991054739)
    ·
      refine ⟨481161935055393968986582109, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320774623370262645991054739 481161935055393968986582109)
      ·
        refine ⟨180435725645772738369968291, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481161935055393968986582109 180435725645772738369968291)
        ·
          refine ⟨270653588468659107554952437, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180435725645772738369968291 270653588468659107554952437)
          ·
            refine ⟨25373773918936791333276791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270653588468659107554952437 25373773918936791333276791)
            ·
              refine ⟨38060660878405186999915187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25373773918936791333276791 38060660878405186999915187)
              ·
                refine ⟨57090991317607780499872781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38060660878405186999915187 57090991317607780499872781)
                ·
                  refine ⟨21409121744102917687452293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57090991317607780499872781 21409121744102917687452293)
                  ·
                    refine ⟨4014210327019297066397305, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21409121744102917687452293 4014210327019297066397305)
                    ·
                      refine ⟨3010657745264472799797979, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014210327019297066397305 3010657745264472799797979)
                      ·
                        rfl

theorem cell23_5863235_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 5, 1, 1, 3, 4, 2].length) (baseStart_5863235 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863235 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863235 prefixEnd_5863235 := by exact prefixLift 5863235
  have htrace : WordTrace (prefixWord ++ tailWord_5863235) baseStart_5863235 baseEnd_5863235 := by
    simpa [prefixWord, tailWord_5863235, baseEnd_5863235] using wordTrace_append hprefix tailTrace_5863235
  have hstable : (prefixWord ++ tailWord_5863235).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863235).length < 2 ^ (prefixWord ++ tailWord_5863235).sum := by decide
  have hdescent : baseEnd_5863235 < baseStart_5863235 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863235) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863248 : List Nat := [2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4]
def baseStart_5863248 : Nat := 118140960795 + 5863248 * 2 ^ 59
def prefixEnd_5863248 : Nat := 4983230072969 + 3 ^ 40 * 5863248 * 2
def baseEnd_5863248 : Nat := 3010664420512981248935419

theorem tailTrace_5863248 : CollatzResearch.WordTrace tailWord_5863248 prefixEnd_5863248 3010664420512981248935419 := by
  unfold tailWord_5863248
  simp only [CollatzResearch.WordTrace]
  refine ⟨106925111531230666940463199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142566815374974222587284265 106925111531230666940463199)
  ·
    refine ⟨160387667296846000410694799, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106925111531230666940463199 160387667296846000410694799)
    ·
      refine ⟨240581500945269000616042199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160387667296846000410694799 240581500945269000616042199)
      ·
        refine ⟨360872251417903500924063299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240581500945269000616042199 360872251417903500924063299)
        ·
          refine ⟨541308377126855251386094949, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360872251417903500924063299 541308377126855251386094949)
          ·
            refine ⟨101495320711285359634892803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 541308377126855251386094949 101495320711285359634892803)
            ·
              refine ⟨152242981066928039452339205, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101495320711285359634892803 152242981066928039452339205)
              ·
                refine ⟨28545558950049007397313601, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 152242981066928039452339205 28545558950049007397313601)
                ·
                  refine ⟨21409169212536755547985201, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28545558950049007397313601 21409169212536755547985201)
                  ·
                    refine ⟨16056876909402566660988901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21409169212536755547985201 16056876909402566660988901)
                    ·
                      refine ⟨3010664420512981248935419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16056876909402566660988901 3010664420512981248935419)
                      ·
                        rfl

theorem cell23_5863248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 1, 4, 2, 2, 4].length) (baseStart_5863248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863248 prefixEnd_5863248 := by exact prefixLift 5863248
  have htrace : WordTrace (prefixWord ++ tailWord_5863248) baseStart_5863248 baseEnd_5863248 := by
    simpa [prefixWord, tailWord_5863248, baseEnd_5863248] using wordTrace_append hprefix tailTrace_5863248
  have hstable : (prefixWord ++ tailWord_5863248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863248).length < 2 ^ (prefixWord ++ tailWord_5863248).sum := by decide
  have hdescent : baseEnd_5863248 < baseStart_5863248 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863258 : List Nat := [3, 1, 1, 2, 1, 3, 2, 3, 7]
def baseStart_5863258 : Nat := 118140960795 + 5863258 * 2 ^ 59
def prefixEnd_5863258 : Nat := 4983230072969 + 3 ^ 40 * 5863258 * 2
def baseEnd_5863258 : Nat := 334518839479947356645597

theorem tailTrace_5863258 : CollatzResearch.WordTrace tailWord_5863258 prefixEnd_5863258 334518839479947356645597 := by
  unfold tailWord_5863258
  simp only [CollatzResearch.WordTrace]
  refine ⟨53462646948106276397197607, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142567058528283403725860285 53462646948106276397197607)
  ·
    refine ⟨80193970422159414595796411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53462646948106276397197607 80193970422159414595796411)
    ·
      refine ⟨120290955633239121893694617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80193970422159414595796411 120290955633239121893694617)
      ·
        refine ⟨90218216724929341420270963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120290955633239121893694617 90218216724929341420270963)
        ·
          refine ⟨135327325087394012130406445, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90218216724929341420270963 135327325087394012130406445)
          ·
            refine ⟨50747746907772754548902417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135327325087394012130406445 50747746907772754548902417)
            ·
              refine ⟨38060810180829565911676813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50747746907772754548902417 38060810180829565911676813)
              ·
                refine ⟨14272803817811087216878805, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38060810180829565911676813 14272803817811087216878805)
                ·
                  refine ⟨334518839479947356645597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14272803817811087216878805 334518839479947356645597)
                  ·
                    rfl

theorem cell23_5863258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 1, 3, 2, 3, 7].length) (baseStart_5863258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863258 prefixEnd_5863258 := by exact prefixLift 5863258
  have htrace : WordTrace (prefixWord ++ tailWord_5863258) baseStart_5863258 baseEnd_5863258 := by
    simpa [prefixWord, tailWord_5863258, baseEnd_5863258] using wordTrace_append hprefix tailTrace_5863258
  have hstable : (prefixWord ++ tailWord_5863258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863258).length < 2 ^ (prefixWord ++ tailWord_5863258).sum := by decide
  have hdescent : baseEnd_5863258 < baseStart_5863258 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863285 : List Nat := [1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 3]
def baseStart_5863285 : Nat := 118140960795 + 5863285 * 2 ^ 59
def prefixEnd_5863285 : Nat := 4983230072969 + 3 ^ 40 * 5863285 * 2
def baseEnd_5863285 : Nat := 3010683419297197604172749

theorem tailTrace_5863285 : CollatzResearch.WordTrace tailWord_5863285 prefixEnd_5863285 3010683419297197604172749 := by
  unfold tailWord_5863285
  simp only [CollatzResearch.WordTrace]
  refine ⟨213851572563327289200023309, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142567715042218192800015539 213851572563327289200023309)
  ·
    refine ⟨80194339711247733450008741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213851572563327289200023309 80194339711247733450008741)
    ·
      refine ⟨15036438695858950021876639, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80194339711247733450008741 15036438695858950021876639)
      ·
        refine ⟨22554658043788425032814959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15036438695858950021876639 22554658043788425032814959)
        ·
          refine ⟨33831987065682637549222439, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22554658043788425032814959 33831987065682637549222439)
          ·
            refine ⟨50747980598523956323833659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33831987065682637549222439 50747980598523956323833659)
            ·
              refine ⟨76121970897785934485750489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50747980598523956323833659 76121970897785934485750489)
              ·
                refine ⟨57091478173339450864312867, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76121970897785934485750489 57091478173339450864312867)
                ·
                  refine ⟨85637217260009176296469301, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57091478173339450864312867 85637217260009176296469301)
                  ·
                    refine ⟨8028489118125860277793997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85637217260009176296469301 8028489118125860277793997)
                    ·
                      refine ⟨3010683419297197604172749, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8028489118125860277793997 3010683419297197604172749)
                      ·
                        rfl

theorem cell23_5863285_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 1, 1, 2, 1, 5, 3].length) (baseStart_5863285 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863285 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863285 prefixEnd_5863285 := by exact prefixLift 5863285
  have htrace : WordTrace (prefixWord ++ tailWord_5863285) baseStart_5863285 baseEnd_5863285 := by
    simpa [prefixWord, tailWord_5863285, baseEnd_5863285] using wordTrace_append hprefix tailTrace_5863285
  have hstable : (prefixWord ++ tailWord_5863285).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863285).length < 2 ^ (prefixWord ++ tailWord_5863285).sum := by decide
  have hdescent : baseEnd_5863285 < baseStart_5863285 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863285) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863303 : List Nat := [1, 1, 4, 2, 5, 1, 1, 2, 2, 2, 2]
def baseStart_5863303 : Nat := 118140960795 + 5863303 * 2 ^ 59
def prefixEnd_5863303 : Nat := 4983230072969 + 3 ^ 40 * 5863303 * 2
def baseEnd_5863303 : Nat := 3010692661948978533747667

theorem tailTrace_5863303 : CollatzResearch.WordTrace tailWord_5863303 prefixEnd_5863303 3010692661948978533747667 := by
  unfold tailWord_5863303
  simp only [CollatzResearch.WordTrace]
  refine ⟨213852229077262078274178563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142568152718174718849452375 213852229077262078274178563)
  ·
    refine ⟨320778343615893117411267845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213852229077262078274178563 320778343615893117411267845)
    ·
      refine ⟨60145939427979959514612721, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320778343615893117411267845 60145939427979959514612721)
      ·
        refine ⟨45109454570984969635959541, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60145939427979959514612721 45109454570984969635959541)
        ·
          refine ⟨4229011366029840903371207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45109454570984969635959541 4229011366029840903371207)
          ·
            refine ⟨6343517049044761355056811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229011366029840903371207 6343517049044761355056811)
            ·
              refine ⟨9515275573567142032585217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343517049044761355056811 9515275573567142032585217)
              ·
                refine ⟨7136456680175356524438913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9515275573567142032585217 7136456680175356524438913)
                ·
                  refine ⟨5352342510131517393329185, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7136456680175356524438913 5352342510131517393329185)
                  ·
                    refine ⟨4014256882598638044996889, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352342510131517393329185 4014256882598638044996889)
                    ·
                      refine ⟨3010692661948978533747667, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014256882598638044996889 3010692661948978533747667)
                      ·
                        rfl

theorem cell23_5863303_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 5, 1, 1, 2, 2, 2, 2].length) (baseStart_5863303 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863303 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863303 prefixEnd_5863303 := by exact prefixLift 5863303
  have htrace : WordTrace (prefixWord ++ tailWord_5863303) baseStart_5863303 baseEnd_5863303 := by
    simpa [prefixWord, tailWord_5863303, baseEnd_5863303] using wordTrace_append hprefix tailTrace_5863303
  have hstable : (prefixWord ++ tailWord_5863303).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863303).length < 2 ^ (prefixWord ++ tailWord_5863303).sum := by decide
  have hdescent : baseEnd_5863303 < baseStart_5863303 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863303) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863325 : List Nat := [1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 4]
def baseStart_5863325 : Nat := 118140960795 + 5863325 * 2 ^ 59
def prefixEnd_5863325 : Nat := 4983230072969 + 3 ^ 40 * 5863325 * 2
def baseEnd_5863325 : Nat := 3010703958523377447672565

theorem tailTrace_5863325 : CollatzResearch.WordTrace tailWord_5863325 prefixEnd_5863325 3010703958523377447672565 := by
  unfold tailWord_5863325
  simp only [CollatzResearch.WordTrace]
  refine ⟨213853031483182376031479429, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142568687655454917354319619 213853031483182376031479429)
  ·
    refine ⟨40097443403096695505902393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213853031483182376031479429 40097443403096695505902393)
    ·
      refine ⟨30073082552322521629426795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40097443403096695505902393 30073082552322521629426795)
      ·
        refine ⟨45109623828483782444140193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30073082552322521629426795 45109623828483782444140193)
        ·
          refine ⟨33832217871362836833105145, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45109623828483782444140193 33832217871362836833105145)
          ·
            refine ⟨25374163403522127624828859, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33832217871362836833105145 25374163403522127624828859)
            ·
              refine ⟨38061245105283191437243289, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25374163403522127624828859 38061245105283191437243289)
              ·
                refine ⟨28545933828962393577932467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38061245105283191437243289 28545933828962393577932467)
                ·
                  refine ⟨42818900743443590366898701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28545933828962393577932467 42818900743443590366898701)
                  ·
                    refine ⟨16057087778791346387587013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42818900743443590366898701 16057087778791346387587013)
                    ·
                      refine ⟨3010703958523377447672565, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16057087778791346387587013 3010703958523377447672565)
                      ·
                        rfl

theorem cell23_5863325_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 2, 1, 3, 4].length) (baseStart_5863325 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863325 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863325 prefixEnd_5863325 := by exact prefixLift 5863325
  have htrace : WordTrace (prefixWord ++ tailWord_5863325) baseStart_5863325 baseEnd_5863325 := by
    simpa [prefixWord, tailWord_5863325, baseEnd_5863325] using wordTrace_append hprefix tailTrace_5863325
  have hstable : (prefixWord ++ tailWord_5863325).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863325).length < 2 ^ (prefixWord ++ tailWord_5863325).sum := by decide
  have hdescent : baseEnd_5863325 < baseStart_5863325 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863325) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863392 : List Nat := [2, 1, 1, 3, 1, 1, 1, 6, 3, 1, 3]
def baseStart_5863392 : Nat := 118140960795 + 5863392 * 2 ^ 59
def prefixEnd_5863392 : Nat := 4983230072969 + 3 ^ 40 * 5863392 * 2
def baseEnd_5863392 : Nat := 3010738361727228685534757

theorem tailTrace_5863392 : CollatzResearch.WordTrace tailWord_5863392 prefixEnd_5863392 3010738361727228685534757 := by
  unfold tailWord_5863392
  simp only [CollatzResearch.WordTrace]
  refine ⟨106927737586969823237084215, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142570316782626430982778953 106927737586969823237084215)
  ·
    refine ⟨160391606380454734855626323, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106927737586969823237084215 160391606380454734855626323)
    ·
      refine ⟨240587409570682102283439485, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160391606380454734855626323 240587409570682102283439485)
      ·
        refine ⟨90220278589005788356289807, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240587409570682102283439485 90220278589005788356289807)
        ·
          refine ⟨135330417883508682534434711, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90220278589005788356289807 135330417883508682534434711)
          ·
            refine ⟨202995626825263023801652067, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135330417883508682534434711 202995626825263023801652067)
            ·
              refine ⟨304493440237894535702478101, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 202995626825263023801652067 304493440237894535702478101)
              ·
                refine ⟨14273130011151306361053661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 304493440237894535702478101 14273130011151306361053661)
                ·
                  refine ⟨5352423754181739885395123, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14273130011151306361053661 5352423754181739885395123)
                  ·
                    refine ⟨8028635631272609828092685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5352423754181739885395123 8028635631272609828092685)
                    ·
                      refine ⟨3010738361727228685534757, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8028635631272609828092685 3010738361727228685534757)
                      ·
                        rfl

theorem cell23_5863392_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 6, 3, 1, 3].length) (baseStart_5863392 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863392 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863392 prefixEnd_5863392 := by exact prefixLift 5863392
  have htrace : WordTrace (prefixWord ++ tailWord_5863392) baseStart_5863392 baseEnd_5863392 := by
    simpa [prefixWord, tailWord_5863392, baseEnd_5863392] using wordTrace_append hprefix tailTrace_5863392
  have hstable : (prefixWord ++ tailWord_5863392).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863392).length < 2 ^ (prefixWord ++ tailWord_5863392).sum := by decide
  have hdescent : baseEnd_5863392 < baseStart_5863392 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863392) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863425 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 3, 6]
def baseStart_5863425 : Nat := 118140960795 + 5863425 * 2 ^ 59
def prefixEnd_5863425 : Nat := 4983230072969 + 3 ^ 40 * 5863425 * 2
def baseEnd_5863425 : Nat := 1003585102196275685474035

theorem tailTrace_5863425 : CollatzResearch.WordTrace tailWord_5863425 prefixEnd_5863425 1003585102196275685474035 := by
  unfold tailWord_5863425
  simp only [CollatzResearch.WordTrace]
  refine ⟨213856678782820093110119729, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142571119188546728740079819 213856678782820093110119729)
  ·
    refine ⟨160392509087115069832589797, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213856678782820093110119729 160392509087115069832589797)
    ·
      refine ⟨30073595453834075593610587, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160392509087115069832589797 30073595453834075593610587)
      ·
        refine ⟨45110393180751113390415881, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30073595453834075593610587 45110393180751113390415881)
        ·
          refine ⟨33832794885563335042811911, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45110393180751113390415881 33832794885563335042811911)
          ·
            refine ⟨50749192328345002564217867, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33832794885563335042811911 50749192328345002564217867)
            ·
              refine ⟨76123788492517503846326801, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50749192328345002564217867 76123788492517503846326801)
              ·
                refine ⟨57092841369388127884745101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76123788492517503846326801 57092841369388127884745101)
                ·
                  refine ⟨21409815513520547956779413, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57092841369388127884745101 21409815513520547956779413)
                  ·
                    refine ⟨1003585102196275685474035, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21409815513520547956779413 1003585102196275685474035)
                    ·
                      rfl

theorem cell23_5863425_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 3, 6].length) (baseStart_5863425 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863425 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863425 prefixEnd_5863425 := by exact prefixLift 5863425
  have htrace : WordTrace (prefixWord ++ tailWord_5863425) baseStart_5863425 baseEnd_5863425 := by
    simpa [prefixWord, tailWord_5863425, baseEnd_5863425] using wordTrace_append hprefix tailTrace_5863425
  have hstable : (prefixWord ++ tailWord_5863425).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863425).length < 2 ^ (prefixWord ++ tailWord_5863425).sum := by decide
  have hdescent : baseEnd_5863425 < baseStart_5863425 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863425) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863435 : List Nat := [1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5]
def baseStart_5863435 : Nat := 118140960795 + 5863435 * 2 ^ 59
def prefixEnd_5863435 : Nat := 4983230072969 + 3 ^ 40 * 5863435 * 2
def baseEnd_5863435 : Nat := 3010760441395372017297059

theorem tailTrace_5863435 : CollatzResearch.WordTrace tailWord_5863435 prefixEnd_5863435 3010760441395372017297059 := by
  unfold tailWord_5863435
  simp only [CollatzResearch.WordTrace]
  refine ⟨213857043512783864817983759, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142571362341855909878655839 213857043512783864817983759)
  ·
    refine ⟨320785565269175797226975639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213857043512783864817983759 320785565269175797226975639)
    ·
      refine ⟨481178347903763695840463459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320785565269175797226975639 481178347903763695840463459)
      ·
        refine ⟨721767521855645543760695189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481178347903763695840463459 721767521855645543760695189)
        ·
          refine ⟨33832852586983384863782587, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 721767521855645543760695189 33832852586983384863782587)
          ·
            refine ⟨50749278880475077295673881, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33832852586983384863782587 50749278880475077295673881)
            ·
              refine ⟨38061959160356307971755411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50749278880475077295673881 38061959160356307971755411)
              ·
                refine ⟨57092938740534461957633117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38061959160356307971755411 57092938740534461957633117)
                ·
                  refine ⟨21409852027700423234112419, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57092938740534461957633117 21409852027700423234112419)
                  ·
                    refine ⟨32114778041550634851168629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21409852027700423234112419 32114778041550634851168629)
                    ·
                      refine ⟨3010760441395372017297059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32114778041550634851168629 3010760441395372017297059)
                      ·
                        rfl

theorem cell23_5863435_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 6, 1, 2, 1, 3, 1, 5].length) (baseStart_5863435 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863435 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863435 prefixEnd_5863435 := by exact prefixLift 5863435
  have htrace : WordTrace (prefixWord ++ tailWord_5863435) baseStart_5863435 baseEnd_5863435 := by
    simpa [prefixWord, tailWord_5863435, baseEnd_5863435] using wordTrace_append hprefix tailTrace_5863435
  have hstable : (prefixWord ++ tailWord_5863435).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863435).length < 2 ^ (prefixWord ++ tailWord_5863435).sum := by decide
  have hdescent : baseEnd_5863435 < baseStart_5863435 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863435) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863463 : List Nat := [1, 1, 7, 1, 2, 2, 2, 1, 1, 5]
def baseStart_5863463 : Nat := 118140960795 + 5863463 * 2 ^ 59
def prefixEnd_5863463 : Nat := 4983230072969 + 3 ^ 40 * 5863463 * 2
def baseEnd_5863463 : Nat := 1003591606284565969248977

theorem tailTrace_5863463 : CollatzResearch.WordTrace tailWord_5863463 prefixEnd_5863463 1003591606284565969248977 := by
  unfold tailWord_5863463
  simp only [CollatzResearch.WordTrace]
  refine ⟨213858064756682425600003043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142572043171121617066668695 213858064756682425600003043)
  ·
    refine ⟨320787097135023638400004565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213858064756682425600003043 320787097135023638400004565)
    ·
      refine ⟨7518447589102116525000107, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 320787097135023638400004565 7518447589102116525000107)
      ·
        refine ⟨11277671383653174787500161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518447589102116525000107 11277671383653174787500161)
        ·
          refine ⟨8458253537739881090625121, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277671383653174787500161 8458253537739881090625121)
          ·
            refine ⟨6343690153304910817968841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8458253537739881090625121 6343690153304910817968841)
            ·
              refine ⟨4757767614978683113476631, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6343690153304910817968841 4757767614978683113476631)
              ·
                refine ⟨7136651422468024670214947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757767614978683113476631 7136651422468024670214947)
                ·
                  refine ⟨10704977133702037005322421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7136651422468024670214947 10704977133702037005322421)
                  ·
                    refine ⟨1003591606284565969248977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10704977133702037005322421 1003591606284565969248977)
                    ·
                      rfl

theorem cell23_5863463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 2, 1, 1, 5].length) (baseStart_5863463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863463 prefixEnd_5863463 := by exact prefixLift 5863463
  have htrace : WordTrace (prefixWord ++ tailWord_5863463) baseStart_5863463 baseEnd_5863463 := by
    simpa [prefixWord, tailWord_5863463, baseEnd_5863463] using wordTrace_append hprefix tailTrace_5863463
  have hstable : (prefixWord ++ tailWord_5863463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863463).length < 2 ^ (prefixWord ++ tailWord_5863463).sum := by decide
  have hdescent : baseEnd_5863463 < baseStart_5863463 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863465 : List Nat := [1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 3]
def baseStart_5863465 : Nat := 118140960795 + 5863465 * 2 ^ 59
def prefixEnd_5863465 : Nat := 4983230072969 + 3 ^ 40 * 5863465 * 2
def baseEnd_5863465 : Nat := 3010775845815006899921921

theorem tailTrace_5863465 : CollatzResearch.WordTrace tailWord_5863465 prefixEnd_5863465 3010775845815006899921921 := by
  unfold tailWord_5863465
  simp only [CollatzResearch.WordTrace]
  refine ⟨213858137702675179941575849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142572091801783453294383899 213858137702675179941575849)
  ·
    refine ⟨160393603277006384956181887, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213858137702675179941575849 160393603277006384956181887)
    ·
      refine ⟨240590404915509577434272831, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160393603277006384956181887 240590404915509577434272831)
      ·
        refine ⟨360885607373264366151409247, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240590404915509577434272831 360885607373264366151409247)
        ·
          refine ⟨541328411059896549227113871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360885607373264366151409247 541328411059896549227113871)
          ·
            refine ⟨811992616589844823840670807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541328411059896549227113871 811992616589844823840670807)
            ·
              refine ⟨1217988924884767235761006211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 811992616589844823840670807 1217988924884767235761006211)
              ·
                refine ⟨1826983387327150853641509317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1217988924884767235761006211 1826983387327150853641509317)
                ·
                  refine ⟨342559385123840785057782997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1826983387327150853641509317 342559385123840785057782997)
                  ·
                    refine ⟨8028735588840018399791789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 342559385123840785057782997 8028735588840018399791789)
                    ·
                      refine ⟨3010775845815006899921921, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8028735588840018399791789 3010775845815006899921921)
                      ·
                        rfl

theorem cell23_5863465_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 1, 1, 4, 7, 3].length) (baseStart_5863465 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863465 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863465 prefixEnd_5863465 := by exact prefixLift 5863465
  have htrace : WordTrace (prefixWord ++ tailWord_5863465) baseStart_5863465 baseEnd_5863465 := by
    simpa [prefixWord, tailWord_5863465, baseEnd_5863465] using wordTrace_append hprefix tailTrace_5863465
  have hstable : (prefixWord ++ tailWord_5863465).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863465).length < 2 ^ (prefixWord ++ tailWord_5863465).sum := by decide
  have hdescent : baseEnd_5863465 < baseStart_5863465 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863465) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863466 : List Nat := [3, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4]
def baseStart_5863466 : Nat := 118140960795 + 5863466 * 2 ^ 59
def prefixEnd_5863466 : Nat := 4983230072969 + 3 ^ 40 * 5863466 * 2
def baseEnd_5863466 : Nat := 3010776359295661396009417

theorem tailTrace_5863466 : CollatzResearch.WordTrace tailWord_5863466 prefixEnd_5863466 3010776359295661396009417 := by
  unfold tailWord_5863466
  simp only [CollatzResearch.WordTrace]
  refine ⟨53464543543917889278090563, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142572116117114371408241501 53464543543917889278090563)
  ·
    refine ⟨80196815315876833917135845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53464543543917889278090563 80196815315876833917135845)
    ·
      refine ⟨15036902871726906359462971, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 80196815315876833917135845 15036902871726906359462971)
      ·
        refine ⟨22555354307590359539194457, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15036902871726906359462971 22555354307590359539194457)
        ·
          refine ⟨16916515730692769654395843, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22555354307590359539194457 16916515730692769654395843)
          ·
            refine ⟨25374773596039154481593765, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16916515730692769654395843 25374773596039154481593765)
            ·
              refine ⟨4757770049257341465298831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25374773596039154481593765 4757770049257341465298831)
              ·
                refine ⟨7136655073886012197948247, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757770049257341465298831 7136655073886012197948247)
                ·
                  refine ⟨10704982610829018296922371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7136655073886012197948247 10704982610829018296922371)
                  ·
                    refine ⟨16057473916243527445383557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10704982610829018296922371 16057473916243527445383557)
                    ·
                      refine ⟨3010776359295661396009417, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16057473916243527445383557 3010776359295661396009417)
                      ·
                        rfl

theorem cell23_5863466_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 1, 2, 1, 4, 1, 1, 1, 4].length) (baseStart_5863466 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863466 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863466 prefixEnd_5863466 := by exact prefixLift 5863466
  have htrace : WordTrace (prefixWord ++ tailWord_5863466) baseStart_5863466 baseEnd_5863466 := by
    simpa [prefixWord, tailWord_5863466, baseEnd_5863466] using wordTrace_append hprefix tailTrace_5863466
  have hstable : (prefixWord ++ tailWord_5863466).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863466).length < 2 ^ (prefixWord ++ tailWord_5863466).sum := by decide
  have hdescent : baseEnd_5863466 < baseStart_5863466 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863466) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863476 : List Nat := [2, 5, 1, 2, 2, 1, 1, 1, 4, 4]
def baseStart_5863476 : Nat := 118140960795 + 5863476 * 2 ^ 59
def prefixEnd_5863476 : Nat := 4983230072969 + 3 ^ 40 * 5863476 * 2
def baseEnd_5863476 : Nat := 1003593831367402118961457

theorem tailTrace_5863476 : CollatzResearch.WordTrace tailWord_5863476 prefixEnd_5863476 1003593831367402118961457 := by
  unfold tailWord_5863476
  simp only [CollatzResearch.WordTrace]
  refine ⟨106929269452817664410113141, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142572359270423552546817521 106929269452817664410113141)
  ·
    refine ⟨10024619011201656038448107, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106929269452817664410113141 10024619011201656038448107)
    ·
      refine ⟨15036928516802484057672161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10024619011201656038448107 15036928516802484057672161)
      ·
        refine ⟨11277696387601863043254121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15036928516802484057672161 11277696387601863043254121)
        ·
          refine ⟨8458272290701397282440591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11277696387601863043254121 8458272290701397282440591)
          ·
            refine ⟨12687408436052095923660887, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458272290701397282440591 12687408436052095923660887)
            ·
              refine ⟨19031112654078143885491331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12687408436052095923660887 19031112654078143885491331)
              ·
                refine ⟨28546668981117215828236997, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19031112654078143885491331 28546668981117215828236997)
                ·
                  refine ⟨5352500433959477967794437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28546668981117215828236997 5352500433959477967794437)
                  ·
                    refine ⟨1003593831367402118961457, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5352500433959477967794437 1003593831367402118961457)
                    ·
                      rfl

theorem cell23_5863476_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 2, 2, 1, 1, 1, 4, 4].length) (baseStart_5863476 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863476 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863476 prefixEnd_5863476 := by exact prefixLift 5863476
  have htrace : WordTrace (prefixWord ++ tailWord_5863476) baseStart_5863476 baseEnd_5863476 := by
    simpa [prefixWord, tailWord_5863476, baseEnd_5863476] using wordTrace_append hprefix tailTrace_5863476
  have hstable : (prefixWord ++ tailWord_5863476).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863476).length < 2 ^ (prefixWord ++ tailWord_5863476).sum := by decide
  have hdescent : baseEnd_5863476 < baseStart_5863476 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863476) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863506 : List Nat := [3, 2, 2, 1, 5, 1, 2, 7]
def baseStart_5863506 : Nat := 118140960795 + 5863506 * 2 ^ 59
def prefixEnd_5863506 : Nat := 4983230072969 + 3 ^ 40 * 5863506 * 2
def baseEnd_5863506 : Nat := 111510996241549675537379

theorem tailTrace_5863506 : CollatzResearch.WordTrace tailWord_5863506 prefixEnd_5863506 111510996241549675537379 := by
  unfold tailWord_5863506
  simp only [CollatzResearch.WordTrace]
  refine ⟨53464908273881660985954593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142573088730351095962545581 53464908273881660985954593)
  ·
    refine ⟨40098681205411245739465945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53464908273881660985954593 40098681205411245739465945)
    ·
      refine ⟨30074010904058434304599459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40098681205411245739465945 30074010904058434304599459)
      ·
        refine ⟨45111016356087651456899189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30074010904058434304599459 45111016356087651456899189)
        ·
          refine ⟨4229157783383217324084299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45111016356087651456899189 4229157783383217324084299)
          ·
            refine ⟨6343736675074825986126449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229157783383217324084299 6343736675074825986126449)
            ·
              refine ⟨4757802506306119489594837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6343736675074825986126449 4757802506306119489594837)
              ·
                refine ⟨111510996241549675537379, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4757802506306119489594837 111510996241549675537379)
                ·
                  rfl

theorem cell23_5863506_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 5, 1, 2, 7].length) (baseStart_5863506 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863506 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863506 prefixEnd_5863506 := by exact prefixLift 5863506
  have htrace : WordTrace (prefixWord ++ tailWord_5863506) baseStart_5863506 baseEnd_5863506 := by
    simpa [prefixWord, tailWord_5863506, baseEnd_5863506] using wordTrace_append hprefix tailTrace_5863506
  have hstable : (prefixWord ++ tailWord_5863506).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863506).length < 2 ^ (prefixWord ++ tailWord_5863506).sum := by decide
  have hdescent : baseEnd_5863506 < baseStart_5863506 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863506) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863517 : List Nat := [1, 4, 4, 1, 1, 3, 1, 3, 1, 2, 2]
def baseStart_5863517 : Nat := 118140960795 + 5863517 * 2 ^ 59
def prefixEnd_5863517 : Nat := 4983230072969 + 3 ^ 40 * 5863517 * 2
def baseEnd_5863517 : Nat := 3010802546809040696471683

theorem tailTrace_5863517 : CollatzResearch.WordTrace tailWord_5863517 prefixEnd_5863517 3010802546809040696471683 := by
  unfold tailWord_5863517
  simp only [CollatzResearch.WordTrace]
  refine ⟨213860034298486792822468805, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142573356198991195214979203 213860034298486792822468805)
  ·
    refine ⟨40098756430966273654212901, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213860034298486792822468805 40098756430966273654212901)
    ·
      refine ⟨7518516830806176310164919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40098756430966273654212901 7518516830806176310164919)
      ·
        refine ⟨11277775246209264465247379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7518516830806176310164919 11277775246209264465247379)
        ·
          refine ⟨16916662869313896697871069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11277775246209264465247379 16916662869313896697871069)
          ·
            refine ⟨6343748575992711261701651, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16916662869313896697871069 6343748575992711261701651)
            ·
              refine ⟨9515622863989066892552477, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6343748575992711261701651 9515622863989066892552477)
              ·
                refine ⟨3568358573995900084707179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9515622863989066892552477 3568358573995900084707179)
                ·
                  refine ⟨5352537860993850127060769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568358573995900084707179 5352537860993850127060769)
                  ·
                    refine ⟨4014403395745387595295577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5352537860993850127060769 4014403395745387595295577)
                    ·
                      refine ⟨3010802546809040696471683, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014403395745387595295577 3010802546809040696471683)
                      ·
                        rfl

theorem cell23_5863517_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 4, 1, 1, 3, 1, 3, 1, 2, 2].length) (baseStart_5863517 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863517 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863517 prefixEnd_5863517 := by exact prefixLift 5863517
  have htrace : WordTrace (prefixWord ++ tailWord_5863517) baseStart_5863517 baseEnd_5863517 := by
    simpa [prefixWord, tailWord_5863517, baseEnd_5863517] using wordTrace_append hprefix tailTrace_5863517
  have hstable : (prefixWord ++ tailWord_5863517).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863517).length < 2 ^ (prefixWord ++ tailWord_5863517).sum := by decide
  have hdescent : baseEnd_5863517 < baseStart_5863517 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863517) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863602 : List Nat := [3, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5]
def baseStart_5863602 : Nat := 118140960795 + 5863602 * 2 ^ 59
def prefixEnd_5863602 : Nat := 4983230072969 + 3 ^ 40 * 5863602 * 2
def baseEnd_5863602 : Nat := 3010846192664672863908791

theorem tailTrace_5863602 : CollatzResearch.WordTrace tailWord_5863602 prefixEnd_5863602 3010846192664672863908791 := by
  unfold tailWord_5863602
  simp only [CollatzResearch.WordTrace]
  refine ⟨53465783625794713084828265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142575423002119234892875373 53465783625794713084828265)
  ·
    refine ⟨40099337719346034813621199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53465783625794713084828265 40099337719346034813621199)
    ·
      refine ⟨60149006579019052220431799, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40099337719346034813621199 60149006579019052220431799)
      ·
        refine ⟨90223509868528578330647699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60149006579019052220431799 90223509868528578330647699)
        ·
          refine ⟨135335264802792867495971549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90223509868528578330647699 135335264802792867495971549)
          ·
            refine ⟨50750724301047325310989331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135335264802792867495971549 50750724301047325310989331)
            ·
              refine ⟨76126086451570987966483997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50750724301047325310989331 76126086451570987966483997)
              ·
                refine ⟨28547282419339120487431499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76126086451570987966483997 28547282419339120487431499)
                ·
                  refine ⟨42820923629008680731147249, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28547282419339120487431499 42820923629008680731147249)
                  ·
                    refine ⟨32115692721756510548360437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42820923629008680731147249 32115692721756510548360437)
                    ·
                      refine ⟨3010846192664672863908791, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32115692721756510548360437 3010846192664672863908791)
                      ·
                        rfl

theorem cell23_5863602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 3, 1, 2, 5].length) (baseStart_5863602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863602 prefixEnd_5863602 := by exact prefixLift 5863602
  have htrace : WordTrace (prefixWord ++ tailWord_5863602) baseStart_5863602 baseEnd_5863602 := by
    simpa [prefixWord, tailWord_5863602, baseEnd_5863602] using wordTrace_append hprefix tailTrace_5863602
  have hstable : (prefixWord ++ tailWord_5863602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863602).length < 2 ^ (prefixWord ++ tailWord_5863602).sum := by decide
  have hdescent : baseEnd_5863602 < baseStart_5863602 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863642 : List Nat := [3, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6]
def baseStart_5863642 : Nat := 118140960795 + 5863642 * 2 ^ 59
def prefixEnd_5863642 : Nat := 4983230072969 + 3 ^ 40 * 5863642 * 2
def baseEnd_5863642 : Nat := 3010866731890852707408607

theorem tailTrace_5863642 : CollatzResearch.WordTrace tailWord_5863642 prefixEnd_5863642 3010866731890852707408607 := by
  unfold tailWord_5863642
  simp only [CollatzResearch.WordTrace]
  refine ⟨53466148355758484792692295, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142576395615355959447179453 53466148355758484792692295)
  ·
    refine ⟨80199222533637727189038443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53466148355758484792692295 80199222533637727189038443)
    ·
      refine ⟨120298833800456590783557665, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80199222533637727189038443 120298833800456590783557665)
      ·
        refine ⟨90224125350342443087668249, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120298833800456590783557665 90224125350342443087668249)
        ·
          refine ⟨67668094012756832315751187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90224125350342443087668249 67668094012756832315751187)
          ·
            refine ⟨101502141019135248473626781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67668094012756832315751187 101502141019135248473626781)
            ·
              refine ⟨38063302882175718177610043, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101502141019135248473626781 38063302882175718177610043)
              ·
                refine ⟨57094954323263577266415065, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38063302882175718177610043 57094954323263577266415065)
                ·
                  refine ⟨42821215742447682949811299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57094954323263577266415065 42821215742447682949811299)
                  ·
                    refine ⟨64231823613671524424716949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42821215742447682949811299 64231823613671524424716949)
                    ·
                      refine ⟨3010866731890852707408607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64231823613671524424716949 3010866731890852707408607)
                      ·
                        rfl

theorem cell23_5863642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 2, 2, 1, 3, 1, 2, 1, 6].length) (baseStart_5863642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863642 prefixEnd_5863642 := by exact prefixLift 5863642
  have htrace : WordTrace (prefixWord ++ tailWord_5863642) baseStart_5863642 baseEnd_5863642 := by
    simpa [prefixWord, tailWord_5863642, baseEnd_5863642] using wordTrace_append hprefix tailTrace_5863642
  have hstable : (prefixWord ++ tailWord_5863642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863642).length < 2 ^ (prefixWord ++ tailWord_5863642).sum := by decide
  have hdescent : baseEnd_5863642 < baseStart_5863642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863649 : List Nat := [1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 3]
def baseStart_5863649 : Nat := 118140960795 + 5863649 * 2 ^ 59
def prefixEnd_5863649 : Nat := 4983230072969 + 3 ^ 40 * 5863649 * 2
def baseEnd_5863649 : Nat := 3010870326255434180021075

theorem tailTrace_5863649 : CollatzResearch.WordTrace tailWord_5863649 prefixEnd_5863649 3010870326255434180021075 := by
  unfold tailWord_5863649
  simp only [CollatzResearch.WordTrace]
  refine ⟨213864848734008579366274001, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142576565822672386244182667 213864848734008579366274001)
  ·
    refine ⟨160398636550506434524705501, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213864848734008579366274001 160398636550506434524705501)
    ·
      refine ⟨60149488706439912946764563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160398636550506434524705501 60149488706439912946764563)
      ·
        refine ⟨90224233059659869420146845, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60149488706439912946764563 90224233059659869420146845)
        ·
          refine ⟨33834087397372451032555067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90224233059659869420146845 33834087397372451032555067)
          ·
            refine ⟨50751131096058676548832601, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33834087397372451032555067 50751131096058676548832601)
            ·
              refine ⟨38063348322044007411624451, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50751131096058676548832601 38063348322044007411624451)
              ·
                refine ⟨57095022483066011117436677, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38063348322044007411624451 57095022483066011117436677)
                ·
                  refine ⟨10705316715574877084519377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57095022483066011117436677 10705316715574877084519377)
                  ·
                    refine ⟨8028987536681157813389533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10705316715574877084519377 8028987536681157813389533)
                    ·
                      refine ⟨3010870326255434180021075, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8028987536681157813389533 3010870326255434180021075)
                      ·
                        rfl

theorem cell23_5863649_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 3, 1, 2, 1, 4, 2, 3].length) (baseStart_5863649 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863649 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863649 prefixEnd_5863649 := by exact prefixLift 5863649
  have htrace : WordTrace (prefixWord ++ tailWord_5863649) baseStart_5863649 baseEnd_5863649 := by
    simpa [prefixWord, tailWord_5863649, baseEnd_5863649] using wordTrace_append hprefix tailTrace_5863649
  have hstable : (prefixWord ++ tailWord_5863649).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863649).length < 2 ^ (prefixWord ++ tailWord_5863649).sum := by decide
  have hdescent : baseEnd_5863649 < baseStart_5863649 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863649) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863656 : List Nat := [2, 1, 4, 1, 2, 3, 2, 1, 3, 4]
def baseStart_5863656 : Nat := 118140960795 + 5863656 * 2 ^ 59
def prefixEnd_5863656 : Nat := 4983230072969 + 3 ^ 40 * 5863656 * 2
def baseEnd_5863656 : Nat := 1003624640206671884211181

theorem tailTrace_5863656 : CollatzResearch.WordTrace tailWord_5863656 prefixEnd_5863656 1003624640206671884211181 := by
  unfold tailWord_5863656
  simp only [CollatzResearch.WordTrace]
  refine ⟨106932552022491609780889411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142576736029988813041185881 106932552022491609780889411)
  ·
    refine ⟨160398828033737414671334117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106932552022491609780889411 160398828033737414671334117)
    ·
      refine ⟨30074780256325765250875147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160398828033737414671334117 30074780256325765250875147)
      ·
        refine ⟨45112170384488647876312721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30074780256325765250875147 45112170384488647876312721)
        ·
          refine ⟨33834127788366485907234541, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45112170384488647876312721 33834127788366485907234541)
          ·
            refine ⟨12687797920637432215212953, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33834127788366485907234541 12687797920637432215212953)
            ·
              refine ⟨9515848440478074161409715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12687797920637432215212953 9515848440478074161409715)
              ·
                refine ⟨14273772660717111242114573, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9515848440478074161409715 14273772660717111242114573)
                ·
                  refine ⟨5352664747768916715792965, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14273772660717111242114573 5352664747768916715792965)
                  ·
                    refine ⟨1003624640206671884211181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5352664747768916715792965 1003624640206671884211181)
                    ·
                      rfl

theorem cell23_5863656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 1, 2, 3, 2, 1, 3, 4].length) (baseStart_5863656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863656 prefixEnd_5863656 := by exact prefixLift 5863656
  have htrace : WordTrace (prefixWord ++ tailWord_5863656) baseStart_5863656 baseEnd_5863656 := by
    simpa [prefixWord, tailWord_5863656, baseEnd_5863656] using wordTrace_append hprefix tailTrace_5863656
  have hstable : (prefixWord ++ tailWord_5863656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863656).length < 2 ^ (prefixWord ++ tailWord_5863656).sum := by decide
  have hdescent : baseEnd_5863656 < baseStart_5863656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863713 : List Nat := [1, 2, 3, 2, 1, 1, 2, 6, 1, 1, 3]
def baseStart_5863713 : Nat := 118140960795 + 5863713 * 2 ^ 59
def prefixEnd_5863713 : Nat := 4983230072969 + 3 ^ 40 * 5863713 * 2
def baseEnd_5863713 : Nat := 3010903189017321929620781

theorem tailTrace_5863713 : CollatzResearch.WordTrace tailWord_5863713 prefixEnd_5863713 3010903189017321929620781 := by
  unfold tailWord_5863713
  simp only [CollatzResearch.WordTrace]
  refine ⟨213867183005776718296603793, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142578122003851145531069195 213867183005776718296603793)
  ·
    refine ⟨160400387254332538722452845, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213867183005776718296603793 160400387254332538722452845)
    ·
      refine ⟨60150145220374702020919817, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160400387254332538722452845 60150145220374702020919817)
      ·
        refine ⟨45112608915281026515689863, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60150145220374702020919817 45112608915281026515689863)
        ·
          refine ⟨67668913372921539773534795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45112608915281026515689863 67668913372921539773534795)
          ·
            refine ⟨101503370059382309660302193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67668913372921539773534795 101503370059382309660302193)
            ·
              refine ⟨76127527544536732245226645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101503370059382309660302193 76127527544536732245226645)
              ·
                refine ⟨3568477853650159323994999, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76127527544536732245226645 3568477853650159323994999)
                ·
                  refine ⟨5352716780475238985992499, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568477853650159323994999 5352716780475238985992499)
                  ·
                    refine ⟨8029075170712858478988749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5352716780475238985992499 8029075170712858478988749)
                    ·
                      refine ⟨3010903189017321929620781, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8029075170712858478988749 3010903189017321929620781)
                      ·
                        rfl

theorem cell23_5863713_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 1, 1, 2, 6, 1, 1, 3].length) (baseStart_5863713 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863713 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863713 prefixEnd_5863713 := by exact prefixLift 5863713
  have htrace : WordTrace (prefixWord ++ tailWord_5863713) baseStart_5863713 baseEnd_5863713 := by
    simpa [prefixWord, tailWord_5863713, baseEnd_5863713] using wordTrace_append hprefix tailTrace_5863713
  have hstable : (prefixWord ++ tailWord_5863713).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863713).length < 2 ^ (prefixWord ++ tailWord_5863713).sum := by decide
  have hdescent : baseEnd_5863713 < baseStart_5863713 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863713) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863720 : List Nat := [2, 1, 5, 1, 4, 1, 2, 1, 6]
def baseStart_5863720 : Nat := 118140960795 + 5863720 * 2 ^ 59
def prefixEnd_5863720 : Nat := 4983230072969 + 3 ^ 40 * 5863720 * 2
def baseEnd_5863720 : Nat := 334545198153544822470361

theorem tailTrace_5863720 : CollatzResearch.WordTrace tailWord_5863720 prefixEnd_5863720 334545198153544822470361 := by
  unfold tailWord_5863720
  simp only [CollatzResearch.WordTrace]
  refine ⟨106933719158375679246054307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142578292211167572328072409 106933719158375679246054307)
  ·
    refine ⟨160400578737563518869081461, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106933719158375679246054307 160400578737563518869081461)
    ·
      refine ⟨15037554256646579893976387, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160400578737563518869081461 15037554256646579893976387)
      ·
        refine ⟨22556331384969869840964581, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15037554256646579893976387 22556331384969869840964581)
        ·
          refine ⟨4229312134681850595180859, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22556331384969869840964581 4229312134681850595180859)
          ·
            refine ⟨6343968202022775892771289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229312134681850595180859 6343968202022775892771289)
            ·
              refine ⟨4757976151517081919578467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6343968202022775892771289 4757976151517081919578467)
              ·
                refine ⟨7136964227275622879367701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4757976151517081919578467 7136964227275622879367701)
                ·
                  refine ⟨334545198153544822470361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7136964227275622879367701 334545198153544822470361)
                  ·
                    rfl

theorem cell23_5863720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 4, 1, 2, 1, 6].length) (baseStart_5863720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863720 prefixEnd_5863720 := by exact prefixLift 5863720
  have htrace : WordTrace (prefixWord ++ tailWord_5863720) baseStart_5863720 baseEnd_5863720 := by
    simpa [prefixWord, tailWord_5863720, baseEnd_5863720] using wordTrace_append hprefix tailTrace_5863720
  have hstable : (prefixWord ++ tailWord_5863720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863720).length < 2 ^ (prefixWord ++ tailWord_5863720).sum := by decide
  have hdescent : baseEnd_5863720 < baseStart_5863720 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863736 : List Nat := [2, 1, 2, 1, 3, 1, 5, 2, 1, 1, 4]
def baseStart_5863736 : Nat := 118140960795 + 5863736 * 2 ^ 59
def prefixEnd_5863736 : Nat := 4983230072969 + 3 ^ 40 * 5863736 * 2
def baseEnd_5863736 : Nat := 3010914999072375339633175

theorem tailTrace_5863736 : CollatzResearch.WordTrace tailWord_5863736 prefixEnd_5863736 3010914999072375339633175 := by
  unfold tailWord_5863736
  simp only [CollatzResearch.WordTrace]
  refine ⟨106934010942346696612345531, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142578681256462262149794041 106934010942346696612345531)
  ·
    refine ⟨160401016413520044918518297, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106934010942346696612345531 160401016413520044918518297)
    ·
      refine ⟨120300762310140033688888723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160401016413520044918518297 120300762310140033688888723)
      ·
        refine ⟨180451143465210050533333085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120300762310140033688888723 180451143465210050533333085)
        ·
          refine ⟨67669178799453768949999907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 180451143465210050533333085 67669178799453768949999907)
          ·
            refine ⟨101503768199180653424999861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67669178799453768949999907 101503768199180653424999861)
            ·
              refine ⟨9515978268673186258593737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101503768199180653424999861 9515978268673186258593737)
              ·
                refine ⟨7136983701504889693945303, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9515978268673186258593737 7136983701504889693945303)
                ·
                  refine ⟨10705475552257334540917955, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7136983701504889693945303 10705475552257334540917955)
                  ·
                    refine ⟨16058213328386001811376933, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10705475552257334540917955 16058213328386001811376933)
                    ·
                      refine ⟨3010914999072375339633175, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16058213328386001811376933 3010914999072375339633175)
                      ·
                        rfl

theorem cell23_5863736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 3, 1, 5, 2, 1, 1, 4].length) (baseStart_5863736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863736 prefixEnd_5863736 := by exact prefixLift 5863736
  have htrace : WordTrace (prefixWord ++ tailWord_5863736) baseStart_5863736 baseEnd_5863736 := by
    simpa [prefixWord, tailWord_5863736, baseEnd_5863736] using wordTrace_append hprefix tailTrace_5863736
  have hstable : (prefixWord ++ tailWord_5863736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863736).length < 2 ^ (prefixWord ++ tailWord_5863736).sum := by decide
  have hdescent : baseEnd_5863736 < baseStart_5863736 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863769 : List Nat := [1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 3]
def baseStart_5863769 : Nat := 118140960795 + 5863769 * 2 ^ 59
def prefixEnd_5863769 : Nat := 4983230072969 + 3 ^ 40 * 5863769 * 2
def baseEnd_5863769 : Nat := 3010931943933973710520523

theorem tailTrace_5863769 : CollatzResearch.WordTrace tailWord_5863769 prefixEnd_5863769 3010931943933973710520523 := by
  unfold tailWord_5863769
  simp only [CollatzResearch.WordTrace]
  refine ⟨213869225493573839860642361, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142579483662382559907094907 213869225493573839860642361)
  ·
    refine ⟨160401919120180379895481771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213869225493573839860642361 160401919120180379895481771)
    ·
      refine ⟨240602878680270569843222657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160401919120180379895481771 240602878680270569843222657)
      ·
        refine ⟨180452159010202927382416993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240602878680270569843222657 180452159010202927382416993)
        ·
          refine ⟨135339119257652195536812745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180452159010202927382416993 135339119257652195536812745)
          ·
            refine ⟨101504339443239146652609559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135339119257652195536812745 101504339443239146652609559)
            ·
              refine ⟨152256509164858719978914339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101504339443239146652609559 152256509164858719978914339)
              ·
                refine ⟨228384763747288079968371509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152256509164858719978914339 228384763747288079968371509)
                ·
                  refine ⟨21411071601308257497034829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 228384763747288079968371509 21411071601308257497034829)
                  ·
                    refine ⟨8029151850490596561388061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21411071601308257497034829 8029151850490596561388061)
                    ·
                      refine ⟨3010931943933973710520523, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8029151850490596561388061 3010931943933973710520523)
                      ·
                        rfl

theorem cell23_5863769_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 2, 1, 1, 5, 3, 3].length) (baseStart_5863769 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863769 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863769 prefixEnd_5863769 := by exact prefixLift 5863769
  have htrace : WordTrace (prefixWord ++ tailWord_5863769) baseStart_5863769 baseEnd_5863769 := by
    simpa [prefixWord, tailWord_5863769, baseEnd_5863769] using wordTrace_append hprefix tailTrace_5863769
  have hstable : (prefixWord ++ tailWord_5863769).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863769).length < 2 ^ (prefixWord ++ tailWord_5863769).sum := by decide
  have hdescent : baseEnd_5863769 < baseStart_5863769 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863769) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863776 : List Nat := [2, 1, 1, 3, 5, 2, 1, 8]
def baseStart_5863776 : Nat := 118140960795 + 5863776 * 2 ^ 59
def prefixEnd_5863776 : Nat := 4983230072969 + 3 ^ 40 * 5863776 * 2
def baseEnd_5863776 : Nat := 111516131048094636412333

theorem tailTrace_5863776 : CollatzResearch.WordTrace tailWord_5863776 prefixEnd_5863776 111516131048094636412333 := by
  unfold tailWord_5863776
  simp only [CollatzResearch.WordTrace]
  refine ⟨106934740402274240028073591, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142579653869698986704098121 106934740402274240028073591)
  ·
    refine ⟨160402110603411360042110387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106934740402274240028073591 160402110603411360042110387)
    ·
      refine ⟨240603165905117040063165581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160402110603411360042110387 240603165905117040063165581)
      ·
        refine ⟨90226187214418890023687093, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240603165905117040063165581 90226187214418890023687093)
        ·
          refine ⟨8458705051351770939720665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90226187214418890023687093 8458705051351770939720665)
          ·
            refine ⟨6344028788513828204790499, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8458705051351770939720665 6344028788513828204790499)
            ·
              refine ⟨9516043182770742307185749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344028788513828204790499 9516043182770742307185749)
              ·
                refine ⟨111516131048094636412333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 9516043182770742307185749 111516131048094636412333)
                ·
                  rfl

theorem cell23_5863776_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 5, 2, 1, 8].length) (baseStart_5863776 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863776 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863776 prefixEnd_5863776 := by exact prefixLift 5863776
  have htrace : WordTrace (prefixWord ++ tailWord_5863776) baseStart_5863776 baseEnd_5863776 := by
    simpa [prefixWord, tailWord_5863776, baseEnd_5863776] using wordTrace_append hprefix tailTrace_5863776
  have hstable : (prefixWord ++ tailWord_5863776).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863776).length < 2 ^ (prefixWord ++ tailWord_5863776).sum := by decide
  have hdescent : baseEnd_5863776 < baseStart_5863776 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863776) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863789 : List Nat := [1, 5, 1, 1, 1, 2, 1, 2, 2, 7]
def baseStart_5863789 : Nat := 118140960795 + 5863789 * 2 ^ 59
def prefixEnd_5863789 : Nat := 4983230072969 + 3 ^ 40 * 5863789 * 2
def baseEnd_5863789 : Nat := 1003647404515687877423477

theorem tailTrace_5863789 : CollatzResearch.WordTrace tailWord_5863789 prefixEnd_5863789 1003647404515687877423477 := by
  unfold tailWord_5863789
  simp only [CollatzResearch.WordTrace]
  refine ⟨213869954953501383276370421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142579969969000922184246947 213869954953501383276370421)
  ·
    refine ⟨20050308276890754682159727, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213869954953501383276370421 20050308276890754682159727)
    ·
      refine ⟨30075462415336132023239591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20050308276890754682159727 30075462415336132023239591)
      ·
        refine ⟨45113193623004198034859387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30075462415336132023239591 45113193623004198034859387)
        ·
          refine ⟨67669790434506297052289081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45113193623004198034859387 67669790434506297052289081)
          ·
            refine ⟨50752342825879722789216811, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67669790434506297052289081 50752342825879722789216811)
            ·
              refine ⟨76128514238819584183825217, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50752342825879722789216811 76128514238819584183825217)
              ·
                refine ⟨57096385679114688137868913, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76128514238819584183825217 57096385679114688137868913)
                ·
                  refine ⟨42822289259336016103401685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57096385679114688137868913 42822289259336016103401685)
                  ·
                    refine ⟨1003647404515687877423477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42822289259336016103401685 1003647404515687877423477)
                    ·
                      rfl

theorem cell23_5863789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 2, 1, 2, 2, 7].length) (baseStart_5863789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863789 prefixEnd_5863789 := by exact prefixLift 5863789
  have htrace : WordTrace (prefixWord ++ tailWord_5863789) baseStart_5863789 baseEnd_5863789 := by
    simpa [prefixWord, tailWord_5863789, baseEnd_5863789] using wordTrace_append hprefix tailTrace_5863789
  have hstable : (prefixWord ++ tailWord_5863789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863789).length < 2 ^ (prefixWord ++ tailWord_5863789).sum := by decide
  have hdescent : baseEnd_5863789 < baseStart_5863789 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863819 : List Nat := [1, 1, 1, 1, 4, 4, 1, 2, 2, 6]
def baseStart_5863819 : Nat := 118140960795 + 5863819 * 2 ^ 59
def prefixEnd_5863819 : Nat := 4983230072969 + 3 ^ 40 * 5863819 * 2
def baseEnd_5863819 : Nat := 1003652539322232838298431

theorem tailTrace_5863819 : CollatzResearch.WordTrace tailWord_5863819 prefixEnd_5863819 1003652539322232838298431 := by
  unfold tailWord_5863819
  simp only [CollatzResearch.WordTrace]
  refine ⟨213871049143392698399962511, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142580699428928465599975007 213871049143392698399962511)
  ·
    refine ⟨320806573715089047599943767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213871049143392698399962511 320806573715089047599943767)
    ·
      refine ⟨481209860572633571399915651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320806573715089047599943767 481209860572633571399915651)
      ·
        refine ⟨721814790858950357099873477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481209860572633571399915651 721814790858950357099873477)
        ·
          refine ⟨135340273286053191956226277, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 721814790858950357099873477 135340273286053191956226277)
          ·
            refine ⟨25376301241134973491792427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135340273286053191956226277 25376301241134973491792427)
            ·
              refine ⟨38064451861702460237688641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25376301241134973491792427 38064451861702460237688641)
              ·
                refine ⟨28548338896276845178266481, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38064451861702460237688641 28548338896276845178266481)
                ·
                  refine ⟨21411254172207633883699861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28548338896276845178266481 21411254172207633883699861)
                  ·
                    refine ⟨1003652539322232838298431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21411254172207633883699861 1003652539322232838298431)
                    ·
                      rfl

theorem cell23_5863819_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 4, 1, 2, 2, 6].length) (baseStart_5863819 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863819 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863819 prefixEnd_5863819 := by exact prefixLift 5863819
  have htrace : WordTrace (prefixWord ++ tailWord_5863819) baseStart_5863819 baseEnd_5863819 := by
    simpa [prefixWord, tailWord_5863819, baseEnd_5863819] using wordTrace_append hprefix tailTrace_5863819
  have hstable : (prefixWord ++ tailWord_5863819).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863819).length < 2 ^ (prefixWord ++ tailWord_5863819).sum := by decide
  have hdescent : baseEnd_5863819 < baseStart_5863819 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863819) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863820 : List Nat := [2, 2, 1, 2, 1, 6, 1, 2, 2, 1, 3]
def baseStart_5863820 : Nat := 118140960795 + 5863820 * 2 ^ 59
def prefixEnd_5863820 : Nat := 4983230072969 + 3 ^ 40 * 5863820 * 2
def baseEnd_5863820 : Nat := 3010958131447353010982789

theorem tailTrace_5863820 : CollatzResearch.WordTrace tailWord_5863820 prefixEnd_5863820 3010958131447353010982789 := by
  unfold tailWord_5863820
  simp only [CollatzResearch.WordTrace]
  refine ⟨106935542808194537785374457, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142580723744259383713832609 106935542808194537785374457)
  ·
    refine ⟨80201657106145903339030843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106935542808194537785374457 80201657106145903339030843)
    ·
      refine ⟨120302485659218855008546265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80201657106145903339030843 120302485659218855008546265)
      ·
        refine ⟨90226864244414141256409699, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120302485659218855008546265 90226864244414141256409699)
        ·
          refine ⟨135340296366621211884614549, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90226864244414141256409699 135340296366621211884614549)
          ·
            refine ⟨6344076392185369307091307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135340296366621211884614549 6344076392185369307091307)
            ·
              refine ⟨9516114588278053960636961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344076392185369307091307 9516114588278053960636961)
              ·
                refine ⟨7137085941208540470477721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9516114588278053960636961 7137085941208540470477721)
                ·
                  refine ⟨5352814455906405352858291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7137085941208540470477721 5352814455906405352858291)
                  ·
                    refine ⟨8029221683859608029287437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5352814455906405352858291 8029221683859608029287437)
                    ·
                      refine ⟨3010958131447353010982789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8029221683859608029287437 3010958131447353010982789)
                      ·
                        rfl

theorem cell23_5863820_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 6, 1, 2, 2, 1, 3].length) (baseStart_5863820 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863820 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863820 prefixEnd_5863820 := by exact prefixLift 5863820
  have htrace : WordTrace (prefixWord ++ tailWord_5863820) baseStart_5863820 baseEnd_5863820 := by
    simpa [prefixWord, tailWord_5863820, baseEnd_5863820] using wordTrace_append hprefix tailTrace_5863820
  have hstable : (prefixWord ++ tailWord_5863820).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863820).length < 2 ^ (prefixWord ++ tailWord_5863820).sum := by decide
  have hdescent : baseEnd_5863820 < baseStart_5863820 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863820) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863829 : List Nat := [1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 5]
def baseStart_5863829 : Nat := 118140960795 + 5863829 * 2 ^ 59
def prefixEnd_5863829 : Nat := 4983230072969 + 3 ^ 40 * 5863829 * 2
def baseEnd_5863829 : Nat := 3010962752773243475770247

theorem tailTrace_5863829 : CollatzResearch.WordTrace tailWord_5863829 prefixEnd_5863829 3010962752773243475770247 := by
  unfold tailWord_5863829
  simp only [CollatzResearch.WordTrace]
  refine ⟨213871413873356470107826541, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142580942582237646738551027 213871413873356470107826541)
  ·
    refine ⟨80201780202508676290434953, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213871413873356470107826541 80201780202508676290434953)
    ·
      refine ⟨60151335151881507217826215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80201780202508676290434953 60151335151881507217826215)
      ·
        refine ⟨90227002727822260826739323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60151335151881507217826215 90227002727822260826739323)
        ·
          refine ⟨135340504091733391240108985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90227002727822260826739323 135340504091733391240108985)
          ·
            refine ⟨101505378068800043430081739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135340504091733391240108985 101505378068800043430081739)
            ·
              refine ⟨152258067103200065145122609, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101505378068800043430081739 152258067103200065145122609)
              ·
                refine ⟨114193550327400048858841957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152258067103200065145122609 114193550327400048858841957)
                ·
                  refine ⟨21411290686387509161032867, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 114193550327400048858841957 21411290686387509161032867)
                  ·
                    refine ⟨32116936029581263741549301, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21411290686387509161032867 32116936029581263741549301)
                    ·
                      refine ⟨3010962752773243475770247, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32116936029581263741549301 3010962752773243475770247)
                      ·
                        rfl

theorem cell23_5863829_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 2, 1, 2, 4, 1, 5].length) (baseStart_5863829 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863829 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863829 prefixEnd_5863829 := by exact prefixLift 5863829
  have htrace : WordTrace (prefixWord ++ tailWord_5863829) baseStart_5863829 baseEnd_5863829 := by
    simpa [prefixWord, tailWord_5863829, baseEnd_5863829] using wordTrace_append hprefix tailTrace_5863829
  have hstable : (prefixWord ++ tailWord_5863829).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863829).length < 2 ^ (prefixWord ++ tailWord_5863829).sum := by decide
  have hdescent : baseEnd_5863829 < baseStart_5863829 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863829) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863837 : List Nat := [1, 4, 2, 1, 4, 1, 3, 1, 2, 1, 3]
def baseStart_5863837 : Nat := 118140960795 + 5863837 * 2 ^ 59
def prefixEnd_5863837 : Nat := 4983230072969 + 3 ^ 40 * 5863837 * 2
def baseEnd_5863837 : Nat := 3010966860618479444470211

theorem tailTrace_5863837 : CollatzResearch.WordTrace tailWord_5863837 prefixEnd_5863837 3010966860618479444470211 := by
  unfold tailWord_5863837
  simp only [CollatzResearch.WordTrace]
  refine ⟨213871705657327487474117765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142581137104884991649411843 213871705657327487474117765)
  ·
    refine ⟨40100944810748903901397081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213871705657327487474117765 40100944810748903901397081)
    ·
      refine ⟨30075708608061677926047811, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40100944810748903901397081 30075708608061677926047811)
      ·
        refine ⟨45113562912092516889071717, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30075708608061677926047811 45113562912092516889071717)
        ·
          refine ⟨8458793046017346916700947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45113562912092516889071717 8458793046017346916700947)
          ·
            refine ⟨12688189569026020375051421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8458793046017346916700947 12688189569026020375051421)
            ·
              refine ⟨4758071088384757640644283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12688189569026020375051421 4758071088384757640644283)
              ·
                refine ⟨7137106632577136460966425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758071088384757640644283 7137106632577136460966425)
                ·
                  refine ⟨5352829974432852345724819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7137106632577136460966425 5352829974432852345724819)
                  ·
                    refine ⟨8029244961649278518587229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5352829974432852345724819 8029244961649278518587229)
                    ·
                      refine ⟨3010966860618479444470211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8029244961649278518587229 3010966860618479444470211)
                      ·
                        rfl

theorem cell23_5863837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 4, 1, 3, 1, 2, 1, 3].length) (baseStart_5863837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863837 prefixEnd_5863837 := by exact prefixLift 5863837
  have htrace : WordTrace (prefixWord ++ tailWord_5863837) baseStart_5863837 baseEnd_5863837 := by
    simpa [prefixWord, tailWord_5863837, baseEnd_5863837] using wordTrace_append hprefix tailTrace_5863837
  have hstable : (prefixWord ++ tailWord_5863837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863837).length < 2 ^ (prefixWord ++ tailWord_5863837).sum := by decide
  have hdescent : baseEnd_5863837 < baseStart_5863837 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863843 : List Nat := [1, 1, 1, 4, 1, 4, 3, 1, 1, 4, 2]
def baseStart_5863843 : Nat := 118140960795 + 5863843 * 2 ^ 59
def prefixEnd_5863843 : Nat := 4983230072969 + 3 ^ 40 * 5863843 * 2
def baseEnd_5863843 : Nat := 3010969941502406420995183

theorem tailTrace_5863843 : CollatzResearch.WordTrace tailWord_5863843 prefixEnd_5863843 3010969941502406420995183 := by
  unfold tailWord_5863843
  simp only [CollatzResearch.WordTrace]
  refine ⟨213871924495305750498836183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142581282996870500332557455 213871924495305750498836183)
  ·
    refine ⟨320807886742958625748254275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213871924495305750498836183 320807886742958625748254275)
    ·
      refine ⟨481211830114437938622381413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320807886742958625748254275 481211830114437938622381413)
      ·
        refine ⟨90227218146457113491696515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 481211830114437938622381413 90227218146457113491696515)
        ·
          refine ⟨135340827219685670237544773, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90227218146457113491696515 135340827219685670237544773)
          ·
            refine ⟨25376405103691063169539645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135340827219685670237544773 25376405103691063169539645)
            ·
              refine ⟨9516151913884148688577367, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25376405103691063169539645 9516151913884148688577367)
              ·
                refine ⟨14274227870826223032866051, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516151913884148688577367 14274227870826223032866051)
                ·
                  refine ⟨21411341806239334549299077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14274227870826223032866051 21411341806239334549299077)
                  ·
                    refine ⟨4014626588669875227993577, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21411341806239334549299077 4014626588669875227993577)
                    ·
                      refine ⟨3010969941502406420995183, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014626588669875227993577 3010969941502406420995183)
                      ·
                        rfl

theorem cell23_5863843_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 4, 3, 1, 1, 4, 2].length) (baseStart_5863843 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863843 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863843 prefixEnd_5863843 := by exact prefixLift 5863843
  have htrace : WordTrace (prefixWord ++ tailWord_5863843) baseStart_5863843 baseEnd_5863843 := by
    simpa [prefixWord, tailWord_5863843, baseEnd_5863843] using wordTrace_append hprefix tailTrace_5863843
  have hstable : (prefixWord ++ tailWord_5863843).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863843).length < 2 ^ (prefixWord ++ tailWord_5863843).sum := by decide
  have hdescent : baseEnd_5863843 < baseStart_5863843 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863843) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863933 : List Nat := [1, 4, 1, 1, 1, 3, 2, 2, 2, 4, 2]
def baseStart_5863933 : Nat := 118140960795 + 5863933 * 2 ^ 59
def prefixEnd_5863933 : Nat := 4983230072969 + 3 ^ 40 * 5863933 * 2
def baseEnd_5863933 : Nat := 3011016154761311068869769

theorem tailTrace_5863933 : CollatzResearch.WordTrace tailWord_5863933 prefixEnd_5863933 3011016154761311068869769 := by
  unfold tailWord_5863933
  simp only [CollatzResearch.WordTrace]
  refine ⟨213875207064979695869612453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142583471376653130579741635 213875207064979695869612453)
  ·
    refine ⟨40101601324683692975552335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213875207064979695869612453 40101601324683692975552335)
    ·
      refine ⟨60152401987025539463328503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40101601324683692975552335 60152401987025539463328503)
      ·
        refine ⟨90228602980538309194992755, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60152401987025539463328503 90228602980538309194992755)
        ·
          refine ⟨135342904470807463792489133, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90228602980538309194992755 135342904470807463792489133)
          ·
            refine ⟨50753589176552798922183425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135342904470807463792489133 50753589176552798922183425)
            ·
              refine ⟨38065191882414599191637569, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50753589176552798922183425 38065191882414599191637569)
              ·
                refine ⟨28548893911810949393728177, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38065191882414599191637569 28548893911810949393728177)
                ·
                  refine ⟨21411670433858212045296133, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28548893911810949393728177 21411670433858212045296133)
                  ·
                    refine ⟨4014688206348414758493025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21411670433858212045296133 4014688206348414758493025)
                    ·
                      refine ⟨3011016154761311068869769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014688206348414758493025 3011016154761311068869769)
                      ·
                        rfl

theorem cell23_5863933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 2, 2, 4, 2].length) (baseStart_5863933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863933 prefixEnd_5863933 := by exact prefixLift 5863933
  have htrace : WordTrace (prefixWord ++ tailWord_5863933) baseStart_5863933 baseEnd_5863933 := by
    simpa [prefixWord, tailWord_5863933, baseEnd_5863933] using wordTrace_append hprefix tailTrace_5863933
  have hstable : (prefixWord ++ tailWord_5863933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863933).length < 2 ^ (prefixWord ++ tailWord_5863933).sum := by decide
  have hdescent : baseEnd_5863933 < baseStart_5863933 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863950 : List Nat := [4, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2]
def baseStart_5863950 : Nat := 118140960795 + 5863950 * 2 ^ 59
def prefixEnd_5863950 : Nat := 4983230072969 + 3 ^ 40 * 5863950 * 2
def baseEnd_5863950 : Nat := 3011024883932437502357191

theorem tailTrace_5863950 : CollatzResearch.WordTrace tailWord_5863950 prefixEnd_5863950 3011024883932437502357191 := by
  unfold tailWord_5863950
  simp only [CollatzResearch.WordTrace]
  refine ⟨26734478388239763471622663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142583884737278738515320869 26734478388239763471622663)
  ·
    refine ⟨40101717582359645207433995, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26734478388239763471622663 40101717582359645207433995)
    ·
      refine ⟨60152576373539467811150993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40101717582359645207433995 60152576373539467811150993)
      ·
        refine ⟨45114432280154600858363245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60152576373539467811150993 45114432280154600858363245)
        ·
          refine ⟨16917912105057975321886217, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45114432280154600858363245 16917912105057975321886217)
          ·
            refine ⟨12688434078793481491414663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16917912105057975321886217 12688434078793481491414663)
            ·
              refine ⟨19032651118190222237121995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12688434078793481491414663 19032651118190222237121995)
              ·
                refine ⟨28548976677285333355682993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19032651118190222237121995 28548976677285333355682993)
                ·
                  refine ⟨21411732507964000016762245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28548976677285333355682993 21411732507964000016762245)
                  ·
                    refine ⟨4014699845243250003142921, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21411732507964000016762245 4014699845243250003142921)
                    ·
                      refine ⟨3011024883932437502357191, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014699845243250003142921 3011024883932437502357191)
                      ·
                        rfl

theorem cell23_5863950_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 1, 2, 4, 2].length) (baseStart_5863950 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863950 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863950 prefixEnd_5863950 := by exact prefixLift 5863950
  have htrace : WordTrace (prefixWord ++ tailWord_5863950) baseStart_5863950 baseEnd_5863950 := by
    simpa [prefixWord, tailWord_5863950, baseEnd_5863950] using wordTrace_append hprefix tailTrace_5863950
  have hstable : (prefixWord ++ tailWord_5863950).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863950).length < 2 ^ (prefixWord ++ tailWord_5863950).sum := by decide
  have hdescent : baseEnd_5863950 < baseStart_5863950 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863950) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5863990 : List Nat := [5, 1, 2, 1, 2, 1, 3, 2, 6]
def baseStart_5863990 : Nat := 118140960795 + 5863990 * 2 ^ 59
def prefixEnd_5863990 : Nat := 4983230072969 + 3 ^ 40 * 5863990 * 2
def baseEnd_5863990 : Nat := 334560602573179705095223

theorem tailTrace_5863990 : CollatzResearch.WordTrace tailWord_5863990 prefixEnd_5863990 334560602573179705095223 := by
  unfold tailWord_5863990
  simp only [CollatzResearch.WordTrace]
  refine ⟨13367330376610824662777339, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142584857350515463069624949 13367330376610824662777339)
  ·
    refine ⟨20050995564916236994166009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 13367330376610824662777339 20050995564916236994166009)
    ·
      refine ⟨15038246673687177745624507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20050995564916236994166009 15038246673687177745624507)
      ·
        refine ⟨22557370010530766618436761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15038246673687177745624507 22557370010530766618436761)
        ·
          refine ⟨16918027507898074963827571, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22557370010530766618436761 16918027507898074963827571)
          ·
            refine ⟨25377041261847112445741357, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16918027507898074963827571 25377041261847112445741357)
            ·
              refine ⟨9516390473192667167153009, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25377041261847112445741357 9516390473192667167153009)
              ·
                refine ⟨7137292854894500375364757, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9516390473192667167153009 7137292854894500375364757)
                ·
                  refine ⟨334560602573179705095223, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7137292854894500375364757 334560602573179705095223)
                  ·
                    rfl

theorem cell23_5863990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 1, 2, 1, 2, 1, 3, 2, 6].length) (baseStart_5863990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5863990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5863990 prefixEnd_5863990 := by exact prefixLift 5863990
  have htrace : WordTrace (prefixWord ++ tailWord_5863990) baseStart_5863990 baseEnd_5863990 := by
    simpa [prefixWord, tailWord_5863990, baseEnd_5863990] using wordTrace_append hprefix tailTrace_5863990
  have hstable : (prefixWord ++ tailWord_5863990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5863990).length < 2 ^ (prefixWord ++ tailWord_5863990).sum := by decide
  have hdescent : baseEnd_5863990 < baseStart_5863990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5863990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864016 : List Nat := [2, 1, 1, 1, 1, 3, 2, 5, 1, 6]
def baseStart_5864016 : Nat := 118140960795 + 5864016 * 2 ^ 59
def prefixEnd_5864016 : Nat := 4983230072969 + 3 ^ 40 * 5864016 * 2
def baseEnd_5864016 : Nat := 1003686257885211414710629

theorem tailTrace_5864016 : CollatzResearch.WordTrace tailWord_5864016 prefixEnd_5864016 1003686257885211414710629 := by
  unfold tailWord_5864016
  simp only [CollatzResearch.WordTrace]
  refine ⟨106939117161839500522441951, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142585489549119334029922601 106939117161839500522441951)
  ·
    refine ⟨160408675742759250783662927, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106939117161839500522441951 160408675742759250783662927)
    ·
      refine ⟨240613013614138876175494391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160408675742759250783662927 240613013614138876175494391)
      ·
        refine ⟨360919520421208314263241587, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240613013614138876175494391 360919520421208314263241587)
        ·
          refine ⟨541379280631812471394862381, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360919520421208314263241587 541379280631812471394862381)
          ·
            refine ⟨203017230236929676773073393, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 541379280631812471394862381 203017230236929676773073393)
            ·
              refine ⟨152262922677697257579805045, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203017230236929676773073393 152262922677697257579805045)
              ·
                refine ⟨14274649001034117898106723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152262922677697257579805045 14274649001034117898106723)
                ·
                  refine ⟨21411973501551176847160085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14274649001034117898106723 21411973501551176847160085)
                  ·
                    refine ⟨1003686257885211414710629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21411973501551176847160085 1003686257885211414710629)
                    ·
                      rfl

theorem cell23_5864016_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 5, 1, 6].length) (baseStart_5864016 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864016 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864016 prefixEnd_5864016 := by exact prefixLift 5864016
  have htrace : WordTrace (prefixWord ++ tailWord_5864016) baseStart_5864016 baseEnd_5864016 := by
    simpa [prefixWord, tailWord_5864016, baseEnd_5864016] using wordTrace_append hprefix tailTrace_5864016
  have hstable : (prefixWord ++ tailWord_5864016).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864016).length < 2 ^ (prefixWord ++ tailWord_5864016).sum := by decide
  have hdescent : baseEnd_5864016 < baseStart_5864016 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864016) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864020 : List Nat := [2, 4, 1, 1, 1, 4, 2, 2, 1, 5]
def baseStart_5864020 : Nat := 118140960795 + 5864020 * 2 ^ 59
def prefixEnd_5864020 : Nat := 4983230072969 + 3 ^ 40 * 5864020 * 2
def baseEnd_5864020 : Nat := 1003686942526084076160623

theorem tailTrace_5864020 : CollatzResearch.WordTrace tailWord_5864020 prefixEnd_5864020 1003686942526084076160623 := by
  unfold tailWord_5864020
  simp only [CollatzResearch.WordTrace]
  refine ⟨106939190107832254864014757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142585586810443006485353009 106939190107832254864014757)
  ·
    refine ⟨20051098145218547787002767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 106939190107832254864014757 20051098145218547787002767)
    ·
      refine ⟨30076647217827821680504151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20051098145218547787002767 30076647217827821680504151)
      ·
        refine ⟨45114970826741732520756227, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30076647217827821680504151 45114970826741732520756227)
        ·
          refine ⟨67672456240112598781134341, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45114970826741732520756227 67672456240112598781134341)
          ·
            refine ⟨12688585545021112271462689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67672456240112598781134341 12688585545021112271462689)
            ·
              refine ⟨9516439158765834203597017, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12688585545021112271462689 9516439158765834203597017)
              ·
                refine ⟨7137329369074375652697763, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9516439158765834203597017 7137329369074375652697763)
                ·
                  refine ⟨10705994053611563479046645, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7137329369074375652697763 10705994053611563479046645)
                  ·
                    refine ⟨1003686942526084076160623, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10705994053611563479046645 1003686942526084076160623)
                    ·
                      rfl

theorem cell23_5864020_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 1, 4, 2, 2, 1, 5].length) (baseStart_5864020 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864020 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864020 prefixEnd_5864020 := by exact prefixLift 5864020
  have htrace : WordTrace (prefixWord ++ tailWord_5864020) baseStart_5864020 baseEnd_5864020 := by
    simpa [prefixWord, tailWord_5864020, baseEnd_5864020] using wordTrace_append hprefix tailTrace_5864020
  have hstable : (prefixWord ++ tailWord_5864020).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864020).length < 2 ^ (prefixWord ++ tailWord_5864020).sum := by decide
  have hdescent : baseEnd_5864020 < baseStart_5864020 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864020) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864023 : List Nat := [1, 1, 3, 2, 2, 2, 1, 1, 2, 6, 2]
def baseStart_5864023 : Nat := 118140960795 + 5864023 * 2 ^ 59
def prefixEnd_5864023 : Nat := 4983230072969 + 3 ^ 40 * 5864023 * 2
def baseEnd_5864023 : Nat := 3011062368020215716744355

theorem tailTrace_5864023 : CollatzResearch.WordTrace tailWord_5864023 prefixEnd_5864023 3011062368020215716744355 := by
  unfold tailWord_5864023
  simp only [CollatzResearch.WordTrace]
  refine ⟨213878489634653641240388723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142585659756435760826925815 213878489634653641240388723)
  ·
    refine ⟨320817734451980461860583085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213878489634653641240388723 320817734451980461860583085)
    ·
      refine ⟨120306650419492673197718657, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320817734451980461860583085 120306650419492673197718657)
      ·
        refine ⟨90229987814619504898288993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120306650419492673197718657 90229987814619504898288993)
        ·
          refine ⟨67672490860964628673716745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90229987814619504898288993 67672490860964628673716745)
          ·
            refine ⟨50754368145723471505287559, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67672490860964628673716745 50754368145723471505287559)
            ·
              refine ⟨76131552218585207257931339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50754368145723471505287559 76131552218585207257931339)
              ·
                refine ⟨114197328327877810886897009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76131552218585207257931339 114197328327877810886897009)
                ·
                  refine ⟨85647996245908358165172757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114197328327877810886897009 85647996245908358165172757)
                  ·
                    refine ⟨4014749824026954288992473, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85647996245908358165172757 4014749824026954288992473)
                    ·
                      refine ⟨3011062368020215716744355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014749824026954288992473 3011062368020215716744355)
                      ·
                        rfl

theorem cell23_5864023_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 2, 1, 1, 2, 6, 2].length) (baseStart_5864023 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864023 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864023 prefixEnd_5864023 := by exact prefixLift 5864023
  have htrace : WordTrace (prefixWord ++ tailWord_5864023) baseStart_5864023 baseEnd_5864023 := by
    simpa [prefixWord, tailWord_5864023, baseEnd_5864023] using wordTrace_append hprefix tailTrace_5864023
  have hstable : (prefixWord ++ tailWord_5864023).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864023).length < 2 ^ (prefixWord ++ tailWord_5864023).sum := by decide
  have hdescent : baseEnd_5864023 < baseStart_5864023 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864023) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864033 : List Nat := [1, 2, 3, 1, 1, 4, 1, 2, 4, 4]
def baseStart_5864033 : Nat := 118140960795 + 5864033 * 2 ^ 59
def prefixEnd_5864033 : Nat := 4983230072969 + 3 ^ 40 * 5864033 * 2
def baseEnd_5864033 : Nat := 1003689167608920225873103

theorem tailTrace_5864033 : CollatzResearch.WordTrace tailWord_5864033 prefixEnd_5864033 1003689167608920225873103 := by
  unfold tailWord_5864033
  simp only [CollatzResearch.WordTrace]
  refine ⟨213878854364617412948252753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142585902909744941965501835 213878854364617412948252753)
  ·
    refine ⟨160409140773463059711189565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213878854364617412948252753 160409140773463059711189565)
    ·
      refine ⟨60153427790048647391696087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160409140773463059711189565 60153427790048647391696087)
      ·
        refine ⟨90230141685072971087544131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60153427790048647391696087 90230141685072971087544131)
        ·
          refine ⟨135345212527609456631316197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90230141685072971087544131 135345212527609456631316197)
          ·
            refine ⟨25377227348926773118371787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135345212527609456631316197 25377227348926773118371787)
            ·
              refine ⟨38065841023390159677557681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25377227348926773118371787 38065841023390159677557681)
              ·
                refine ⟨28549380767542619758168261, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38065841023390159677557681 28549380767542619758168261)
                ·
                  refine ⟨5353008893914241204656549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28549380767542619758168261 5353008893914241204656549)
                  ·
                    refine ⟨1003689167608920225873103, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5353008893914241204656549 1003689167608920225873103)
                    ·
                      rfl

theorem cell23_5864033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 4, 1, 2, 4, 4].length) (baseStart_5864033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864033 prefixEnd_5864033 := by exact prefixLift 5864033
  have htrace : WordTrace (prefixWord ++ tailWord_5864033) baseStart_5864033 baseEnd_5864033 := by
    simpa [prefixWord, tailWord_5864033, baseEnd_5864033] using wordTrace_append hprefix tailTrace_5864033
  have hstable : (prefixWord ++ tailWord_5864033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864033).length < 2 ^ (prefixWord ++ tailWord_5864033).sum := by decide
  have hdescent : baseEnd_5864033 < baseStart_5864033 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864057 : List Nat := [1, 2, 1, 3, 3, 2, 3, 1, 3, 2, 2]
def baseStart_5864057 : Nat := 118140960795 + 5864057 * 2 ^ 59
def prefixEnd_5864057 : Nat := 4983230072969 + 3 ^ 40 * 5864057 * 2
def baseEnd_5864057 : Nat := 3011079826362468583719199

theorem tailTrace_5864057 : CollatzResearch.WordTrace tailWord_5864057 prefixEnd_5864057 3011079826362468583719199 := by
  unfold tailWord_5864057
  simp only [CollatzResearch.WordTrace]
  refine ⟨213879729716530465047126425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142586486477686976698084283 213879729716530465047126425)
  ·
    refine ⟨160409797287397848785344819, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213879729716530465047126425 160409797287397848785344819)
    ·
      refine ⟨240614695931096773178017229, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160409797287397848785344819 240614695931096773178017229)
      ·
        refine ⟨90230510974161289941756461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240614695931096773178017229 90230510974161289941756461)
        ·
          refine ⟨33836441615310483728158673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90230510974161289941756461 33836441615310483728158673)
          ·
            refine ⟨25377331211482862796119005, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33836441615310483728158673 25377331211482862796119005)
            ·
              refine ⟨9516499204306073548544627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25377331211482862796119005 9516499204306073548544627)
              ·
                refine ⟨14274748806459110322816941, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516499204306073548544627 14274748806459110322816941)
                ·
                  refine ⟨5353030802422166371056353, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14274748806459110322816941 5353030802422166371056353)
                  ·
                    refine ⟨4014773101816624778292265, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5353030802422166371056353 4014773101816624778292265)
                    ·
                      refine ⟨3011079826362468583719199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014773101816624778292265 3011079826362468583719199)
                      ·
                        rfl

theorem cell23_5864057_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 3, 2, 3, 1, 3, 2, 2].length) (baseStart_5864057 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864057 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864057 prefixEnd_5864057 := by exact prefixLift 5864057
  have htrace : WordTrace (prefixWord ++ tailWord_5864057) baseStart_5864057 baseEnd_5864057 := by
    simpa [prefixWord, tailWord_5864057, baseEnd_5864057] using wordTrace_append hprefix tailTrace_5864057
  have hstable : (prefixWord ++ tailWord_5864057).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864057).length < 2 ^ (prefixWord ++ tailWord_5864057).sum := by decide
  have hdescent : baseEnd_5864057 < baseStart_5864057 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864057) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864073 : List Nat := [1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 3]
def baseStart_5864073 : Nat := 118140960795 + 5864073 * 2 ^ 59
def prefixEnd_5864073 : Nat := 4983230072969 + 3 ^ 40 * 5864073 * 2
def baseEnd_5864073 : Nat := 3011088042052940521119125

theorem tailTrace_5864073 : CollatzResearch.WordTrace tailWord_5864073 prefixEnd_5864073 3011088042052940521119125 := by
  unfold tailWord_5864073
  simp only [CollatzResearch.WordTrace]
  refine ⟨213880313284472499779708873, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142586875522981666519805915 213880313284472499779708873)
  ·
    refine ⟨160410234963354374834781655, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213880313284472499779708873 160410234963354374834781655)
    ·
      refine ⟨240615352445031562252172483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160410234963354374834781655 240615352445031562252172483)
      ·
        refine ⟨360923028667547343378258725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240615352445031562252172483 360923028667547343378258725)
        ·
          refine ⟨67673067875165126883423511, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 360923028667547343378258725 67673067875165126883423511)
          ·
            refine ⟨101509601812747690325135267, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67673067875165126883423511 101509601812747690325135267)
            ·
              refine ⟨152264402719121535487702901, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101509601812747690325135267 152264402719121535487702901)
              ·
                refine ⟨14274787754917643951972147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152264402719121535487702901 14274787754917643951972147)
                ·
                  refine ⟨21412181632376465927958221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14274787754917643951972147 21412181632376465927958221)
                  ·
                    refine ⟨8029568112141174722984333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21412181632376465927958221 8029568112141174722984333)
                    ·
                      refine ⟨3011088042052940521119125, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8029568112141174722984333 3011088042052940521119125)
                      ·
                        rfl

theorem cell23_5864073_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 1, 1, 5, 1, 3, 3].length) (baseStart_5864073 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864073 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864073 prefixEnd_5864073 := by exact prefixLift 5864073
  have htrace : WordTrace (prefixWord ++ tailWord_5864073) baseStart_5864073 baseEnd_5864073 := by
    simpa [prefixWord, tailWord_5864073, baseEnd_5864073] using wordTrace_append hprefix tailTrace_5864073
  have hstable : (prefixWord ++ tailWord_5864073).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864073).length < 2 ^ (prefixWord ++ tailWord_5864073).sum := by decide
  have hdescent : baseEnd_5864073 < baseStart_5864073 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864073) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864074 : List Nat := [3, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4]
def baseStart_5864074 : Nat := 118140960795 + 5864074 * 2 ^ 59
def prefixEnd_5864074 : Nat := 4983230072969 + 3 ^ 40 * 5864074 * 2
def baseEnd_5864074 : Nat := 3011088555533595017206621

theorem tailTrace_5864074 : CollatzResearch.WordTrace tailWord_5864074 prefixEnd_5864074 3011088555533595017206621 := by
  unfold tailWord_5864074
  simp only [CollatzResearch.WordTrace]
  refine ⟨53470087439367219237623819, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142586899838312584633663517 53470087439367219237623819)
  ·
    refine ⟨80205131159050828856435729, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53470087439367219237623819 80205131159050828856435729)
    ·
      refine ⟨60153848369288121642326797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80205131159050828856435729 60153848369288121642326797)
      ·
        refine ⟨22557693138483045615872549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60153848369288121642326797 22557693138483045615872549)
        ·
          refine ⟨4229567463465571052976103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 22557693138483045615872549 4229567463465571052976103)
          ·
            refine ⟨6344351195198356579464155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4229567463465571052976103 6344351195198356579464155)
            ·
              refine ⟨9516526792797534869196233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344351195198356579464155 9516526792797534869196233)
              ·
                refine ⟨7137395094598151151897175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9516526792797534869196233 7137395094598151151897175)
                ·
                  refine ⟨10706092641897226727845763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7137395094598151151897175 10706092641897226727845763)
                  ·
                    refine ⟨16059138962845840091768645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10706092641897226727845763 16059138962845840091768645)
                    ·
                      refine ⟨3011088555533595017206621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16059138962845840091768645 3011088555533595017206621)
                      ·
                        rfl

theorem cell23_5864074_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 4, 1, 1, 2, 1, 1, 4].length) (baseStart_5864074 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864074 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864074 prefixEnd_5864074 := by exact prefixLift 5864074
  have htrace : WordTrace (prefixWord ++ tailWord_5864074) baseStart_5864074 baseEnd_5864074 := by
    simpa [prefixWord, tailWord_5864074, baseEnd_5864074] using wordTrace_append hprefix tailTrace_5864074
  have hstable : (prefixWord ++ tailWord_5864074).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864074).length < 2 ^ (prefixWord ++ tailWord_5864074).sum := by decide
  have hdescent : baseEnd_5864074 < baseStart_5864074 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864074) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864076 : List Nat := [2, 2, 1, 2, 1, 1, 2, 1, 4, 7]
def baseStart_5864076 : Nat := 118140960795 + 5864076 * 2 ^ 59
def prefixEnd_5864076 : Nat := 4983230072969 + 3 ^ 40 * 5864076 * 2
def baseEnd_5864076 : Nat := 1003696527498301336460537

theorem tailTrace_5864076 : CollatzResearch.WordTrace tailWord_5864076 prefixEnd_5864076 1003696527498301336460537 := by
  unfold tailWord_5864076
  simp only [CollatzResearch.WordTrace]
  refine ⟨106940211351730815646034041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142586948468974420861378721 106940211351730815646034041)
  ·
    refine ⟨80205158513798111734525531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106940211351730815646034041 80205158513798111734525531)
    ·
      refine ⟨120307737770697167601788297, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80205158513798111734525531 120307737770697167601788297)
      ·
        refine ⟨90230803328022875701341223, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120307737770697167601788297 90230803328022875701341223)
        ·
          refine ⟨135346204992034313552011835, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90230803328022875701341223 135346204992034313552011835)
          ·
            refine ⟨203019307488051470328017753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135346204992034313552011835 203019307488051470328017753)
            ·
              refine ⟨152264480616038602746013315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203019307488051470328017753 152264480616038602746013315)
              ·
                refine ⟨228396720924057904119019973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152264480616038602746013315 228396720924057904119019973)
                ·
                  refine ⟨42824385173260857022316245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 228396720924057904119019973 42824385173260857022316245)
                  ·
                    refine ⟨1003696527498301336460537, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42824385173260857022316245 1003696527498301336460537)
                    ·
                      rfl

theorem cell23_5864076_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 4, 7].length) (baseStart_5864076 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864076 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864076 prefixEnd_5864076 := by exact prefixLift 5864076
  have htrace : WordTrace (prefixWord ++ tailWord_5864076) baseStart_5864076 baseEnd_5864076 := by
    simpa [prefixWord, tailWord_5864076, baseEnd_5864076] using wordTrace_append hprefix tailTrace_5864076
  have hstable : (prefixWord ++ tailWord_5864076).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864076).length < 2 ^ (prefixWord ++ tailWord_5864076).sum := by decide
  have hdescent : baseEnd_5864076 < baseStart_5864076 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864076) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864083 : List Nat := [1, 1, 1, 2, 1, 2, 2, 2, 2, 7, 2]
def baseStart_5864083 : Nat := 118140960795 + 5864083 * 2 ^ 59
def prefixEnd_5864083 : Nat := 4983230072969 + 3 ^ 40 * 5864083 * 2
def baseEnd_5864083 : Nat := 3011093176859485481994079

theorem tailTrace_5864083 : CollatzResearch.WordTrace tailWord_5864083 prefixEnd_5864083 3011093176859485481994079 := by
  unfold tailWord_5864083
  simp only [CollatzResearch.WordTrace]
  refine ⟨213880678014436271487572903, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142587118676290847658381935 213880678014436271487572903)
  ·
    refine ⟨320821017021654407231359355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213880678014436271487572903 320821017021654407231359355)
    ·
      refine ⟨481231525532481610847039033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320821017021654407231359355 481231525532481610847039033)
      ·
        refine ⟨360923644149361208135279275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481231525532481610847039033 360923644149361208135279275)
        ·
          refine ⟨541385466224041812202918913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360923644149361208135279275 541385466224041812202918913)
          ·
            refine ⟨406039099668031359152189185, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541385466224041812202918913 406039099668031359152189185)
            ·
              refine ⟨304529324751023519364141889, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406039099668031359152189185 304529324751023519364141889)
              ·
                refine ⟨228396993563267639523106417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304529324751023519364141889 228396993563267639523106417)
                ·
                  refine ⟨171297745172450729642329813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228396993563267639523106417 171297745172450729642329813)
                  ·
                    refine ⟨4014790902479313975992105, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 171297745172450729642329813 4014790902479313975992105)
                    ·
                      refine ⟨3011093176859485481994079, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014790902479313975992105 3011093176859485481994079)
                      ·
                        rfl

theorem cell23_5864083_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 2, 2, 7, 2].length) (baseStart_5864083 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864083 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864083 prefixEnd_5864083 := by exact prefixLift 5864083
  have htrace : WordTrace (prefixWord ++ tailWord_5864083) baseStart_5864083 baseEnd_5864083 := by
    simpa [prefixWord, tailWord_5864083, baseEnd_5864083] using wordTrace_append hprefix tailTrace_5864083
  have hstable : (prefixWord ++ tailWord_5864083).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864083).length < 2 ^ (prefixWord ++ tailWord_5864083).sum := by decide
  have hdescent : baseEnd_5864083 < baseStart_5864083 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864083) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864094 : List Nat := [4, 3, 1, 1, 1, 1, 5, 1, 1, 2, 3]
def baseStart_5864094 : Nat := 118140960795 + 5864094 * 2 ^ 59
def prefixEnd_5864094 : Nat := 4983230072969 + 3 ^ 40 * 5864094 * 2
def baseEnd_5864094 : Nat := 3011098825146684938956529

theorem tailTrace_5864094 : CollatzResearch.WordTrace tailWord_5864094 prefixEnd_5864094 3011098825146684938956529 := by
  unfold tailWord_5864094
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735134902174552545777917, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142587386144930946910815557 26735134902174552545777917)
  ·
    refine ⟨10025675588315457204666719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26735134902174552545777917 10025675588315457204666719)
    ·
      refine ⟨15038513382473185807000079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10025675588315457204666719 15038513382473185807000079)
      ·
        refine ⟨22557770073709778710500119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15038513382473185807000079 22557770073709778710500119)
        ·
          refine ⟨33836655110564668065750179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22557770073709778710500119 33836655110564668065750179)
          ·
            refine ⟨50754982665847002098625269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33836655110564668065750179 50754982665847002098625269)
            ·
              refine ⟨4758279624923156446746119, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 50754982665847002098625269 4758279624923156446746119)
              ·
                refine ⟨7137419437384734670119179, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758279624923156446746119 7137419437384734670119179)
                ·
                  refine ⟨10706129156077102005178769, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7137419437384734670119179 10706129156077102005178769)
                  ·
                    refine ⟨8029596867057826503884077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10706129156077102005178769 8029596867057826503884077)
                    ·
                      refine ⟨3011098825146684938956529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8029596867057826503884077 3011098825146684938956529)
                      ·
                        rfl

theorem cell23_5864094_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 1, 1, 5, 1, 1, 2, 3].length) (baseStart_5864094 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864094 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864094 prefixEnd_5864094 := by exact prefixLift 5864094
  have htrace : WordTrace (prefixWord ++ tailWord_5864094) baseStart_5864094 baseEnd_5864094 := by
    simpa [prefixWord, tailWord_5864094, baseEnd_5864094] using wordTrace_append hprefix tailTrace_5864094
  have hstable : (prefixWord ++ tailWord_5864094).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864094).length < 2 ^ (prefixWord ++ tailWord_5864094).sum := by decide
  have hdescent : baseEnd_5864094 < baseStart_5864094 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864094) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864110 : List Nat := [4, 1, 4, 1, 1, 1, 1, 1, 2, 7]
def baseStart_5864110 : Nat := 118140960795 + 5864110 * 2 ^ 59
def prefixEnd_5864110 : Nat := 4983230072969 + 3 ^ 40 * 5864110 * 2
def baseEnd_5864110 : Nat := 1003702346945718958785485

theorem tailTrace_5864110 : CollatzResearch.WordTrace tailWord_5864110 prefixEnd_5864110 1003702346945718958785485 := by
  unfold tailWord_5864110
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735207848167306887350723, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142587775190225636732537189 26735207848167306887350723)
  ·
    refine ⟨40102811772250960331026085, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26735207848167306887350723 40102811772250960331026085)
    ·
      refine ⟨7519277207297055062067391, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 40102811772250960331026085 7519277207297055062067391)
      ·
        refine ⟨11278915810945582593101087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7519277207297055062067391 11278915810945582593101087)
        ·
          refine ⟨16918373716418373889651631, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11278915810945582593101087 16918373716418373889651631)
          ·
            refine ⟨25377560574627560834477447, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16918373716418373889651631 25377560574627560834477447)
            ·
              refine ⟨38066340861941341251716171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25377560574627560834477447 38066340861941341251716171)
              ·
                refine ⟨57099511292912011877574257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38066340861941341251716171 57099511292912011877574257)
                ·
                  refine ⟨42824633469684008908180693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57099511292912011877574257 42824633469684008908180693)
                  ·
                    refine ⟨1003702346945718958785485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 42824633469684008908180693 1003702346945718958785485)
                    ·
                      rfl

theorem cell23_5864110_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 1, 1, 1, 1, 2, 7].length) (baseStart_5864110 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864110 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864110 prefixEnd_5864110 := by exact prefixLift 5864110
  have htrace : WordTrace (prefixWord ++ tailWord_5864110) baseStart_5864110 baseEnd_5864110 := by
    simpa [prefixWord, tailWord_5864110, baseEnd_5864110] using wordTrace_append hprefix tailTrace_5864110
  have hstable : (prefixWord ++ tailWord_5864110).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864110).length < 2 ^ (prefixWord ++ tailWord_5864110).sum := by decide
  have hdescent : baseEnd_5864110 < baseStart_5864110 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864110) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864117 : List Nat := [1, 3, 3, 3, 1, 1, 1, 2, 3, 3, 2]
def baseStart_5864117 : Nat := 118140960795 + 5864117 * 2 ^ 59
def prefixEnd_5864117 : Nat := 4983230072969 + 3 ^ 40 * 5864117 * 2
def baseEnd_5864117 : Nat := 3011110635201738348968923

theorem tailTrace_5864117 : CollatzResearch.WordTrace tailWord_5864117 prefixEnd_5864117 3011110635201738348968923 := by
  unfold tailWord_5864117
  simp only [CollatzResearch.WordTrace]
  refine ⟨213881918096313095294310605, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142587945397542063529540403 213881918096313095294310605)
  ·
    refine ⟨80205719286117410735366477, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213881918096313095294310605 80205719286117410735366477)
    ·
      refine ⟨30077144732294029025762429, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80205719286117410735366477 30077144732294029025762429)
      ·
        refine ⟨11278929274610260884660911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30077144732294029025762429 11278929274610260884660911)
        ·
          refine ⟨16918393911915391326991367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11278929274610260884660911 16918393911915391326991367)
          ·
            refine ⟨25377590867873086990487051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16918393911915391326991367 25377590867873086990487051)
            ·
              refine ⟨38066386301809630485730577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25377590867873086990487051 38066386301809630485730577)
              ·
                refine ⟨28549789726357222864297933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38066386301809630485730577 28549789726357222864297933)
                ·
                  refine ⟨10706171147383958574111725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28549789726357222864297933 10706171147383958574111725)
                  ·
                    refine ⟨4014814180268984465291897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10706171147383958574111725 4014814180268984465291897)
                    ·
                      refine ⟨3011110635201738348968923, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014814180268984465291897 3011110635201738348968923)
                      ·
                        rfl

theorem cell23_5864117_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 3, 1, 1, 1, 2, 3, 3, 2].length) (baseStart_5864117 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864117 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864117 prefixEnd_5864117 := by exact prefixLift 5864117
  have htrace : WordTrace (prefixWord ++ tailWord_5864117) baseStart_5864117 baseEnd_5864117 := by
    simpa [prefixWord, tailWord_5864117, baseEnd_5864117] using wordTrace_append hprefix tailTrace_5864117
  have hstable : (prefixWord ++ tailWord_5864117).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864117).length < 2 ^ (prefixWord ++ tailWord_5864117).sum := by decide
  have hdescent : baseEnd_5864117 < baseStart_5864117 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864117) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864164 : List Nat := [2, 3, 1, 1, 1, 4, 3, 2, 2, 2, 2]
def baseStart_5864164 : Nat := 118140960795 + 5864164 * 2 ^ 59
def prefixEnd_5864164 : Nat := 4983230072969 + 3 ^ 40 * 5864164 * 2
def baseEnd_5864164 : Nat := 3011134768792499665081207

theorem tailTrace_5864164 : CollatzResearch.WordTrace tailWord_5864164 prefixEnd_5864164 3011134768792499665081207 := by
  unfold tailWord_5864164
  simp only [CollatzResearch.WordTrace]
  refine ⟨106941816163571411160635773, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142589088218095214880847697 106941816163571411160635773)
  ·
    refine ⟨40103181061339279185238415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106941816163571411160635773 40103181061339279185238415)
    ·
      refine ⟨60154771592008918777857623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40103181061339279185238415 60154771592008918777857623)
      ·
        refine ⟨90232157388013378166786435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60154771592008918777857623 90232157388013378166786435)
        ·
          refine ⟨135348236082020067250179653, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90232157388013378166786435 135348236082020067250179653)
          ·
            refine ⟨25377794265378762609408685, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135348236082020067250179653 25377794265378762609408685)
            ·
              refine ⟨9516672849517035978528257, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25377794265378762609408685 9516672849517035978528257)
              ·
                refine ⟨7137504637137776983896193, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9516672849517035978528257 7137504637137776983896193)
                ·
                  refine ⟨5353128477853332737922145, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7137504637137776983896193 5353128477853332737922145)
                  ·
                    refine ⟨4014846358389999553441609, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5353128477853332737922145 4014846358389999553441609)
                    ·
                      refine ⟨3011134768792499665081207, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4014846358389999553441609 3011134768792499665081207)
                      ·
                        rfl

theorem cell23_5864164_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 1, 4, 3, 2, 2, 2, 2].length) (baseStart_5864164 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864164 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864164 prefixEnd_5864164 := by exact prefixLift 5864164
  have htrace : WordTrace (prefixWord ++ tailWord_5864164) baseStart_5864164 baseEnd_5864164 := by
    simpa [prefixWord, tailWord_5864164, baseEnd_5864164] using wordTrace_append hprefix tailTrace_5864164
  have hstable : (prefixWord ++ tailWord_5864164).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864164).length < 2 ^ (prefixWord ++ tailWord_5864164).sum := by decide
  have hdescent : baseEnd_5864164 < baseStart_5864164 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864164) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864193 : List Nat := [1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 5]
def baseStart_5864193 : Nat := 118140960795 + 5864193 * 2 ^ 59
def prefixEnd_5864193 : Nat := 4983230072969 + 3 ^ 40 * 5864193 * 2
def baseEnd_5864193 : Nat := 3011149659731480051618573

theorem tailTrace_5864193 : CollatzResearch.WordTrace tailWord_5864193 prefixEnd_5864193 3011149659731480051618573 := by
  unfold tailWord_5864193
  simp only [CollatzResearch.WordTrace]
  refine ⟨213884690044037760274077233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142589793362691840182718155 213884690044037760274077233)
  ·
    refine ⟨160413517533028320205557925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213884690044037760274077233 160413517533028320205557925)
    ·
      refine ⟨30077534537442810038542111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160413517533028320205557925 30077534537442810038542111)
      ·
        refine ⟨45116301806164215057813167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30077534537442810038542111 45116301806164215057813167)
        ·
          refine ⟨67674452709246322586719751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45116301806164215057813167 67674452709246322586719751)
          ·
            refine ⟨101511679063869483880079627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67674452709246322586719751 101511679063869483880079627)
            ·
              refine ⟨152267518595804225820119441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101511679063869483880079627 152267518595804225820119441)
              ·
                refine ⟨114200638946853169365089581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152267518595804225820119441 114200638946853169365089581)
                ·
                  refine ⟨42825239605069938511908593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114200638946853169365089581 42825239605069938511908593)
                  ·
                    refine ⟨32118929703802453883931445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42825239605069938511908593 32118929703802453883931445)
                    ·
                      refine ⟨3011149659731480051618573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32118929703802453883931445 3011149659731480051618573)
                      ·
                        rfl

theorem cell23_5864193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 1, 1, 1, 2, 3, 2, 5].length) (baseStart_5864193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864193 prefixEnd_5864193 := by exact prefixLift 5864193
  have htrace : WordTrace (prefixWord ++ tailWord_5864193) baseStart_5864193 baseEnd_5864193 := by
    simpa [prefixWord, tailWord_5864193, baseEnd_5864193] using wordTrace_append hprefix tailTrace_5864193
  have hstable : (prefixWord ++ tailWord_5864193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864193).length < 2 ^ (prefixWord ++ tailWord_5864193).sum := by decide
  have hdescent : baseEnd_5864193 < baseStart_5864193 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864220 : List Nat := [2, 2, 3, 1, 1, 3, 1, 1, 4, 1, 4]
def baseStart_5864220 : Nat := 118140960795 + 5864220 * 2 ^ 59
def prefixEnd_5864220 : Nat := 4983230072969 + 3 ^ 40 * 5864220 * 2
def baseEnd_5864220 : Nat := 3011163523709151445980949

theorem tailTrace_5864220 : CollatzResearch.WordTrace tailWord_5864220 prefixEnd_5864220 3011163523709151445980949 := by
  unfold tailWord_5864220
  simp only [CollatzResearch.WordTrace]
  refine ⟨106942837407469971942655057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142590449876626629256873409 106942837407469971942655057)
  ·
    refine ⟨80207128055602478956991293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106942837407469971942655057 80207128055602478956991293)
    ·
      refine ⟨30077673020850929608871735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80207128055602478956991293 30077673020850929608871735)
      ·
        refine ⟨45116509531276394413307603, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30077673020850929608871735 45116509531276394413307603)
        ·
          refine ⟨67674764296914591619961405, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45116509531276394413307603 67674764296914591619961405)
          ·
            refine ⟨25378036611342971857485527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67674764296914591619961405 25378036611342971857485527)
            ·
              refine ⟨38067054917014457786228291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25378036611342971857485527 38067054917014457786228291)
              ·
                refine ⟨57100582375521686679342437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38067054917014457786228291 57100582375521686679342437)
                ·
                  refine ⟨10706359195410316252376707, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57100582375521686679342437 10706359195410316252376707)
                  ·
                    refine ⟨16059538793115474378565061, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10706359195410316252376707 16059538793115474378565061)
                    ·
                      refine ⟨3011163523709151445980949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16059538793115474378565061 3011163523709151445980949)
                      ·
                        rfl

theorem cell23_5864220_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 3, 1, 1, 4, 1, 4].length) (baseStart_5864220 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864220 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864220 prefixEnd_5864220 := by exact prefixLift 5864220
  have htrace : WordTrace (prefixWord ++ tailWord_5864220) baseStart_5864220 baseEnd_5864220 := by
    simpa [prefixWord, tailWord_5864220, baseEnd_5864220] using wordTrace_append hprefix tailTrace_5864220
  have hstable : (prefixWord ++ tailWord_5864220).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864220).length < 2 ^ (prefixWord ++ tailWord_5864220).sum := by decide
  have hdescent : baseEnd_5864220 < baseStart_5864220 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864220) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864221 : List Nat := [1, 4, 2, 4, 1, 1, 3, 2, 5]
def baseStart_5864221 : Nat := 118140960795 + 5864221 * 2 ^ 59
def prefixEnd_5864221 : Nat := 4983230072969 + 3 ^ 40 * 5864221 * 2
def baseEnd_5864221 : Nat := 334573781909978438007605

theorem tailTrace_5864221 : CollatzResearch.WordTrace tailWord_5864221 prefixEnd_5864221 334573781909978438007605 := by
  unfold tailWord_5864221
  simp only [CollatzResearch.WordTrace]
  refine ⟨213885711287936321056096517, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142590474191957547370731011 213885711287936321056096517)
  ·
    refine ⟨40103570866488060198018097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213885711287936321056096517 40103570866488060198018097)
    ·
      refine ⟨30077678149866045148513573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40103570866488060198018097 30077678149866045148513573)
      ·
        refine ⟨5639564653099883465346295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30077678149866045148513573 5639564653099883465346295)
        ·
          refine ⟨8459346979649825198019443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5639564653099883465346295 8459346979649825198019443)
          ·
            refine ⟨12689020469474737797029165, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8459346979649825198019443 12689020469474737797029165)
            ·
              refine ⟨4758382676053026673885937, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12689020469474737797029165 4758382676053026673885937)
              ·
                refine ⟨3568787007039770005414453, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4758382676053026673885937 3568787007039770005414453)
                ·
                  refine ⟨334573781909978438007605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3568787007039770005414453 334573781909978438007605)
                  ·
                    rfl

theorem cell23_5864221_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 3, 2, 5].length) (baseStart_5864221 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864221 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864221 prefixEnd_5864221 := by exact prefixLift 5864221
  have htrace : WordTrace (prefixWord ++ tailWord_5864221) baseStart_5864221 baseEnd_5864221 := by
    simpa [prefixWord, tailWord_5864221, baseEnd_5864221] using wordTrace_append hprefix tailTrace_5864221
  have hstable : (prefixWord ++ tailWord_5864221).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864221).length < 2 ^ (prefixWord ++ tailWord_5864221).sum := by decide
  have hdescent : baseEnd_5864221 < baseStart_5864221 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864221) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864254 : List Nat := [4, 2, 1, 2, 3, 1, 2, 1, 2, 1, 4]
def baseStart_5864254 : Nat := 118140960795 + 5864254 * 2 ^ 59
def prefixEnd_5864254 : Nat := 4983230072969 + 3 ^ 40 * 5864254 * 2
def baseEnd_5864254 : Nat := 3011180982051404312955793

theorem tailTrace_5864254 : CollatzResearch.WordTrace tailWord_5864254 prefixEnd_5864254 3011180982051404312955793 := by
  unfold tailWord_5864254
  simp only [CollatzResearch.WordTrace]
  refine ⟨26735864362102095961505977, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142591276597877845128031877 26735864362102095961505977)
  ·
    refine ⟨20051898271576571971129483, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26735864362102095961505977 20051898271576571971129483)
    ·
      refine ⟨30077847407364857956694225, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20051898271576571971129483 30077847407364857956694225)
      ·
        refine ⟨22558385555523643467520669, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30077847407364857956694225 22558385555523643467520669)
        ·
          refine ⟨8459394583321366300320251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22558385555523643467520669 8459394583321366300320251)
          ·
            refine ⟨12689091874982049450480377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8459394583321366300320251 12689091874982049450480377)
            ·
              refine ⟨9516818906236537087860283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12689091874982049450480377 9516818906236537087860283)
              ·
                refine ⟨14275228359354805631790425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516818906236537087860283 14275228359354805631790425)
                ·
                  refine ⟨10706421269516104223842819, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14275228359354805631790425 10706421269516104223842819)
                  ·
                    refine ⟨16059631904274156335764229, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10706421269516104223842819 16059631904274156335764229)
                    ·
                      refine ⟨3011180982051404312955793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16059631904274156335764229 3011180982051404312955793)
                      ·
                        rfl

theorem cell23_5864254_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 2, 3, 1, 2, 1, 2, 1, 4].length) (baseStart_5864254 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864254 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864254 prefixEnd_5864254 := by exact prefixLift 5864254
  have htrace : WordTrace (prefixWord ++ tailWord_5864254) baseStart_5864254 baseEnd_5864254 := by
    simpa [prefixWord, tailWord_5864254, baseEnd_5864254] using wordTrace_append hprefix tailTrace_5864254
  have hstable : (prefixWord ++ tailWord_5864254).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864254).length < 2 ^ (prefixWord ++ tailWord_5864254).sum := by decide
  have hdescent : baseEnd_5864254 < baseStart_5864254 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864254) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864263 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 8]
def baseStart_5864263 : Nat := 118140960795 + 5864263 * 2 ^ 59
def prefixEnd_5864263 : Nat := 4983230072969 + 3 ^ 40 * 5864263 * 2
def baseEnd_5864263 : Nat := 3011185603377294777743251

theorem tailTrace_5864263 : CollatzResearch.WordTrace tailWord_5864263 prefixEnd_5864263 3011185603377294777743251 := by
  unfold tailWord_5864263
  simp only [CollatzResearch.WordTrace]
  refine ⟨213887243153784162229125443, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142591495435856108152750295 213887243153784162229125443)
  ·
    refine ⟨320830864730676243343688165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213887243153784162229125443 320830864730676243343688165)
    ·
      refine ⟨60155787137001795626941531, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320830864730676243343688165 60155787137001795626941531)
      ·
        refine ⟨90233680705502693440412297, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60155787137001795626941531 90233680705502693440412297)
        ·
          refine ⟨67675260529127020080309223, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90233680705502693440412297 67675260529127020080309223)
          ·
            refine ⟨101512890793690530120463835, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67675260529127020080309223 101512890793690530120463835)
            ·
              refine ⟨152269336190535795180695753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101512890793690530120463835 152269336190535795180695753)
              ·
                refine ⟨114202002142901846385521815, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 152269336190535795180695753 114202002142901846385521815)
                ·
                  refine ⟨171303003214352769578282723, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114202002142901846385521815 171303003214352769578282723)
                  ·
                    refine ⟨256954504821529154367424085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 171303003214352769578282723 256954504821529154367424085)
                    ·
                      refine ⟨3011185603377294777743251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 8 256954504821529154367424085 3011185603377294777743251)
                      ·
                        rfl

theorem cell23_5864263_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 1, 8].length) (baseStart_5864263 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864263 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864263 prefixEnd_5864263 := by exact prefixLift 5864263
  have htrace : WordTrace (prefixWord ++ tailWord_5864263) baseStart_5864263 baseEnd_5864263 := by
    simpa [prefixWord, tailWord_5864263, baseEnd_5864263] using wordTrace_append hprefix tailTrace_5864263
  have hstable : (prefixWord ++ tailWord_5864263).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864263).length < 2 ^ (prefixWord ++ tailWord_5864263).sum := by decide
  have hdescent : baseEnd_5864263 < baseStart_5864263 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864263) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864281 : List Nat := [1, 2, 1, 2, 2, 6, 2, 2, 1, 4]
def baseStart_5864281 : Nat := 118140960795 + 5864281 * 2 ^ 59
def prefixEnd_5864281 : Nat := 4983230072969 + 3 ^ 40 * 5864281 * 2
def baseEnd_5864281 : Nat := 1003731615343025235772723

theorem tailTrace_5864281 : CollatzResearch.WordTrace tailWord_5864281 prefixEnd_5864281 1003731615343025235772723 := by
  unfold tailWord_5864281
  simp only [CollatzResearch.WordTrace]
  refine ⟨213887899667718951303280697, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142591933111812634202187131 213887899667718951303280697)
  ·
    refine ⟨160415924750789213477460523, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213887899667718951303280697 160415924750789213477460523)
    ·
      refine ⟨240623887126183820216190785, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160415924750789213477460523 240623887126183820216190785)
      ·
        refine ⟨180467915344637865162143089, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240623887126183820216190785 180467915344637865162143089)
        ·
          refine ⟨135350936508478398871607317, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180467915344637865162143089 135350936508478398871607317)
          ·
            refine ⟨6344575148834924947106593, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135350936508478398871607317 6344575148834924947106593)
            ·
              refine ⟨4758431361626193710329945, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6344575148834924947106593 4758431361626193710329945)
              ·
                refine ⟨3568823521219645282747459, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 4758431361626193710329945 3568823521219645282747459)
                ·
                  refine ⟨5353235281829467924121189, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3568823521219645282747459 5353235281829467924121189)
                  ·
                    refine ⟨1003731615343025235772723, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5353235281829467924121189 1003731615343025235772723)
                    ·
                      rfl

theorem cell23_5864281_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 6, 2, 2, 1, 4].length) (baseStart_5864281 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864281 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864281 prefixEnd_5864281 := by exact prefixLift 5864281
  have htrace : WordTrace (prefixWord ++ tailWord_5864281) baseStart_5864281 baseEnd_5864281 := by
    simpa [prefixWord, tailWord_5864281, baseEnd_5864281] using wordTrace_append hprefix tailTrace_5864281
  have hstable : (prefixWord ++ tailWord_5864281).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864281).length < 2 ^ (prefixWord ++ tailWord_5864281).sum := by decide
  have hdescent : baseEnd_5864281 < baseStart_5864281 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864281) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864287 : List Nat := [1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 3]
def baseStart_5864287 : Nat := 118140960795 + 5864287 * 2 ^ 59
def prefixEnd_5864287 : Nat := 4983230072969 + 3 ^ 40 * 5864287 * 2
def baseEnd_5864287 : Nat := 3011197926913002683843141

theorem tailTrace_5864287 : CollatzResearch.WordTrace tailWord_5864287 prefixEnd_5864287 3011197926913002683843141 := by
  unfold tailWord_5864287
  simp only [CollatzResearch.WordTrace]
  refine ⟨213888118505697214327999115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142592079003798142885332743 213888118505697214327999115)
  ·
    refine ⟨320832177758545821491998673, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213888118505697214327999115 320832177758545821491998673)
    ·
      refine ⟨240624133318909366118999005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320832177758545821491998673 240624133318909366118999005)
      ·
        refine ⟨90234049994591012294624627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240624133318909366118999005 90234049994591012294624627)
        ·
          refine ⟨135351074991886518441936941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90234049994591012294624627 135351074991886518441936941)
          ·
            refine ⟨50756653121957444415726353, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135351074991886518441936941 50756653121957444415726353)
            ·
              refine ⟨38067489841468083311794765, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50756653121957444415726353 38067489841468083311794765)
              ·
                refine ⟨14275308690550531241923037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38067489841468083311794765 14275308690550531241923037)
                ·
                  refine ⟨5353240758956449215721139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14275308690550531241923037 5353240758956449215721139)
                  ·
                    refine ⟨8029861138434673823581709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353240758956449215721139 8029861138434673823581709)
                    ·
                      refine ⟨3011197926913002683843141, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8029861138434673823581709 3011197926913002683843141)
                      ·
                        rfl

theorem cell23_5864287_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 3, 2, 3, 3, 1, 3].length) (baseStart_5864287 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864287 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864287 prefixEnd_5864287 := by exact prefixLift 5864287
  have htrace : WordTrace (prefixWord ++ tailWord_5864287) baseStart_5864287 baseEnd_5864287 := by
    simpa [prefixWord, tailWord_5864287, baseEnd_5864287] using wordTrace_append hprefix tailTrace_5864287
  have hstable : (prefixWord ++ tailWord_5864287).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864287).length < 2 ^ (prefixWord ++ tailWord_5864287).sum := by decide
  have hdescent : baseEnd_5864287 < baseStart_5864287 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864287) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864354 : List Nat := [3, 3, 1, 2, 2, 3, 1, 1, 1, 6]
def baseStart_5864354 : Nat := 118140960795 + 5864354 * 2 ^ 59
def prefixEnd_5864354 : Nat := 4983230072969 + 3 ^ 40 * 5864354 * 2
def baseEnd_5864354 : Nat := 1003744110038951307235111

theorem tailTrace_5864354 : CollatzResearch.WordTrace tailWord_5864354 prefixEnd_5864354 1003744110038951307235111 := by
  unfold tailWord_5864354
  simp only [CollatzResearch.WordTrace]
  refine ⟨53472640549113621192672029, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142593708130969656513792077 53472640549113621192672029)
  ·
    refine ⟨20052240205917607947252011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 53472640549113621192672029 20052240205917607947252011)
    ·
      refine ⟨30078360308876411920878017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20052240205917607947252011 30078360308876411920878017)
      ·
        refine ⟨22558770231657308940658513, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30078360308876411920878017 22558770231657308940658513)
        ·
          refine ⟨16919077673742981705493885, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22558770231657308940658513 16919077673742981705493885)
          ·
            refine ⟨6344654127653618139560207, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16919077673742981705493885 6344654127653618139560207)
            ·
              refine ⟨9516981191480427209340311, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6344654127653618139560207 9516981191480427209340311)
              ·
                refine ⟨14275471787220640814010467, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9516981191480427209340311 14275471787220640814010467)
                ·
                  refine ⟨21413207680830961221015701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14275471787220640814010467 21413207680830961221015701)
                  ·
                    refine ⟨1003744110038951307235111, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21413207680830961221015701 1003744110038951307235111)
                    ·
                      rfl

theorem cell23_5864354_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 2, 2, 3, 1, 1, 1, 6].length) (baseStart_5864354 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864354 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864354 prefixEnd_5864354 := by exact prefixLift 5864354
  have htrace : WordTrace (prefixWord ++ tailWord_5864354) baseStart_5864354 baseEnd_5864354 := by
    simpa [prefixWord, tailWord_5864354, baseEnd_5864354] using wordTrace_append hprefix tailTrace_5864354
  have hstable : (prefixWord ++ tailWord_5864354).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864354).length < 2 ^ (prefixWord ++ tailWord_5864354).sum := by decide
  have hdescent : baseEnd_5864354 < baseStart_5864354 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864354) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864394 : List Nat := [3, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3]
def baseStart_5864394 : Nat := 118140960795 + 5864394 * 2 ^ 59
def prefixEnd_5864394 : Nat := 4983230072969 + 3 ^ 40 * 5864394 * 2
def baseEnd_5864394 : Nat := 3011252869343033765205149

theorem tailTrace_5864394 : CollatzResearch.WordTrace tailWord_5864394 prefixEnd_5864394 3011252869343033765205149 := by
  unfold tailWord_5864394
  simp only [CollatzResearch.WordTrace]
  refine ⟨53473005279077392900536059, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142594680744206381068096157 53473005279077392900536059)
  ·
    refine ⟨80209507918616089350804089, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53473005279077392900536059 80209507918616089350804089)
    ·
      refine ⟨60157130938962067013103067, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80209507918616089350804089 60157130938962067013103067)
      ·
        refine ⟨90235696408443100519654601, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60157130938962067013103067 90235696408443100519654601)
        ·
          refine ⟨67676772306332325389740951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90235696408443100519654601 67676772306332325389740951)
          ·
            refine ⟨101515158459498488084611427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67676772306332325389740951 101515158459498488084611427)
            ·
              refine ⟨152272737689247732126917141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101515158459498488084611427 152272737689247732126917141)
              ·
                refine ⟨7137784579183487443449241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152272737689247732126917141 7137784579183487443449241)
                ·
                  refine ⟨5353338434387615582586931, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7137784579183487443449241 5353338434387615582586931)
                  ·
                    refine ⟨8030007651581423373880397, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353338434387615582586931 8030007651581423373880397)
                    ·
                      refine ⟨3011252869343033765205149, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8030007651581423373880397 3011252869343033765205149)
                      ·
                        rfl

theorem cell23_5864394_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 1, 2, 1, 1, 6, 2, 1, 3].length) (baseStart_5864394 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864394 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864394 prefixEnd_5864394 := by exact prefixLift 5864394
  have htrace : WordTrace (prefixWord ++ tailWord_5864394) baseStart_5864394 baseEnd_5864394 := by
    simpa [prefixWord, tailWord_5864394, baseEnd_5864394] using wordTrace_append hprefix tailTrace_5864394
  have hstable : (prefixWord ++ tailWord_5864394).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864394).length < 2 ^ (prefixWord ++ tailWord_5864394).sum := by decide
  have hdescent : baseEnd_5864394 < baseStart_5864394 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864394) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864400 : List Nat := [2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4]
def baseStart_5864400 : Nat := 118140960795 + 5864400 * 2 ^ 59
def prefixEnd_5864400 : Nat := 4983230072969 + 3 ^ 40 * 5864400 * 2
def baseEnd_5864400 : Nat := 3011255950226960741730121

theorem tailTrace_5864400 : CollatzResearch.WordTrace tailWord_5864400 prefixEnd_5864400 3011255950226960741730121 := by
  unfold tailWord_5864400
  simp only [CollatzResearch.WordTrace]
  refine ⟨106946119977143917313431327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142594826636191889751241769 106946119977143917313431327)
  ·
    refine ⟨160419179965715875970146991, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106946119977143917313431327 160419179965715875970146991)
    ·
      refine ⟨240628769948573813955220487, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160419179965715875970146991 240628769948573813955220487)
      ·
        refine ⟨360943154922860720932830731, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240628769948573813955220487 360943154922860720932830731)
        ·
          refine ⟨541414732384291081399246097, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360943154922860720932830731 541414732384291081399246097)
          ·
            refine ⟨406061049288218311049434573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541414732384291081399246097 406061049288218311049434573)
            ·
              refine ⟨152272893483081866643537965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 406061049288218311049434573 152272893483081866643537965)
              ·
                refine ⟨57102335056155699991326737, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152272893483081866643537965 57102335056155699991326737)
                ·
                  refine ⟨42826751292116774993495053, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 57102335056155699991326737 42826751292116774993495053)
                  ·
                    refine ⟨16060031734543790622560645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42826751292116774993495053 16060031734543790622560645)
                    ·
                      refine ⟨3011255950226960741730121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16060031734543790622560645 3011255950226960741730121)
                      ·
                        rfl

theorem cell23_5864400_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 3, 3, 2, 3, 4].length) (baseStart_5864400 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864400 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864400 prefixEnd_5864400 := by exact prefixLift 5864400
  have htrace : WordTrace (prefixWord ++ tailWord_5864400) baseStart_5864400 baseEnd_5864400 := by
    simpa [prefixWord, tailWord_5864400, baseEnd_5864400] using wordTrace_append hprefix tailTrace_5864400
  have hstable : (prefixWord ++ tailWord_5864400).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864400).length < 2 ^ (prefixWord ++ tailWord_5864400).sum := by decide
  have hdescent : baseEnd_5864400 < baseStart_5864400 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864400) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864544 : List Nat := [2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3]
def baseStart_5864544 : Nat := 118140960795 + 5864544 * 2 ^ 59
def prefixEnd_5864544 : Nat := 4983230072969 + 3 ^ 40 * 5864544 * 2
def baseEnd_5864544 : Nat := 3011329891441208178329459

theorem tailTrace_5864544 : CollatzResearch.WordTrace tailWord_5864544 prefixEnd_5864544 3011329891441208178329459 := by
  unfold tailWord_5864544
  simp only [CollatzResearch.WordTrace]
  refine ⟨106948746032883073610052343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142598328043844098146736457 106948746032883073610052343)
  ·
    refine ⟨160423119049324610415078515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106948746032883073610052343 160423119049324610415078515)
    ·
      refine ⟨240634678573986915622617773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160423119049324610415078515 240634678573986915622617773)
      ·
        refine ⟨90238004465245093358481665, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240634678573986915622617773 90238004465245093358481665)
        ·
          refine ⟨67678503348933820018861249, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90238004465245093358481665 67678503348933820018861249)
          ·
            refine ⟨50758877511700365014145937, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67678503348933820018861249 50758877511700365014145937)
            ·
              refine ⟨38069158133775273760609453, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50758877511700365014145937 38069158133775273760609453)
              ·
                refine ⟨14275934300165727660228545, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38069158133775273760609453 14275934300165727660228545)
                ·
                  refine ⟨10706950725124295745171409, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14275934300165727660228545 10706950725124295745171409)
                  ·
                    refine ⟨8030213043843221808878557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10706950725124295745171409 8030213043843221808878557)
                    ·
                      refine ⟨3011329891441208178329459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8030213043843221808878557 3011329891441208178329459)
                      ·
                        rfl

theorem cell23_5864544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 2, 2, 3, 2, 2, 3].length) (baseStart_5864544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864544 prefixEnd_5864544 := by exact prefixLift 5864544
  have htrace : WordTrace (prefixWord ++ tailWord_5864544) baseStart_5864544 baseEnd_5864544 := by
    simpa [prefixWord, tailWord_5864544, baseEnd_5864544] using wordTrace_append hprefix tailTrace_5864544
  have hstable : (prefixWord ++ tailWord_5864544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864544).length < 2 ^ (prefixWord ++ tailWord_5864544).sum := by decide
  have hdescent : baseEnd_5864544 < baseStart_5864544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864608 : List Nat := [2, 1, 1, 4, 2, 1, 2, 5, 1, 1, 3]
def baseStart_5864608 : Nat := 118140960795 + 5864608 * 2 ^ 59
def prefixEnd_5864608 : Nat := 4983230072969 + 3 ^ 40 * 5864608 * 2
def baseEnd_5864608 : Nat := 3011362754203095927929165

theorem tailTrace_5864608 : CollatzResearch.WordTrace tailWord_5864608 prefixEnd_5864608 3011362754203095927929165 := by
  unfold tailWord_5864608
  simp only [CollatzResearch.WordTrace]
  refine ⟨106949913168767143075217239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142599884225022857433622985 106949913168767143075217239)
  ·
    refine ⟨160424869753150714612825859, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106949913168767143075217239 160424869753150714612825859)
    ·
      refine ⟨240637304629726071919238789, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160424869753150714612825859 240637304629726071919238789)
      ·
        refine ⟨45119494618073638484857273, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240637304629726071919238789 45119494618073638484857273)
        ·
          refine ⟨33839620963555228863642955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45119494618073638484857273 33839620963555228863642955)
          ·
            refine ⟨50759431445332843295464433, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33839620963555228863642955 50759431445332843295464433)
            ·
              refine ⟨38069573583999632471598325, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50759431445332843295464433 38069573583999632471598325)
              ·
                refine ⟨3569022523499965544212343, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 38069573583999632471598325 3569022523499965544212343)
                ·
                  refine ⟨5353533785249948316318515, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569022523499965544212343 5353533785249948316318515)
                  ·
                    refine ⟨8030300677874922474477773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353533785249948316318515 8030300677874922474477773)
                    ·
                      refine ⟨3011362754203095927929165, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8030300677874922474477773 3011362754203095927929165)
                      ·
                        rfl

theorem cell23_5864608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 2, 1, 2, 5, 1, 1, 3].length) (baseStart_5864608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864608 prefixEnd_5864608 := by exact prefixLift 5864608
  have htrace : WordTrace (prefixWord ++ tailWord_5864608) baseStart_5864608 baseEnd_5864608 := by
    simpa [prefixWord, tailWord_5864608, baseEnd_5864608] using wordTrace_append hprefix tailTrace_5864608
  have hstable : (prefixWord ++ tailWord_5864608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864608).length < 2 ^ (prefixWord ++ tailWord_5864608).sum := by decide
  have hdescent : baseEnd_5864608 < baseStart_5864608 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864617 : List Nat := [1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 5]
def baseStart_5864617 : Nat := 118140960795 + 5864617 * 2 ^ 59
def prefixEnd_5864617 : Nat := 4983230072969 + 3 ^ 40 * 5864617 * 2
def baseEnd_5864617 : Nat := 3011367375528986392716623

theorem tailTrace_5864617 : CollatzResearch.WordTrace tailWord_5864617 prefixEnd_5864617 3011367375528986392716623 := by
  unfold tailWord_5864617
  simp only [CollatzResearch.WordTrace]
  refine ⟨213900154594501680687512105, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142600103063001120458341403 213900154594501680687512105)
  ·
    refine ⟨160425115945876260515634079, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213900154594501680687512105 160425115945876260515634079)
    ·
      refine ⟨240637673918814390773451119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160425115945876260515634079 240637673918814390773451119)
      ·
        refine ⟨360956510878221586160176679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240637673918814390773451119 360956510878221586160176679)
        ·
          refine ⟨541434766317332379240265019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360956510878221586160176679 541434766317332379240265019)
          ·
            refine ⟨812152149475998568860397529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541434766317332379240265019 812152149475998568860397529)
            ·
              refine ⟨609114112106998926645298147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812152149475998568860397529 609114112106998926645298147)
              ·
                refine ⟨913671168160498389967947221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609114112106998926645298147 913671168160498389967947221)
                ·
                  refine ⟨21414168003761681014873763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 913671168160498389967947221 21414168003761681014873763)
                  ·
                    refine ⟨32121252005642521522310645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21414168003761681014873763 32121252005642521522310645)
                    ·
                      refine ⟨3011367375528986392716623, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32121252005642521522310645 3011367375528986392716623)
                      ·
                        rfl

theorem cell23_5864617_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 1, 7, 1, 5].length) (baseStart_5864617 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864617 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864617 prefixEnd_5864617 := by exact prefixLift 5864617
  have htrace : WordTrace (prefixWord ++ tailWord_5864617) baseStart_5864617 baseEnd_5864617 := by
    simpa [prefixWord, tailWord_5864617, baseEnd_5864617] using wordTrace_append hprefix tailTrace_5864617
  have hstable : (prefixWord ++ tailWord_5864617).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864617).length < 2 ^ (prefixWord ++ tailWord_5864617).sum := by decide
  have hdescent : baseEnd_5864617 < baseStart_5864617 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864617) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864625 : List Nat := [1, 2, 2, 5, 1, 2, 1, 4, 1, 1, 3]
def baseStart_5864625 : Nat := 118140960795 + 5864625 * 2 ^ 59
def prefixEnd_5864625 : Nat := 4983230072969 + 3 ^ 40 * 5864625 * 2
def baseEnd_5864625 : Nat := 3011371483374222361416587

theorem tailTrace_5864625 : CollatzResearch.WordTrace tailWord_5864625 prefixEnd_5864625 3011371483374222361416587 := by
  unfold tailWord_5864625
  simp only [CollatzResearch.WordTrace]
  refine ⟨213900446378472698053803329, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142600297585648465369202219 213900446378472698053803329)
  ·
    refine ⟨160425334783854523540352497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213900446378472698053803329 160425334783854523540352497)
    ·
      refine ⟨120319001087890892655264373, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160425334783854523540352497 120319001087890892655264373)
      ·
        refine ⟨11279906351989771186431035, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 120319001087890892655264373 11279906351989771186431035)
        ·
          refine ⟨16919859527984656779646553, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11279906351989771186431035 16919859527984656779646553)
          ·
            refine ⟨12689894645988492584734915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16919859527984656779646553 12689894645988492584734915)
            ·
              refine ⟨19034841968982738877102373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12689894645988492584734915 19034841968982738877102373)
              ·
                refine ⟨3569032869184263539456695, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19034841968982738877102373 3569032869184263539456695)
                ·
                  refine ⟨5353549303776395309185043, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569032869184263539456695 5353549303776395309185043)
                  ·
                    refine ⟨8030323955664592963777565, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353549303776395309185043 8030323955664592963777565)
                    ·
                      refine ⟨3011371483374222361416587, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8030323955664592963777565 3011371483374222361416587)
                      ·
                        rfl

theorem cell23_5864625_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 5, 1, 2, 1, 4, 1, 1, 3].length) (baseStart_5864625 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864625 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864625 prefixEnd_5864625 := by exact prefixLift 5864625
  have htrace : WordTrace (prefixWord ++ tailWord_5864625) baseStart_5864625 baseEnd_5864625 := by
    simpa [prefixWord, tailWord_5864625, baseEnd_5864625] using wordTrace_append hprefix tailTrace_5864625
  have hstable : (prefixWord ++ tailWord_5864625).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864625).length < 2 ^ (prefixWord ++ tailWord_5864625).sum := by decide
  have hdescent : baseEnd_5864625 < baseStart_5864625 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864625) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864627 : List Nat := [1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6]
def baseStart_5864627 : Nat := 118140960795 + 5864627 * 2 ^ 59
def prefixEnd_5864627 : Nat := 4983230072969 + 3 ^ 40 * 5864627 * 2
def baseEnd_5864627 : Nat := 3011372510335531353591577

theorem tailTrace_5864627 : CollatzResearch.WordTrace tailWord_5864627 prefixEnd_5864627 3011372510335531353591577 := by
  unfold tailWord_5864627
  simp only [CollatzResearch.WordTrace]
  refine ⟨213900519324465452395376135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142600346216310301596917423 213900519324465452395376135)
  ·
    refine ⟨320850778986698178593064203, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213900519324465452395376135 320850778986698178593064203)
    ·
      refine ⟨481276168480047267889596305, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320850778986698178593064203 481276168480047267889596305)
      ·
        refine ⟨360957126360035450917197229, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481276168480047267889596305 360957126360035450917197229)
        ·
          refine ⟨135358922385013294093948961, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 360957126360035450917197229 135358922385013294093948961)
          ·
            refine ⟨101519191788759970570461721, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135358922385013294093948961 101519191788759970570461721)
            ·
              refine ⟨76139393841569977927846291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101519191788759970570461721 76139393841569977927846291)
              ·
                refine ⟨114209090762354966891769437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76139393841569977927846291 114209090762354966891769437)
                ·
                  refine ⟨42828409035883112584413539, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114209090762354966891769437 42828409035883112584413539)
                  ·
                    refine ⟨64242613553824668876620309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42828409035883112584413539 64242613553824668876620309)
                    ·
                      refine ⟨3011372510335531353591577, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64242613553824668876620309 3011372510335531353591577)
                      ·
                        rfl

theorem cell23_5864627_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 2, 2, 1, 3, 1, 6].length) (baseStart_5864627 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864627 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864627 prefixEnd_5864627 := by exact prefixLift 5864627
  have htrace : WordTrace (prefixWord ++ tailWord_5864627) baseStart_5864627 baseEnd_5864627 := by
    simpa [prefixWord, tailWord_5864627, baseEnd_5864627] using wordTrace_append hprefix tailTrace_5864627
  have hstable : (prefixWord ++ tailWord_5864627).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864627).length < 2 ^ (prefixWord ++ tailWord_5864627).sum := by decide
  have hdescent : baseEnd_5864627 < baseStart_5864627 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864627) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864641 : List Nat := [1, 2, 6, 1, 1, 1, 1, 3, 1, 6]
def baseStart_5864641 : Nat := 118140960795 + 5864641 * 2 ^ 59
def prefixEnd_5864641 : Nat := 4983230072969 + 3 ^ 40 * 5864641 * 2
def baseEnd_5864641 : Nat := 1003793233021564766272171

theorem tailTrace_5864641 : CollatzResearch.WordTrace tailWord_5864641 prefixEnd_5864641 1003793233021564766272171 := by
  unfold tailWord_5864641
  simp only [CollatzResearch.WordTrace]
  refine ⟨213901029946414732786385777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142600686630943155190923851 213901029946414732786385777)
  ·
    refine ⟨160425772459811049589789333, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213901029946414732786385777 160425772459811049589789333)
    ·
      refine ⟨7519958084053642949521375, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 160425772459811049589789333 7519958084053642949521375)
      ·
        refine ⟨11279937126080464424282063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7519958084053642949521375 11279937126080464424282063)
        ·
          refine ⟨16919905689120696636423095, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11279937126080464424282063 16919905689120696636423095)
          ·
            refine ⟨25379858533681044954634643, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16919905689120696636423095 25379858533681044954634643)
            ·
              refine ⟨38069787800521567431951965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25379858533681044954634643 38069787800521567431951965)
              ·
                refine ⟨14276170425195587786981987, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38069787800521567431951965 14276170425195587786981987)
                ·
                  refine ⟨21414255637793381680472981, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14276170425195587786981987 21414255637793381680472981)
                  ·
                    refine ⟨1003793233021564766272171, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21414255637793381680472981 1003793233021564766272171)
                    ·
                      rfl

theorem cell23_5864641_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 3, 1, 6].length) (baseStart_5864641 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864641 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864641 prefixEnd_5864641 := by exact prefixLift 5864641
  have htrace : WordTrace (prefixWord ++ tailWord_5864641) baseStart_5864641 baseEnd_5864641 := by
    simpa [prefixWord, tailWord_5864641, baseEnd_5864641] using wordTrace_append hprefix tailTrace_5864641
  have hstable : (prefixWord ++ tailWord_5864641).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864641).length < 2 ^ (prefixWord ++ tailWord_5864641).sum := by decide
  have hdescent : baseEnd_5864641 < baseStart_5864641 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864641) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864642 : List Nat := [3, 5, 1, 1, 2, 1, 1, 2, 3, 1, 3]
def baseStart_5864642 : Nat := 118140960795 + 5864642 * 2 ^ 59
def prefixEnd_5864642 : Nat := 4983230072969 + 3 ^ 40 * 5864642 * 2
def baseEnd_5864642 : Nat := 3011380212545348794904009

theorem tailTrace_5864642 : CollatzResearch.WordTrace tailWord_5864642 prefixEnd_5864642 3011380212545348794904009 := by
  unfold tailWord_5864642
  simp only [CollatzResearch.WordTrace]
  refine ⟨53475266604852777489293045, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142600710946274073304781453 53475266604852777489293045)
  ·
    refine ⟨5013306244204947889621223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 53475266604852777489293045 5013306244204947889621223)
    ·
      refine ⟨7519959366307421834431835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5013306244204947889621223 7519959366307421834431835)
      ·
        refine ⟨11279939049461132751647753, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7519959366307421834431835 11279939049461132751647753)
        ·
          refine ⟨8459954287095849563735815, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11279939049461132751647753 8459954287095849563735815)
          ·
            refine ⟨12689931430643774345603723, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8459954287095849563735815 12689931430643774345603723)
            ·
              refine ⟨19034897145965661518405585, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12689931430643774345603723 19034897145965661518405585)
              ·
                refine ⟨14276172859474246138804189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19034897145965661518405585 14276172859474246138804189)
                ·
                  refine ⟨5353564822302842302051571, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14276172859474246138804189 5353564822302842302051571)
                  ·
                    refine ⟨8030347233454263453077357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353564822302842302051571 8030347233454263453077357)
                    ·
                      refine ⟨3011380212545348794904009, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8030347233454263453077357 3011380212545348794904009)
                      ·
                        rfl

theorem cell23_5864642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 5, 1, 1, 2, 1, 1, 2, 3, 1, 3].length) (baseStart_5864642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864642 prefixEnd_5864642 := by exact prefixLift 5864642
  have htrace : WordTrace (prefixWord ++ tailWord_5864642) baseStart_5864642 baseEnd_5864642 := by
    simpa [prefixWord, tailWord_5864642, baseEnd_5864642] using wordTrace_append hprefix tailTrace_5864642
  have hstable : (prefixWord ++ tailWord_5864642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864642).length < 2 ^ (prefixWord ++ tailWord_5864642).sum := by decide
  have hdescent : baseEnd_5864642 < baseStart_5864642 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864647 : List Nat := [1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 7]
def baseStart_5864647 : Nat := 118140960795 + 5864647 * 2 ^ 59
def prefixEnd_5864647 : Nat := 4983230072969 + 3 ^ 40 * 5864647 * 2
def baseEnd_5864647 : Nat := 3011382779948621275341485

theorem tailTrace_5864647 : CollatzResearch.WordTrace tailWord_5864647 prefixEnd_5864647 3011382779948621275341485 := by
  unfold tailWord_5864647
  simp only [CollatzResearch.WordTrace]
  refine ⟨213901248784392995811104195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142600832522928663874069463 213901248784392995811104195)
  ·
    refine ⟨320851873176589493716656293, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213901248784392995811104195 320851873176589493716656293)
    ·
      refine ⟨60159726220610530071873055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320851873176589493716656293 60159726220610530071873055)
      ·
        refine ⟨90239589330915795107809583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60159726220610530071873055 90239589330915795107809583)
        ·
          refine ⟨135359383996373692661714375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90239589330915795107809583 135359383996373692661714375)
          ·
            refine ⟨203039075994560538992571563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135359383996373692661714375 203039075994560538992571563)
            ·
              refine ⟨304558613991840808488857345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203039075994560538992571563 304558613991840808488857345)
              ·
                refine ⟨228418960493880606366643009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 304558613991840808488857345 228418960493880606366643009)
                ·
                  refine ⟨171314220370410454774982257, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 228418960493880606366643009 171314220370410454774982257)
                  ·
                    refine ⟨128485665277807841081236693, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 171314220370410454774982257 128485665277807841081236693)
                    ·
                      refine ⟨3011382779948621275341485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128485665277807841081236693 3011382779948621275341485)
                      ·
                        rfl

theorem cell23_5864647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 2, 2, 7].length) (baseStart_5864647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864647 prefixEnd_5864647 := by exact prefixLift 5864647
  have htrace : WordTrace (prefixWord ++ tailWord_5864647) baseStart_5864647 baseEnd_5864647 := by
    simpa [prefixWord, tailWord_5864647, baseEnd_5864647] using wordTrace_append hprefix tailTrace_5864647
  have hstable : (prefixWord ++ tailWord_5864647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864647).length < 2 ^ (prefixWord ++ tailWord_5864647).sum := by decide
  have hdescent : baseEnd_5864647 < baseStart_5864647 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864661 : List Nat := [1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 4]
def baseStart_5864661 : Nat := 118140960795 + 5864661 * 2 ^ 59
def prefixEnd_5864661 : Nat := 4983230072969 + 3 ^ 40 * 5864661 * 2
def baseEnd_5864661 : Nat := 3011389968677784220566421

theorem tailTrace_5864661 : CollatzResearch.WordTrace tailWord_5864661 prefixEnd_5864661 3011389968677784220566421 := by
  unfold tailWord_5864661
  simp only [CollatzResearch.WordTrace]
  refine ⟨213901759406342276202113837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142601172937561517468075891 213901759406342276202113837)
  ·
    refine ⟨80213159777378353575792689, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213901759406342276202113837 80213159777378353575792689)
    ·
      refine ⟨60159869833033765181844517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80213159777378353575792689 60159869833033765181844517)
      ·
        refine ⟨11279975593693830971595847, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60159869833033765181844517 11279975593693830971595847)
        ·
          refine ⟨16919963390540746457393771, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11279975593693830971595847 16919963390540746457393771)
          ·
            refine ⟨25379945085811119686090657, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16919963390540746457393771 25379945085811119686090657)
            ·
              refine ⟨19034958814358339764567993, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25379945085811119686090657 19034958814358339764567993)
              ·
                refine ⟨14276219110768754823425995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19034958814358339764567993 14276219110768754823425995)
                ·
                  refine ⟨21414328666153132235138993, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14276219110768754823425995 21414328666153132235138993)
                  ·
                    refine ⟨16060746499614849176354245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21414328666153132235138993 16060746499614849176354245)
                    ·
                      refine ⟨3011389968677784220566421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16060746499614849176354245 3011389968677784220566421)
                      ·
                        rfl

theorem cell23_5864661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 2, 1, 2, 4].length) (baseStart_5864661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864661 prefixEnd_5864661 := by exact prefixLift 5864661
  have htrace : WordTrace (prefixWord ++ tailWord_5864661) baseStart_5864661 baseEnd_5864661 := by
    simpa [prefixWord, tailWord_5864661, baseEnd_5864661] using wordTrace_append hprefix tailTrace_5864661
  have hstable : (prefixWord ++ tailWord_5864661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864661).length < 2 ^ (prefixWord ++ tailWord_5864661).sum := by decide
  have hdescent : baseEnd_5864661 < baseStart_5864661 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864662 : List Nat := [5, 2, 1, 2, 2, 2, 2, 1, 1, 5]
def baseStart_5864662 : Nat := 118140960795 + 5864662 * 2 ^ 59
def prefixEnd_5864662 : Nat := 4983230072969 + 3 ^ 40 * 5864662 * 2
def baseEnd_5864662 : Nat := 1003796827386146238884639

theorem tailTrace_5864662 : CollatzResearch.WordTrace tailWord_5864662 prefixEnd_5864662 1003796827386146238884639 := by
  unfold tailWord_5864662
  simp only [CollatzResearch.WordTrace]
  refine ⟨13368862242458665835806265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 142601197252892435581933493 13368862242458665835806265)
  ·
    refine ⟨10026646681843999376854699, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 13368862242458665835806265 10026646681843999376854699)
    ·
      refine ⟨15039970022765999065282049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10026646681843999376854699 15039970022765999065282049)
      ·
        refine ⟨11279977517074499298961537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15039970022765999065282049 11279977517074499298961537)
        ·
          refine ⟨8459983137805874474221153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11279977517074499298961537 8459983137805874474221153)
          ·
            refine ⟨6344987353354405855665865, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8459983137805874474221153 6344987353354405855665865)
            ·
              refine ⟨4758740515015804391749399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6344987353354405855665865 4758740515015804391749399)
              ·
                refine ⟨7138110772523706587624099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758740515015804391749399 7138110772523706587624099)
                ·
                  refine ⟨10707166158785559881436149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138110772523706587624099 10707166158785559881436149)
                  ·
                    refine ⟨1003796827386146238884639, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10707166158785559881436149 1003796827386146238884639)
                    ·
                      rfl

theorem cell23_5864662_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 2, 1, 1, 5].length) (baseStart_5864662 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864662 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864662 prefixEnd_5864662 := by exact prefixLift 5864662
  have htrace : WordTrace (prefixWord ++ tailWord_5864662) baseStart_5864662 baseEnd_5864662 := by
    simpa [prefixWord, tailWord_5864662, baseEnd_5864662] using wordTrace_append hprefix tailTrace_5864662
  have hstable : (prefixWord ++ tailWord_5864662).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864662).length < 2 ^ (prefixWord ++ tailWord_5864662).sum := by decide
  have hdescent : baseEnd_5864662 < baseStart_5864662 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864662) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864692 : List Nat := [2, 6, 1, 2, 1, 2, 1, 1, 1, 6]
def baseStart_5864692 : Nat := 118140960795 + 5864692 * 2 ^ 59
def prefixEnd_5864692 : Nat := 4983230072969 + 3 ^ 40 * 5864692 * 2
def baseEnd_5864692 : Nat := 1003801962192691199759593

theorem tailTrace_5864692 : CollatzResearch.WordTrace tailWord_5864692 prefixEnd_5864692 1003801962192691199759593 := by
  unfold tailWord_5864692
  simp only [CollatzResearch.WordTrace]
  refine ⟨106951445034614984248246165, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142601926712819978997661553 106951445034614984248246165)
  ·
    refine ⟨5013348985997577386636539, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 106951445034614984248246165 5013348985997577386636539)
    ·
      refine ⟨7520023478996366079954809, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5013348985997577386636539 7520023478996366079954809)
      ·
        refine ⟨5640017609247274559966107, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 7520023478996366079954809 5640017609247274559966107)
        ·
          refine ⟨8460026413870911839949161, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640017609247274559966107 8460026413870911839949161)
          ·
            refine ⟨6345019810403183879961871, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8460026413870911839949161 6345019810403183879961871)
            ·
              refine ⟨9517529715604775819942807, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345019810403183879961871 9517529715604775819942807)
              ·
                refine ⟨14276294573407163729914211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9517529715604775819942807 14276294573407163729914211)
                ·
                  refine ⟨21414441860110745594871317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14276294573407163729914211 21414441860110745594871317)
                  ·
                    refine ⟨1003801962192691199759593, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21414441860110745594871317 1003801962192691199759593)
                    ·
                      rfl

theorem cell23_5864692_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 6, 1, 2, 1, 2, 1, 1, 1, 6].length) (baseStart_5864692 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864692 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864692 prefixEnd_5864692 := by exact prefixLift 5864692
  have htrace : WordTrace (prefixWord ++ tailWord_5864692) baseStart_5864692 baseEnd_5864692 := by
    simpa [prefixWord, tailWord_5864692, baseEnd_5864692] using wordTrace_append hprefix tailTrace_5864692
  have hstable : (prefixWord ++ tailWord_5864692).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864692).length < 2 ^ (prefixWord ++ tailWord_5864692).sum := by decide
  have hdescent : baseEnd_5864692 < baseStart_5864692 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864692) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864721 : List Nat := [1, 2, 2, 1, 1, 4, 2, 1, 3, 4, 2]
def baseStart_5864721 : Nat := 118140960795 + 5864721 * 2 ^ 59
def prefixEnd_5864721 : Nat := 4983230072969 + 3 ^ 40 * 5864721 * 2
def baseEnd_5864721 : Nat := 3011420777517053985816145

theorem tailTrace_5864721 : CollatzResearch.WordTrace tailWord_5864721 prefixEnd_5864721 3011420777517053985816145 := by
  unfold tailWord_5864721
  simp only [CollatzResearch.WordTrace]
  refine ⟨213903947786124906449298017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142602631857416604299532011 213903947786124906449298017)
  ·
    refine ⟨160427960839593679836973513, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213903947786124906449298017 160427960839593679836973513)
    ·
      refine ⟨120320970629695259877730135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160427960839593679836973513 120320970629695259877730135)
      ·
        refine ⟨180481455944542889816595203, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120320970629695259877730135 180481455944542889816595203)
        ·
          refine ⟨270722183916814334724892805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180481455944542889816595203 270722183916814334724892805)
          ·
            refine ⟨50760409484402687760917401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270722183916814334724892805 50760409484402687760917401)
            ·
              refine ⟨38070307113302015820688051, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50760409484402687760917401 38070307113302015820688051)
              ·
                refine ⟨57105460669953023731032077, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38070307113302015820688051 57105460669953023731032077)
                ·
                  refine ⟨21414547751232383899137029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 57105460669953023731032077 21414547751232383899137029)
                  ·
                    refine ⟨4015227703356071981088193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21414547751232383899137029 4015227703356071981088193)
                    ·
                      refine ⟨3011420777517053985816145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015227703356071981088193 3011420777517053985816145)
                      ·
                        rfl

theorem cell23_5864721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 1, 4, 2, 1, 3, 4, 2].length) (baseStart_5864721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864721 prefixEnd_5864721 := by exact prefixLift 5864721
  have htrace : WordTrace (prefixWord ++ tailWord_5864721) baseStart_5864721 baseEnd_5864721 := by
    simpa [prefixWord, tailWord_5864721, baseEnd_5864721] using wordTrace_append hprefix tailTrace_5864721
  have hstable : (prefixWord ++ tailWord_5864721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864721).length < 2 ^ (prefixWord ++ tailWord_5864721).sum := by decide
  have hdescent : baseEnd_5864721 < baseStart_5864721 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864749 : List Nat := [1, 5, 3, 1, 1, 3, 2, 1, 2, 1, 3]
def baseStart_5864749 : Nat := 118140960795 + 5864749 * 2 ^ 59
def prefixEnd_5864749 : Nat := 4983230072969 + 3 ^ 40 * 5864749 * 2
def baseEnd_5864749 : Nat := 3011435154975379876266017

theorem tailTrace_5864749 : CollatzResearch.WordTrace tailWord_5864749 prefixEnd_5864749 3011435154975379876266017 := by
  unfold tailWord_5864749
  simp only [CollatzResearch.WordTrace]
  refine ⟨213904969030023467231317301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142603312686682311487544867 213904969030023467231317301)
  ·
    refine ⟨20053590846564700052935997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213904969030023467231317301 20053590846564700052935997)
    ·
      refine ⟨7520096567461762519850999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 20053590846564700052935997 7520096567461762519850999)
      ·
        refine ⟨11280144851192643779776499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7520096567461762519850999 11280144851192643779776499)
        ·
          refine ⟨16920217276788965669664749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11280144851192643779776499 16920217276788965669664749)
          ·
            refine ⟨6345081478795862126124281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 16920217276788965669664749 6345081478795862126124281)
            ·
              refine ⟨4758811109096896594593211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6345081478795862126124281 4758811109096896594593211)
              ·
                refine ⟨7138216663645344891889817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4758811109096896594593211 7138216663645344891889817)
                ·
                  refine ⟨5353662497734008668917363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7138216663645344891889817 5353662497734008668917363)
                  ·
                    refine ⟨8030493746601013003376045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5353662497734008668917363 8030493746601013003376045)
                    ·
                      refine ⟨3011435154975379876266017, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8030493746601013003376045 3011435154975379876266017)
                      ·
                        rfl

theorem cell23_5864749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 3, 1, 1, 3, 2, 1, 2, 1, 3].length) (baseStart_5864749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864749 prefixEnd_5864749 := by exact prefixLift 5864749
  have htrace : WordTrace (prefixWord ++ tailWord_5864749) baseStart_5864749 baseEnd_5864749 := by
    simpa [prefixWord, tailWord_5864749, baseEnd_5864749] using wordTrace_append hprefix tailTrace_5864749
  have hstable : (prefixWord ++ tailWord_5864749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864749).length < 2 ^ (prefixWord ++ tailWord_5864749).sum := by decide
  have hdescent : baseEnd_5864749 < baseStart_5864749 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864755 : List Nat := [1, 1, 1, 2, 5, 3, 1, 3, 2, 2, 2]
def baseStart_5864755 : Nat := 118140960795 + 5864755 * 2 ^ 59
def prefixEnd_5864755 : Nat := 4983230072969 + 3 ^ 40 * 5864755 * 2
def baseEnd_5864755 : Nat := 3011438235859306852790989

theorem tailTrace_5864755 : CollatzResearch.WordTrace tailWord_5864755 prefixEnd_5864755 3011438235859306852790989 := by
  unfold tailWord_5864755
  simp only [CollatzResearch.WordTrace]
  refine ⟨213905187868001730256035719, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142603458578667820170690479 213905187868001730256035719)
  ·
    refine ⟨320857781802002595384053579, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213905187868001730256035719 320857781802002595384053579)
    ·
      refine ⟨481286672703003893076080369, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320857781802002595384053579 481286672703003893076080369)
      ·
        refine ⟨360965004527252919807060277, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481286672703003893076080369 360965004527252919807060277)
        ·
          refine ⟨33840469174429961231911901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 360965004527252919807060277 33840469174429961231911901)
          ·
            refine ⟨12690175940411235461966963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33840469174429961231911901 12690175940411235461966963)
            ·
              refine ⟨19035263910616853192950445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12690175940411235461966963 19035263910616853192950445)
              ·
                refine ⟨7138223966481319947356417, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19035263910616853192950445 7138223966481319947356417)
                ·
                  refine ⟨5353667974860989960517313, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7138223966481319947356417 5353667974860989960517313)
                  ·
                    refine ⟨4015250981145742470387985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5353667974860989960517313 4015250981145742470387985)
                    ·
                      refine ⟨3011438235859306852790989, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015250981145742470387985 3011438235859306852790989)
                      ·
                        rfl

theorem cell23_5864755_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 5, 3, 1, 3, 2, 2, 2].length) (baseStart_5864755 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864755 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864755 prefixEnd_5864755 := by exact prefixLift 5864755
  have htrace : WordTrace (prefixWord ++ tailWord_5864755) baseStart_5864755 baseEnd_5864755 := by
    simpa [prefixWord, tailWord_5864755, baseEnd_5864755] using wordTrace_append hprefix tailTrace_5864755
  have hstable : (prefixWord ++ tailWord_5864755).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864755).length < 2 ^ (prefixWord ++ tailWord_5864755).sum := by decide
  have hdescent : baseEnd_5864755 < baseStart_5864755 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864755) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864784 : List Nat := [2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5]
def baseStart_5864784 : Nat := 118140960795 + 5864784 * 2 ^ 59
def prefixEnd_5864784 : Nat := 4983230072969 + 3 ^ 40 * 5864784 * 2
def baseEnd_5864784 : Nat := 3011453126798287239328355

theorem tailTrace_5864784 : CollatzResearch.WordTrace tailWord_5864784 prefixEnd_5864784 3011453126798287239328355 := by
  unfold tailWord_5864784
  simp only [CollatzResearch.WordTrace]
  refine ⟨106953122792448334104420703, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142604163723264445472560937 106953122792448334104420703)
  ·
    refine ⟨160429684188672501156631055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106953122792448334104420703 160429684188672501156631055)
    ·
      refine ⟨240644526283008751734946583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160429684188672501156631055 240644526283008751734946583)
      ·
        refine ⟨360966789424513127602419875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240644526283008751734946583 360966789424513127602419875)
        ·
          refine ⟨541450184136769691403629813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360966789424513127602419875 541450184136769691403629813)
          ·
            refine ⟨50760954762822158569090295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 541450184136769691403629813 50760954762822158569090295)
            ·
              refine ⟨76141432144233237853635443, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50760954762822158569090295 76141432144233237853635443)
              ·
                refine ⟨114212148216349856780453165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76141432144233237853635443 114212148216349856780453165)
                ·
                  refine ⟨42829555581131196292669937, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114212148216349856780453165 42829555581131196292669937)
                  ·
                    refine ⟨32122166685848397219502453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42829555581131196292669937 32122166685848397219502453)
                    ·
                      refine ⟨3011453126798287239328355, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32122166685848397219502453 3011453126798287239328355)
                      ·
                        rfl

theorem cell23_5864784_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 5, 1, 1, 3, 2, 5].length) (baseStart_5864784 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864784 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864784 prefixEnd_5864784 := by exact prefixLift 5864784
  have htrace : WordTrace (prefixWord ++ tailWord_5864784) baseStart_5864784 baseEnd_5864784 := by
    simpa [prefixWord, tailWord_5864784, baseEnd_5864784] using wordTrace_append hprefix tailTrace_5864784
  have hstable : (prefixWord ++ tailWord_5864784).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864784).length < 2 ^ (prefixWord ++ tailWord_5864784).sum := by decide
  have hdescent : baseEnd_5864784 < baseStart_5864784 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864784) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864791 : List Nat := [1, 1, 3, 2, 3, 2, 2, 2, 2, 5]
def baseStart_5864791 : Nat := 118140960795 + 5864791 * 2 ^ 59
def prefixEnd_5864791 : Nat := 4983230072969 + 3 ^ 40 * 5864791 * 2
def baseEnd_5864791 : Nat := 1003818907054289570646941

theorem tailTrace_5864791 : CollatzResearch.WordTrace tailWord_5864791 prefixEnd_5864791 1003818907054289570646941 := by
  unfold tailWord_5864791
  simp only [CollatzResearch.WordTrace]
  refine ⟨213906500895871308404346227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142604333930580872269564151 213906500895871308404346227)
  ·
    refine ⟨320859751343806962606519341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213906500895871308404346227 320859751343806962606519341)
    ·
      refine ⟨120322406753927610977444753, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320859751343806962606519341 120322406753927610977444753)
      ·
        refine ⟨90241805065445708233083565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120322406753927610977444753 90241805065445708233083565)
        ·
          refine ⟨33840676899542140587406337, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90241805065445708233083565 33840676899542140587406337)
          ·
            refine ⟨25380507674656605440554753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33840676899542140587406337 25380507674656605440554753)
            ·
              refine ⟨19035380755992454080416065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25380507674656605440554753 19035380755992454080416065)
              ·
                refine ⟨14276535566994340560312049, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19035380755992454080416065 14276535566994340560312049)
                ·
                  refine ⟨10707401675245755420234037, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14276535566994340560312049 10707401675245755420234037)
                  ·
                    refine ⟨1003818907054289570646941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10707401675245755420234037 1003818907054289570646941)
                    ·
                      rfl

theorem cell23_5864791_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 2, 2, 5].length) (baseStart_5864791 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864791 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864791 prefixEnd_5864791 := by exact prefixLift 5864791
  have htrace : WordTrace (prefixWord ++ tailWord_5864791) baseStart_5864791 baseEnd_5864791 := by
    simpa [prefixWord, tailWord_5864791, baseEnd_5864791] using wordTrace_append hprefix tailTrace_5864791
  have hstable : (prefixWord ++ tailWord_5864791).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864791).length < 2 ^ (prefixWord ++ tailWord_5864791).sum := by decide
  have hdescent : baseEnd_5864791 < baseStart_5864791 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864791) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864824 : List Nat := [2, 1, 2, 1, 1, 1, 1, 1, 6, 1, 6]
def baseStart_5864824 : Nat := 118140960795 + 5864824 * 2 ^ 59
def prefixEnd_5864824 : Nat := 4983230072969 + 3 ^ 40 * 5864824 * 2
def baseEnd_5864824 : Nat := 3011473666024467082828171

theorem tailTrace_5864824 : CollatzResearch.WordTrace tailWord_5864824 prefixEnd_5864824 3011473666024467082828171 := by
  unfold tailWord_5864824
  simp only [CollatzResearch.WordTrace]
  refine ⟨106953852252375877520148763, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142605136336501170026865017 106953852252375877520148763)
  ·
    refine ⟨160430778378563816280223145, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106953852252375877520148763 160430778378563816280223145)
    ·
      refine ⟨120323083783922862210167359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160430778378563816280223145 120323083783922862210167359)
      ·
        refine ⟨180484625675884293315251039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120323083783922862210167359 180484625675884293315251039)
        ·
          refine ⟨270726938513826439972876559, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180484625675884293315251039 270726938513826439972876559)
          ·
            refine ⟨406090407770739659959314839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270726938513826439972876559 406090407770739659959314839)
            ·
              refine ⟨609135611656109489938972259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406090407770739659959314839 609135611656109489938972259)
              ·
                refine ⟨913703417484164234908458389, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 609135611656109489938972259 913703417484164234908458389)
                ·
                  refine ⟨42829847694570198511333987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 913703417484164234908458389 42829847694570198511333987)
                  ·
                    refine ⟨64244771541855297767000981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 42829847694570198511333987 64244771541855297767000981)
                    ·
                      refine ⟨3011473666024467082828171, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64244771541855297767000981 3011473666024467082828171)
                      ·
                        rfl

theorem cell23_5864824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 1, 1, 6, 1, 6].length) (baseStart_5864824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864824 prefixEnd_5864824 := by exact prefixLift 5864824
  have htrace : WordTrace (prefixWord ++ tailWord_5864824) baseStart_5864824 baseEnd_5864824 := by
    simpa [prefixWord, tailWord_5864824, baseEnd_5864824] using wordTrace_append hprefix tailTrace_5864824
  have hstable : (prefixWord ++ tailWord_5864824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864824).length < 2 ^ (prefixWord ++ tailWord_5864824).sum := by decide
  have hdescent : baseEnd_5864824 < baseStart_5864824 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864871 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 6]
def baseStart_5864871 : Nat := 118140960795 + 5864871 * 2 ^ 59
def prefixEnd_5864871 : Nat := 4983230072969 + 3 ^ 40 * 5864871 * 2
def baseEnd_5864871 : Nat := 3011497799615228398940455

theorem tailTrace_5864871 : CollatzResearch.WordTrace tailWord_5864871 prefixEnd_5864871 3011497799615228398940455 := by
  unfold tailWord_5864871
  simp only [CollatzResearch.WordTrace]
  refine ⟨213909418735581482067258467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142606279157054321378172311 213909418735581482067258467)
  ·
    refine ⟨320864128103372223100887701, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213909418735581482067258467 320864128103372223100887701)
    ·
      refine ⟨15040506004845572957854111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 320864128103372223100887701 15040506004845572957854111)
      ·
        refine ⟨22560759007268359436781167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15040506004845572957854111 22560759007268359436781167)
        ·
          refine ⟨33841138510902539155171751, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22560759007268359436781167 33841138510902539155171751)
          ·
            refine ⟨50761707766353808732757627, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33841138510902539155171751 50761707766353808732757627)
            ·
              refine ⟨76142561649530713099136441, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50761707766353808732757627 76142561649530713099136441)
              ·
                refine ⟨57106921237148034824352331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76142561649530713099136441 57106921237148034824352331)
                ·
                  refine ⟨85660381855722052236528497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57106921237148034824352331 85660381855722052236528497)
                  ·
                    refine ⟨64245286391791539177396373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85660381855722052236528497 64245286391791539177396373)
                    ·
                      refine ⟨3011497799615228398940455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64245286391791539177396373 3011497799615228398940455)
                      ·
                        rfl

theorem cell23_5864871_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 1, 2, 6].length) (baseStart_5864871 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864871 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864871 prefixEnd_5864871 := by exact prefixLift 5864871
  have htrace : WordTrace (prefixWord ++ tailWord_5864871) baseStart_5864871 baseEnd_5864871 := by
    simpa [prefixWord, tailWord_5864871, baseEnd_5864871] using wordTrace_append hprefix tailTrace_5864871
  have hstable : (prefixWord ++ tailWord_5864871).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864871).length < 2 ^ (prefixWord ++ tailWord_5864871).sum := by decide
  have hdescent : baseEnd_5864871 < baseStart_5864871 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864871) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864888 : List Nat := [2, 1, 2, 1, 2, 2, 4, 1, 1, 5, 2]
def baseStart_5864888 : Nat := 118140960795 + 5864888 * 2 ^ 59
def prefixEnd_5864888 : Nat := 4983230072969 + 3 ^ 40 * 5864888 * 2
def baseEnd_5864888 : Nat := 3011506528786354832427877

theorem tailTrace_5864888 : CollatzResearch.WordTrace tailWord_5864888 prefixEnd_5864888 3011506528786354832427877 := by
  unfold tailWord_5864888
  simp only [CollatzResearch.WordTrace]
  refine ⟨106955019388259946985313659, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142606692517679929313751545 106955019388259946985313659)
  ·
    refine ⟨160432529082389920477970489, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106955019388259946985313659 160432529082389920477970489)
    ·
      refine ⟨120324396811792440358477867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160432529082389920477970489 120324396811792440358477867)
      ·
        refine ⟨180486595217688660537716801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120324396811792440358477867 180486595217688660537716801)
        ·
          refine ⟨135364946413266495403287601, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180486595217688660537716801 135364946413266495403287601)
          ·
            refine ⟨101523709809949871552465701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135364946413266495403287601 101523709809949871552465701)
            ·
              refine ⟨19035695589365600916087319, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101523709809949871552465701 19035695589365600916087319)
              ·
                refine ⟨28553543384048401374130979, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19035695589365600916087319 28553543384048401374130979)
                ·
                  refine ⟨42830315076072602061196469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28553543384048401374130979 42830315076072602061196469)
                  ·
                    refine ⟨4015342038381806443237169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 42830315076072602061196469 4015342038381806443237169)
                    ·
                      refine ⟨3011506528786354832427877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015342038381806443237169 3011506528786354832427877)
                      ·
                        rfl

theorem cell23_5864888_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 2, 4, 1, 1, 5, 2].length) (baseStart_5864888 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864888 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864888 prefixEnd_5864888 := by exact prefixLift 5864888
  have htrace : WordTrace (prefixWord ++ tailWord_5864888) baseStart_5864888 baseEnd_5864888 := by
    simpa [prefixWord, tailWord_5864888, baseEnd_5864888] using wordTrace_append hprefix tailTrace_5864888
  have hstable : (prefixWord ++ tailWord_5864888).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864888).length < 2 ^ (prefixWord ++ tailWord_5864888).sum := by decide
  have hdescent : baseEnd_5864888 < baseStart_5864888 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864888) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864889 : List Nat := [1, 2, 1, 4, 5, 1, 1, 3, 1, 4]
def baseStart_5864889 : Nat := 118140960795 + 5864889 * 2 ^ 59
def prefixEnd_5864889 : Nat := 4983230072969 + 3 ^ 40 * 5864889 * 2
def baseEnd_5864889 : Nat := 1003835680755669776171791

theorem tailTrace_5864889 : CollatzResearch.WordTrace tailWord_5864889 prefixEnd_5864889 1003835680755669776171791 := by
  unfold tailWord_5864889
  simp only [CollatzResearch.WordTrace]
  refine ⟨213910075249516271141413721, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142606716833010847427609147 213910075249516271141413721)
  ·
    refine ⟨160432556437137203356060291, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213910075249516271141413721 160432556437137203356060291)
    ·
      refine ⟨240648834655705805034090437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160432556437137203356060291 240648834655705805034090437)
      ·
        refine ⟨45121656497944838443891957, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 240648834655705805034090437 45121656497944838443891957)
        ·
          refine ⟨4230155296682328604114871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 45121656497944838443891957 4230155296682328604114871)
          ·
            refine ⟨6345232945023492906172307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230155296682328604114871 6345232945023492906172307)
            ·
              refine ⟨9517849417535239359258461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345232945023492906172307 9517849417535239359258461)
              ·
                refine ⟨3569193531575714759721923, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9517849417535239359258461 3569193531575714759721923)
                ·
                  refine ⟨5353790297363572139582885, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569193531575714759721923 5353790297363572139582885)
                  ·
                    refine ⟨1003835680755669776171791, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5353790297363572139582885 1003835680755669776171791)
                    ·
                      rfl

theorem cell23_5864889_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 5, 1, 1, 3, 1, 4].length) (baseStart_5864889 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864889 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864889 prefixEnd_5864889 := by exact prefixLift 5864889
  have htrace : WordTrace (prefixWord ++ tailWord_5864889) baseStart_5864889 baseEnd_5864889 := by
    simpa [prefixWord, tailWord_5864889, baseEnd_5864889] using wordTrace_append hprefix tailTrace_5864889
  have hstable : (prefixWord ++ tailWord_5864889).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864889).length < 2 ^ (prefixWord ++ tailWord_5864889).sum := by decide
  have hdescent : baseEnd_5864889 < baseStart_5864889 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864889) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864935 : List Nat := [1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 4]
def baseStart_5864935 : Nat := 118140960795 + 5864935 * 2 ^ 59
def prefixEnd_5864935 : Nat := 4983230072969 + 3 ^ 40 * 5864935 * 2
def baseEnd_5864935 : Nat := 3011530662377116148540161

theorem tailTrace_5864935 : CollatzResearch.WordTrace tailWord_5864935 prefixEnd_5864935 3011530662377116148540161 := by
  unfold tailWord_5864935
  simp only [CollatzResearch.WordTrace]
  refine ⟨213911753007349620997588259, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142607835338233080665058839 213911753007349620997588259)
  ·
    refine ⟨320867629511024431496382389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213911753007349620997588259 320867629511024431496382389)
    ·
      refine ⟨30081340266658540452785849, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320867629511024431496382389 30081340266658540452785849)
      ·
        refine ⟨22561005199993905339589387, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30081340266658540452785849 22561005199993905339589387)
        ·
          refine ⟨33841507799990858009384081, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22561005199993905339589387 33841507799990858009384081)
          ·
            refine ⟨25381130849993143507038061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33841507799990858009384081 25381130849993143507038061)
            ·
              refine ⟨9517924068747428815139273, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25381130849993143507038061 9517924068747428815139273)
              ·
                refine ⟨7138443051560571611354455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9517924068747428815139273 7138443051560571611354455)
                ·
                  refine ⟨10707664577340857417031683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138443051560571611354455 10707664577340857417031683)
                  ·
                    refine ⟨16061496866011286125547525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10707664577340857417031683 16061496866011286125547525)
                    ·
                      refine ⟨3011530662377116148540161, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16061496866011286125547525 3011530662377116148540161)
                      ·
                        rfl

theorem cell23_5864935_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 2, 1, 2, 3, 2, 1, 1, 4].length) (baseStart_5864935 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864935 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864935 prefixEnd_5864935 := by exact prefixLift 5864935
  have htrace : WordTrace (prefixWord ++ tailWord_5864935) baseStart_5864935 baseEnd_5864935 := by
    simpa [prefixWord, tailWord_5864935, baseEnd_5864935] using wordTrace_append hprefix tailTrace_5864935
  have hstable : (prefixWord ++ tailWord_5864935).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864935).length < 2 ^ (prefixWord ++ tailWord_5864935).sum := by decide
  have hdescent : baseEnd_5864935 < baseStart_5864935 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864935) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864958 : List Nat := [4, 2, 2, 3, 12]
def baseStart_5864958 : Nat := 118140960795 + 5864958 * 2 ^ 59
def prefixEnd_5864958 : Nat := 4983230072969 + 3 ^ 40 * 5864958 * 2
def baseEnd_5864958 : Nat := 4131059632965939037795

theorem tailTrace_5864958 : CollatzResearch.WordTrace tailWord_5864958 prefixEnd_5864958 4131059632965939037795 := by
  unfold tailWord_5864958
  simp only [CollatzResearch.WordTrace]
  refine ⟨26739073985783286990709441, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142608394590844197283783685 26739073985783286990709441)
  ·
    refine ⟨20054305489337465243032081, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 26739073985783286990709441 20054305489337465243032081)
    ·
      refine ⟨15040729117003098932274061, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 20054305489337465243032081 15040729117003098932274061)
      ·
        refine ⟨5640273418876162099602773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 15040729117003098932274061 5640273418876162099602773)
        ·
          refine ⟨4131059632965939037795, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 12 5640273418876162099602773 4131059632965939037795)
          ·
            rfl

theorem cell23_5864958_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 2, 3, 12].length) (baseStart_5864958 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864958 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864958 prefixEnd_5864958 := by exact prefixLift 5864958
  have htrace : WordTrace (prefixWord ++ tailWord_5864958) baseStart_5864958 baseEnd_5864958 := by
    simpa [prefixWord, tailWord_5864958, baseEnd_5864958] using wordTrace_append hprefix tailTrace_5864958
  have hstable : (prefixWord ++ tailWord_5864958).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864958).length < 2 ^ (prefixWord ++ tailWord_5864958).sum := by decide
  have hdescent : baseEnd_5864958 < baseStart_5864958 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864958) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864962 : List Nat := [3, 4, 1, 2, 1, 1, 1, 4, 2, 4]
def baseStart_5864962 : Nat := 118140960795 + 5864962 * 2 ^ 59
def prefixEnd_5864962 : Nat := 4983230072969 + 3 ^ 40 * 5864962 * 2
def baseEnd_5864962 : Nat := 1003848175451595847634179

theorem tailTrace_5864962 : CollatzResearch.WordTrace tailWord_5864962 prefixEnd_5864962 1003848175451595847634179 := by
  unfold tailWord_5864962
  simp only [CollatzResearch.WordTrace]
  refine ⟨53478184444562951152205285, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142608491852167869739214093 53478184444562951152205285)
  ·
    refine ⟨10027159583355553341038491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 53478184444562951152205285 10027159583355553341038491)
    ·
      refine ⟨15040739375033330011557737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10027159583355553341038491 15040739375033330011557737)
      ·
        refine ⟨11280554531274997508668303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15040739375033330011557737 11280554531274997508668303)
        ·
          refine ⟨16920831796912496263002455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11280554531274997508668303 16920831796912496263002455)
          ·
            refine ⟨25381247695368744394503683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16920831796912496263002455 25381247695368744394503683)
            ·
              refine ⟨38071871543053116591755525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25381247695368744394503683 38071871543053116591755525)
              ·
                refine ⟨7138475914322459360954161, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38071871543053116591755525 7138475914322459360954161)
                ·
                  refine ⟨5353856935741844520715621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7138475914322459360954161 5353856935741844520715621)
                  ·
                    refine ⟨1003848175451595847634179, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5353856935741844520715621 1003848175451595847634179)
                    ·
                      rfl

theorem cell23_5864962_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 2, 1, 1, 1, 4, 2, 4].length) (baseStart_5864962 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864962 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864962 prefixEnd_5864962 := by exact prefixLift 5864962
  have htrace : WordTrace (prefixWord ++ tailWord_5864962) baseStart_5864962 baseEnd_5864962 := by
    simpa [prefixWord, tailWord_5864962, baseEnd_5864962] using wordTrace_append hprefix tailTrace_5864962
  have hstable : (prefixWord ++ tailWord_5864962).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864962).length < 2 ^ (prefixWord ++ tailWord_5864962).sum := by decide
  have hdescent : baseEnd_5864962 < baseStart_5864962 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864962) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5864990 : List Nat := [4, 3, 3, 1, 2, 1, 1, 1, 2, 3, 2]
def baseStart_5864990 : Nat := 118140960795 + 5864990 * 2 ^ 59
def prefixEnd_5864990 : Nat := 4983230072969 + 3 ^ 40 * 5864990 * 2
def baseEnd_5864990 : Nat := 3011558903813113433352409

theorem tailTrace_5864990 : CollatzResearch.WordTrace tailWord_5864990 prefixEnd_5864990 3011558903813113433352409 := by
  unfold tailWord_5864990
  simp only [CollatzResearch.WordTrace]
  refine ⟨26739219877768795673855053, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142609172681433576927226949 26739219877768795673855053)
  ·
    refine ⟨10027207454163298377695645, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26739219877768795673855053 10027207454163298377695645)
    ·
      refine ⟨3760202795311236891635867, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 10027207454163298377695645 3760202795311236891635867)
      ·
        refine ⟨5640304192966855337453801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 3760202795311236891635867 5640304192966855337453801)
        ·
          refine ⟨4230228144725141503090351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5640304192966855337453801 4230228144725141503090351)
          ·
            refine ⟨6345342217087712254635527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230228144725141503090351 6345342217087712254635527)
            ·
              refine ⟨9518013325631568381953291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345342217087712254635527 9518013325631568381953291)
              ·
                refine ⟨14277019988447352572929937, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518013325631568381953291 14277019988447352572929937)
                ·
                  refine ⟨10707764991335514429697453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14277019988447352572929937 10707764991335514429697453)
                  ·
                    refine ⟨4015411871750817911136545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10707764991335514429697453 4015411871750817911136545)
                    ·
                      refine ⟨3011558903813113433352409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015411871750817911136545 3011558903813113433352409)
                      ·
                        rfl

theorem cell23_5864990_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 3, 1, 2, 1, 1, 1, 2, 3, 2].length) (baseStart_5864990 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5864990 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5864990 prefixEnd_5864990 := by exact prefixLift 5864990
  have htrace : WordTrace (prefixWord ++ tailWord_5864990) baseStart_5864990 baseEnd_5864990 := by
    simpa [prefixWord, tailWord_5864990, baseEnd_5864990] using wordTrace_append hprefix tailTrace_5864990
  have hstable : (prefixWord ++ tailWord_5864990).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5864990).length < 2 ^ (prefixWord ++ tailWord_5864990).sum := by decide
  have hdescent : baseEnd_5864990 < baseStart_5864990 := by decide
  rcases family_descends (prefixWord ++ tailWord_5864990) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865042 : List Nat := [3, 2, 2, 1, 2, 2, 3, 1, 1, 4, 2]
def baseStart_5865042 : Nat := 118140960795 + 5865042 * 2 ^ 59
def prefixEnd_5865042 : Nat := 4983230072969 + 3 ^ 40 * 5865042 * 2
def baseEnd_5865042 : Nat := 3011585604807147229902169

theorem tailTrace_5865042 : CollatzResearch.WordTrace tailWord_5865042 prefixEnd_5865042 3011585604807147229902169 := by
  unfold tailWord_5865042
  simp only [CollatzResearch.WordTrace]
  refine ⟨53478913904490494567933345, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142610437078641318847822253 53478913904490494567933345)
  ·
    refine ⟨40109185428367870925950009, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53478913904490494567933345 40109185428367870925950009)
    ·
      refine ⟨30081889071275903194462507, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40109185428367870925950009 30081889071275903194462507)
      ·
        refine ⟨45122833606913854791693761, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30081889071275903194462507 45122833606913854791693761)
        ·
          refine ⟨33842125205185391093770321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45122833606913854791693761 33842125205185391093770321)
          ·
            refine ⟨25381593903889043320327741, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33842125205185391093770321 25381593903889043320327741)
            ·
              refine ⟨9518097713958391245122903, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25381593903889043320327741 9518097713958391245122903)
              ·
                refine ⟨14277146570937586867684355, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518097713958391245122903 14277146570937586867684355)
                ·
                  refine ⟨21415719856406380301526533, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14277146570937586867684355 21415719856406380301526533)
                  ·
                    refine ⟨4015447473076196306536225, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21415719856406380301526533 4015447473076196306536225)
                    ·
                      refine ⟨3011585604807147229902169, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015447473076196306536225 3011585604807147229902169)
                      ·
                        rfl

theorem cell23_5865042_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 1, 2, 2, 3, 1, 1, 4, 2].length) (baseStart_5865042 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865042 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865042 prefixEnd_5865042 := by exact prefixLift 5865042
  have htrace : WordTrace (prefixWord ++ tailWord_5865042) baseStart_5865042 baseEnd_5865042 := by
    simpa [prefixWord, tailWord_5865042, baseEnd_5865042] using wordTrace_append hprefix tailTrace_5865042
  have hstable : (prefixWord ++ tailWord_5865042).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865042).length < 2 ^ (prefixWord ++ tailWord_5865042).sum := by decide
  have hdescent : baseEnd_5865042 < baseStart_5865042 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865042) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865065 : List Nat := [1, 2, 1, 1, 1, 4, 5, 3, 5]
def baseStart_5865065 : Nat := 118140960795 + 5865065 * 2 ^ 59
def prefixEnd_5865065 : Nat := 4983230072969 + 3 ^ 40 * 5865065 * 2
def baseEnd_5865065 : Nat := 334621934984688959990507

theorem tailTrace_5865065 : CollatzResearch.WordTrace tailWord_5865065 prefixEnd_5865065 334621934984688959990507 := by
  unfold tailWord_5865065
  simp only [CollatzResearch.WordTrace]
  refine ⟨213916494496878653199820649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142610996331252435466547099 213916494496878653199820649)
  ·
    refine ⟨160437370872658989899865487, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213916494496878653199820649 160437370872658989899865487)
    ·
      refine ⟨240656056308988484849798231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160437370872658989899865487 240656056308988484849798231)
      ·
        refine ⟨360984084463482727274697347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240656056308988484849798231 360984084463482727274697347)
        ·
          refine ⟨541476126695224090912046021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 360984084463482727274697347 541476126695224090912046021)
          ·
            refine ⟨101526773755354517046008629, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 541476126695224090912046021 101526773755354517046008629)
            ·
              refine ⟨9518135039564485973063309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101526773755354517046008629 9518135039564485973063309)
              ·
                refine ⟨3569300639836682239898741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9518135039564485973063309 3569300639836682239898741)
                ·
                  refine ⟨334621934984688959990507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3569300639836682239898741 334621934984688959990507)
                  ·
                    rfl

theorem cell23_5865065_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 4, 5, 3, 5].length) (baseStart_5865065 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865065 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865065 prefixEnd_5865065 := by exact prefixLift 5865065
  have htrace : WordTrace (prefixWord ++ tailWord_5865065) baseStart_5865065 baseEnd_5865065 := by
    simpa [prefixWord, tailWord_5865065, baseEnd_5865065] using wordTrace_append hprefix tailTrace_5865065
  have hstable : (prefixWord ++ tailWord_5865065).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865065).length < 2 ^ (prefixWord ++ tailWord_5865065).sum := by decide
  have hdescent : baseEnd_5865065 < baseStart_5865065 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865065) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865088 : List Nat := [2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5]
def baseStart_5865088 : Nat := 118140960795 + 5865088 * 2 ^ 59
def prefixEnd_5865088 : Nat := 4983230072969 + 3 ^ 40 * 5865088 * 2
def baseEnd_5865088 : Nat := 3011609224917254049926957

theorem tailTrace_5865088 : CollatzResearch.WordTrace tailWord_5865088 prefixEnd_5865088 3011609224917254049926957 := by
  unfold tailWord_5865088
  simp only [CollatzResearch.WordTrace]
  refine ⟨106958666687897664063953959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142611555583863552085271945 106958666687897664063953959)
  ·
    refine ⟨160438000031846496095930939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106958666687897664063953959 160438000031846496095930939)
    ·
      refine ⟨240657000047769744143896409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160438000031846496095930939 240657000047769744143896409)
      ·
        refine ⟨180492750035827308107922307, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240657000047769744143896409 180492750035827308107922307)
        ·
          refine ⟨270739125053740962161883461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180492750035827308107922307 270739125053740962161883461)
          ·
            refine ⟨50763585947576430405353149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270739125053740962161883461 50763585947576430405353149)
            ·
              refine ⟨19036344730341161402007431, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50763585947576430405353149 19036344730341161402007431)
              ·
                refine ⟨28554517095511742103011147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19036344730341161402007431 28554517095511742103011147)
                ·
                  refine ⟨42831775643267613154516721, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 28554517095511742103011147 42831775643267613154516721)
                  ·
                    refine ⟨32123831732450709865887541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 42831775643267613154516721 32123831732450709865887541)
                    ·
                      refine ⟨3011609224917254049926957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32123831732450709865887541 3011609224917254049926957)
                      ·
                        rfl

theorem cell23_5865088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 1, 1, 2, 5].length) (baseStart_5865088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865088 prefixEnd_5865088 := by exact prefixLift 5865088
  have htrace : WordTrace (prefixWord ++ tailWord_5865088) baseStart_5865088 baseEnd_5865088 := by
    simpa [prefixWord, tailWord_5865088, baseEnd_5865088] using wordTrace_append hprefix tailTrace_5865088
  have hstable : (prefixWord ++ tailWord_5865088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865088).length < 2 ^ (prefixWord ++ tailWord_5865088).sum := by decide
  have hdescent : baseEnd_5865088 < baseStart_5865088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865135 : List Nat := [1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 3]
def baseStart_5865135 : Nat := 118140960795 + 5865135 * 2 ^ 59
def prefixEnd_5865135 : Nat := 4983230072969 + 3 ^ 40 * 5865135 * 2
def baseEnd_5865135 : Nat := 3011633358508015366039241

theorem tailTrace_5865135 : CollatzResearch.WordTrace tailWord_5865135 prefixEnd_5865135 3011633358508015366039241 := by
  unfold tailWord_5865135
  simp only [CollatzResearch.WordTrace]
  refine ⟨213919047606625055154868859, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142612698404416703436579239 213919047606625055154868859)
  ·
    refine ⟨320878571409937582732303289, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213919047606625055154868859 320878571409937582732303289)
    ·
      refine ⟨240658928557453187049227467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320878571409937582732303289 240658928557453187049227467)
      ·
        refine ⟨360988392836179780573841201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240658928557453187049227467 360988392836179780573841201)
        ·
          refine ⟨270741294627134835430380901, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 360988392836179780573841201 270741294627134835430380901)
          ·
            refine ⟨50763992742587781643196419, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270741294627134835430380901 50763992742587781643196419)
            ·
              refine ⟨76145989113881672464794629, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50763992742587781643196419 76145989113881672464794629)
              ·
                refine ⟨14277372958852813587148993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76145989113881672464794629 14277372958852813587148993)
                ·
                  refine ⟨10708029719139610190361745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14277372958852813587148993 10708029719139610190361745)
                  ·
                    refine ⟨8031022289354707642771309, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10708029719139610190361745 8031022289354707642771309)
                    ·
                      refine ⟨3011633358508015366039241, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8031022289354707642771309 3011633358508015366039241)
                      ·
                        rfl

theorem cell23_5865135_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 4, 1, 4, 2, 2, 3].length) (baseStart_5865135 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865135 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865135 prefixEnd_5865135 := by exact prefixLift 5865135
  have htrace : WordTrace (prefixWord ++ tailWord_5865135) baseStart_5865135 baseEnd_5865135 := by
    simpa [prefixWord, tailWord_5865135, baseEnd_5865135] using wordTrace_append hprefix tailTrace_5865135
  have hstable : (prefixWord ++ tailWord_5865135).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865135).length < 2 ^ (prefixWord ++ tailWord_5865135).sum := by decide
  have hdescent : baseEnd_5865135 < baseStart_5865135 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865135) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865138 : List Nat := [3, 2, 1, 1, 1, 2, 2, 3, 8]
def baseStart_5865138 : Nat := 118140960795 + 5865138 * 2 ^ 59
def prefixEnd_5865138 : Nat := 4983230072969 + 3 ^ 40 * 5865138 * 2
def baseEnd_5865138 : Nat := 334626099883330983811303

theorem tailTrace_5865138 : CollatzResearch.WordTrace tailWord_5865138 prefixEnd_5865138 334626099883330983811303 := by
  unfold tailWord_5865138
  simp only [CollatzResearch.WordTrace]
  refine ⟨53479789256403546666807017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142612771350409457778152045 53479789256403546666807017)
  ·
    refine ⟨40109841942302660000105263, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53479789256403546666807017 40109841942302660000105263)
    ·
      refine ⟨60164762913453990000157895, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40109841942302660000105263 60164762913453990000157895)
      ·
        refine ⟨90247144370180985000236843, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60164762913453990000157895 90247144370180985000236843)
        ·
          refine ⟨135370716555271477500355265, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90247144370180985000236843 135370716555271477500355265)
          ·
            refine ⟨101528037416453608125266449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135370716555271477500355265 101528037416453608125266449)
            ·
              refine ⟨76146028062340206093949837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101528037416453608125266449 76146028062340206093949837)
              ·
                refine ⟨28554760523377577285231189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 76146028062340206093949837 28554760523377577285231189)
                ·
                  refine ⟨334626099883330983811303, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28554760523377577285231189 334626099883330983811303)
                  ·
                    rfl

theorem cell23_5865138_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 2, 2, 3, 8].length) (baseStart_5865138 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865138 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865138 prefixEnd_5865138 := by exact prefixLift 5865138
  have htrace : WordTrace (prefixWord ++ tailWord_5865138) baseStart_5865138 baseEnd_5865138 := by
    simpa [prefixWord, tailWord_5865138, baseEnd_5865138] using wordTrace_append hprefix tailTrace_5865138
  have hstable : (prefixWord ++ tailWord_5865138).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865138).length < 2 ^ (prefixWord ++ tailWord_5865138).sum := by decide
  have hdescent : baseEnd_5865138 < baseStart_5865138 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865138) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865199 : List Nat := [1, 1, 2, 1, 5, 1, 1, 6, 1, 1, 3]
def baseStart_5865199 : Nat := 118140960795 + 5865199 * 2 ^ 59
def prefixEnd_5865199 : Nat := 4983230072969 + 3 ^ 40 * 5865199 * 2
def baseEnd_5865199 : Nat := 3011666221269903115638947

theorem tailTrace_5865199 : CollatzResearch.WordTrace tailWord_5865199 prefixEnd_5865199 3011666221269903115638947 := by
  unfold tailWord_5865199
  simp only [CollatzResearch.WordTrace]
  refine ⟨213921381878393194085198651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142614254585595462723465767 213921381878393194085198651)
  ·
    refine ⟨320882072817589791127797977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213921381878393194085198651 320882072817589791127797977)
    ·
      refine ⟨240661554613192343345848483, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320882072817589791127797977 240661554613192343345848483)
      ·
        refine ⟨360992331919788515018772725, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240661554613192343345848483 360992331919788515018772725)
        ·
          refine ⟨33843031117480173283009943, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 360992331919788515018772725 33843031117480173283009943)
          ·
            refine ⟨50764546676220259924514915, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33843031117480173283009943 50764546676220259924514915)
            ·
              refine ⟨76146820014330389886772373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50764546676220259924514915 76146820014330389886772373)
              ·
                refine ⟨3569382188171737025942455, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 76146820014330389886772373 3569382188171737025942455)
                ·
                  refine ⟨5354073282257605538913683, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569382188171737025942455 5354073282257605538913683)
                  ·
                    refine ⟨8031109923386408308370525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5354073282257605538913683 8031109923386408308370525)
                    ·
                      refine ⟨3011666221269903115638947, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8031109923386408308370525 3011666221269903115638947)
                      ·
                        rfl

theorem cell23_5865199_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 5, 1, 1, 6, 1, 1, 3].length) (baseStart_5865199 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865199 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865199 prefixEnd_5865199 := by exact prefixLift 5865199
  have htrace : WordTrace (prefixWord ++ tailWord_5865199) baseStart_5865199 baseEnd_5865199 := by
    simpa [prefixWord, tailWord_5865199, baseEnd_5865199] using wordTrace_append hprefix tailTrace_5865199
  have hstable : (prefixWord ++ tailWord_5865199).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865199).length < 2 ^ (prefixWord ++ tailWord_5865199).sum := by decide
  have hdescent : baseEnd_5865199 < baseStart_5865199 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865199) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865215 : List Nat := [1, 1, 2, 2, 1, 3, 5, 1, 1, 6]
def baseStart_5865215 : Nat := 118140960795 + 5865215 * 2 ^ 59
def prefixEnd_5865215 : Nat := 4983230072969 + 3 ^ 40 * 5865215 * 2
def baseEnd_5865215 : Nat := 1003891478986791684346291

theorem tailTrace_5865215 : CollatzResearch.WordTrace tailWord_5865215 prefixEnd_5865215 1003891478986791684346291 := by
  unfold tailWord_5865215
  simp only [CollatzResearch.WordTrace]
  refine ⟨213921965446335228817781099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142614643630890152545187399 213921965446335228817781099)
  ·
    refine ⟨320882948169502843226671649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213921965446335228817781099 320882948169502843226671649)
    ·
      refine ⟨240662211127127132420003737, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320882948169502843226671649 240662211127127132420003737)
      ·
        refine ⟨180496658345345349315002803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240662211127127132420003737 180496658345345349315002803)
        ·
          refine ⟨270744987518018023972504205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180496658345345349315002803 270744987518018023972504205)
          ·
            refine ⟨101529370319256758989689077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270744987518018023972504205 101529370319256758989689077)
            ·
              refine ⟨9518378467430321155283351, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 101529370319256758989689077 9518378467430321155283351)
              ·
                refine ⟨14277567701145481732925027, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518378467430321155283351 14277567701145481732925027)
                ·
                  refine ⟨21416351551718222599387541, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14277567701145481732925027 21416351551718222599387541)
                  ·
                    refine ⟨1003891478986791684346291, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21416351551718222599387541 1003891478986791684346291)
                    ·
                      rfl

theorem cell23_5865215_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 3, 5, 1, 1, 6].length) (baseStart_5865215 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865215 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865215 prefixEnd_5865215 := by exact prefixLift 5865215
  have htrace : WordTrace (prefixWord ++ tailWord_5865215) baseStart_5865215 baseEnd_5865215 := by
    simpa [prefixWord, tailWord_5865215, baseEnd_5865215] using wordTrace_append hprefix tailTrace_5865215
  have hstable : (prefixWord ++ tailWord_5865215).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865215).length < 2 ^ (prefixWord ++ tailWord_5865215).sum := by decide
  have hdescent : baseEnd_5865215 < baseStart_5865215 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865215) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865242 : List Nat := [3, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5]
def baseStart_5865242 : Nat := 118140960795 + 5865242 * 2 ^ 59
def prefixEnd_5865242 : Nat := 4983230072969 + 3 ^ 40 * 5865242 * 2
def baseEnd_5865242 : Nat := 3011688300938046447401249

theorem tailTrace_5865242 : CollatzResearch.WordTrace tailWord_5865242 prefixEnd_5865242 3011688300938046447401249 := by
  unfold tailWord_5865242
  simp only [CollatzResearch.WordTrace]
  refine ⟨53480737554309353107253495, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142615300144824941619342653 53480737554309353107253495)
  ·
    refine ⟨80221106331464029660880243, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53480737554309353107253495 80221106331464029660880243)
    ·
      refine ⟨120331659497196044491320365, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80221106331464029660880243 120331659497196044491320365)
      ·
        refine ⟨45124372311448516684245137, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120331659497196044491320365 45124372311448516684245137)
        ·
          refine ⟨33843279233586387513183853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45124372311448516684245137 33843279233586387513183853)
          ·
            refine ⟨12691229712594895317443945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33843279233586387513183853 12691229712594895317443945)
            ·
              refine ⟨9518422284446171488082959, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12691229712594895317443945 9518422284446171488082959)
              ·
                refine ⟨14277633426669257232124439, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518422284446171488082959 14277633426669257232124439)
                ·
                  refine ⟨21416450140003885848186659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14277633426669257232124439 21416450140003885848186659)
                  ·
                    refine ⟨32124675210005828772279989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21416450140003885848186659 32124675210005828772279989)
                    ·
                      refine ⟨3011688300938046447401249, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32124675210005828772279989 3011688300938046447401249)
                      ·
                        rfl

theorem cell23_5865242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 2, 3, 2, 1, 1, 1, 5].length) (baseStart_5865242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865242 prefixEnd_5865242 := by exact prefixLift 5865242
  have htrace : WordTrace (prefixWord ++ tailWord_5865242) baseStart_5865242 baseEnd_5865242 := by
    simpa [prefixWord, tailWord_5865242, baseEnd_5865242] using wordTrace_append hprefix tailTrace_5865242
  have hstable : (prefixWord ++ tailWord_5865242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865242).length < 2 ^ (prefixWord ++ tailWord_5865242).sum := by decide
  have hdescent : baseEnd_5865242 < baseStart_5865242 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865256 : List Nat := [2, 1, 5, 1, 1, 2, 3, 1, 3, 2, 2]
def baseStart_5865256 : Nat := 118140960795 + 5865256 * 2 ^ 59
def prefixEnd_5865256 : Nat := 4983230072969 + 3 ^ 40 * 5865256 * 2
def baseEnd_5865256 : Nat := 3011695489667209392626185

theorem tailTrace_5865256 : CollatzResearch.WordTrace tailWord_5865256 prefixEnd_5865256 3011695489667209392626185 := by
  unfold tailWord_5865256
  simp only [CollatzResearch.WordTrace]
  refine ⟨106961730419593346410011811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142615640559457795213349081 106961730419593346410011811)
  ·
    refine ⟨160442595629390019615017717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106961730419593346410011811 160442595629390019615017717)
    ·
      refine ⟨15041493340255314338907911, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 160442595629390019615017717 15041493340255314338907911)
      ·
        refine ⟨22562240010382971508361867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15041493340255314338907911 22562240010382971508361867)
        ·
          refine ⟨33843360015574457262542801, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22562240010382971508361867 33843360015574457262542801)
          ·
            refine ⟨25382520011680842946907101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33843360015574457262542801 25382520011680842946907101)
            ·
              refine ⟨9518445004380316105090163, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25382520011680842946907101 9518445004380316105090163)
              ·
                refine ⟨14277667506570474157635245, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518445004380316105090163 14277667506570474157635245)
                ·
                  refine ⟨5354125314963927809113217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14277667506570474157635245 5354125314963927809113217)
                  ·
                    refine ⟨4015593986222945856834913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354125314963927809113217 4015593986222945856834913)
                    ·
                      refine ⟨3011695489667209392626185, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015593986222945856834913 3011695489667209392626185)
                      ·
                        rfl

theorem cell23_5865256_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 1, 1, 2, 3, 1, 3, 2, 2].length) (baseStart_5865256 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865256 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865256 prefixEnd_5865256 := by exact prefixLift 5865256
  have htrace : WordTrace (prefixWord ++ tailWord_5865256) baseStart_5865256 baseEnd_5865256 := by
    simpa [prefixWord, tailWord_5865256, baseEnd_5865256] using wordTrace_append hprefix tailTrace_5865256
  have hstable : (prefixWord ++ tailWord_5865256).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865256).length < 2 ^ (prefixWord ++ tailWord_5865256).sum := by decide
  have hdescent : baseEnd_5865256 < baseStart_5865256 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865256) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865266 : List Nat := [3, 2, 1, 1, 3, 4, 2, 1, 2, 4]
def baseStart_5865266 : Nat := 118140960795 + 5865266 * 2 ^ 59
def prefixEnd_5865266 : Nat := 4983230072969 + 3 ^ 40 * 5865266 * 2
def baseEnd_5865266 : Nat := 1003900208157918117833713

theorem tailTrace_5865266 : CollatzResearch.WordTrace tailWord_5865266 prefixEnd_5865266 1003900208157918117833713 := by
  unfold tailWord_5865266
  simp only [CollatzResearch.WordTrace]
  refine ⟨53480956392287616131971913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142615883712766976351925101 53480956392287616131971913)
  ·
    refine ⟨40110717294215712098978935, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53480956392287616131971913 40110717294215712098978935)
    ·
      refine ⟨60166075941323568148468403, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40110717294215712098978935 60166075941323568148468403)
      ·
        refine ⟨90249113911985352222702605, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60166075941323568148468403 90249113911985352222702605)
        ·
          refine ⟨33843417716994507083513477, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90249113911985352222702605 33843417716994507083513477)
          ·
            refine ⟨6345640821936470078158777, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 33843417716994507083513477 6345640821936470078158777)
            ·
              refine ⟨4759230616452352558619083, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6345640821936470078158777 4759230616452352558619083)
              ·
                refine ⟨7138845924678528837928625, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759230616452352558619083 7138845924678528837928625)
                ·
                  refine ⟨5354134443508896628446469, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7138845924678528837928625 5354134443508896628446469)
                  ·
                    refine ⟨1003900208157918117833713, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354134443508896628446469 1003900208157918117833713)
                    ·
                      rfl

theorem cell23_5865266_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 3, 4, 2, 1, 2, 4].length) (baseStart_5865266 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865266 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865266 prefixEnd_5865266 := by exact prefixLift 5865266
  have htrace : WordTrace (prefixWord ++ tailWord_5865266) baseStart_5865266 baseEnd_5865266 := by
    simpa [prefixWord, tailWord_5865266, baseEnd_5865266] using wordTrace_append hprefix tailTrace_5865266
  have hstable : (prefixWord ++ tailWord_5865266).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865266).length < 2 ^ (prefixWord ++ tailWord_5865266).sum := by decide
  have hdescent : baseEnd_5865266 < baseStart_5865266 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865266) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865273 : List Nat := [1, 2, 1, 7, 2, 1, 1, 2, 1, 1, 4]
def baseStart_5865273 : Nat := 118140960795 + 5865273 * 2 ^ 59
def prefixEnd_5865273 : Nat := 4983230072969 + 3 ^ 40 * 5865273 * 2
def baseEnd_5865273 : Nat := 3011704218838335826113607

theorem tailTrace_5865273 : CollatzResearch.WordTrace tailWord_5865273 prefixEnd_5865273 3011704218838335826113607 := by
  unfold tailWord_5865273
  simp only [CollatzResearch.WordTrace]
  refine ⟨213924080880125104723392473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142616053920083403148928315 213924080880125104723392473)
  ·
    refine ⟨160443060660093828542544355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213924080880125104723392473 160443060660093828542544355)
    ·
      refine ⟨240664590990140742813816533, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160443060660093828542544355 240664590990140742813816533)
      ·
        refine ⟨5640576351331423659698825, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 240664590990140742813816533 5640576351331423659698825)
        ·
          refine ⟨4230432263498567744774119, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 5640576351331423659698825 4230432263498567744774119)
          ·
            refine ⟨6345648395247851617161179, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4230432263498567744774119 6345648395247851617161179)
            ·
              refine ⟨9518472592871777425741769, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6345648395247851617161179 9518472592871777425741769)
              ·
                refine ⟨7138854444653833069306327, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9518472592871777425741769 7138854444653833069306327)
                ·
                  refine ⟨10708281666980749603959491, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138854444653833069306327 10708281666980749603959491)
                  ·
                    refine ⟨16062422500471124405939237, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10708281666980749603959491 16062422500471124405939237)
                    ·
                      refine ⟨3011704218838335826113607, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16062422500471124405939237 3011704218838335826113607)
                      ·
                        rfl

theorem cell23_5865273_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 7, 2, 1, 1, 2, 1, 1, 4].length) (baseStart_5865273 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865273 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865273 prefixEnd_5865273 := by exact prefixLift 5865273
  have htrace : WordTrace (prefixWord ++ tailWord_5865273) baseStart_5865273 baseEnd_5865273 := by
    simpa [prefixWord, tailWord_5865273, baseEnd_5865273] using wordTrace_append hprefix tailTrace_5865273
  have hstable : (prefixWord ++ tailWord_5865273).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865273).length < 2 ^ (prefixWord ++ tailWord_5865273).sum := by decide
  have hdescent : baseEnd_5865273 < baseStart_5865273 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865273) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865286 : List Nat := [6, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4]
def baseStart_5865286 : Nat := 118140960795 + 5865286 * 2 ^ 59
def prefixEnd_5865286 : Nat := 4983230072969 + 3 ^ 40 * 5865286 * 2
def baseEnd_5865286 : Nat := 3011710894086844275251047

theorem tailTrace_5865286 : CollatzResearch.WordTrace tailWord_5865286 prefixEnd_5865286 3011710894086844275251047 := by
  unfold tailWord_5865286
  simp only [CollatzResearch.WordTrace]
  refine ⟨6685142344658687748237991, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142616370019385338629077141 6685142344658687748237991)
  ·
    refine ⟨10027713516988031622356987, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6685142344658687748237991 10027713516988031622356987)
    ·
      refine ⟨15041570275482047433535481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10027713516988031622356987 15041570275482047433535481)
      ·
        refine ⟨11281177706611535575151611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15041570275482047433535481 11281177706611535575151611)
        ·
          refine ⟨16921766559917303362727417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281177706611535575151611 16921766559917303362727417)
          ·
            refine ⟨12691324919937977522045563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16921766559917303362727417 12691324919937977522045563)
            ·
              refine ⟨19036987379906966283068345, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12691324919937977522045563 19036987379906966283068345)
              ·
                refine ⟨14277740534930224712301259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19036987379906966283068345 14277740534930224712301259)
                ·
                  refine ⟨21416610802395337068451889, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14277740534930224712301259 21416610802395337068451889)
                  ·
                    refine ⟨16062458101796502801338917, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21416610802395337068451889 16062458101796502801338917)
                    ·
                      refine ⟨3011710894086844275251047, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16062458101796502801338917 3011710894086844275251047)
                      ·
                        rfl

theorem cell23_5865286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_5865286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865286 prefixEnd_5865286 := by exact prefixLift 5865286
  have htrace : WordTrace (prefixWord ++ tailWord_5865286) baseStart_5865286 baseEnd_5865286 := by
    simpa [prefixWord, tailWord_5865286, baseEnd_5865286] using wordTrace_append hprefix tailTrace_5865286
  have hstable : (prefixWord ++ tailWord_5865286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865286).length < 2 ^ (prefixWord ++ tailWord_5865286).sum := by decide
  have hdescent : baseEnd_5865286 < baseStart_5865286 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865293 : List Nat := [1, 6, 1, 2, 1, 2, 3, 1, 1, 2, 3]
def baseStart_5865293 : Nat := 118140960795 + 5865293 * 2 ^ 59
def prefixEnd_5865293 : Nat := 4983230072969 + 3 ^ 40 * 5865293 * 2
def baseEnd_5865293 : Nat := 3011714488451425747863515

theorem tailTrace_5865293 : CollatzResearch.WordTrace tailWord_5865293 prefixEnd_5865293 3011714488451425747863515 := by
  unfold tailWord_5865293
  simp only [CollatzResearch.WordTrace]
  refine ⟨213924810340052648139120533, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142616540226701765426080355 213924810340052648139120533)
  ·
    refine ⟨10027725484689967881521275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 213924810340052648139120533 10027725484689967881521275)
    ·
      refine ⟨15041588227034951822281913, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10027725484689967881521275 15041588227034951822281913)
      ·
        refine ⟨11281191170276213866711435, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 15041588227034951822281913 11281191170276213866711435)
        ·
          refine ⟨16921786755414320800067153, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11281191170276213866711435 16921786755414320800067153)
          ·
            refine ⟨12691340066560740600050365, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16921786755414320800067153 12691340066560740600050365)
            ·
              refine ⟨4759252524960277725018887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12691340066560740600050365 4759252524960277725018887)
              ·
                refine ⟨7138878787440416587528331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759252524960277725018887 7138878787440416587528331)
                ·
                  refine ⟨10708318181160624881292497, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7138878787440416587528331 10708318181160624881292497)
                  ·
                    refine ⟨8031238635870468660969373, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10708318181160624881292497 8031238635870468660969373)
                    ·
                      refine ⟨3011714488451425747863515, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8031238635870468660969373 3011714488451425747863515)
                      ·
                        rfl

theorem cell23_5865293_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 2, 1, 2, 3, 1, 1, 2, 3].length) (baseStart_5865293 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865293 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865293 prefixEnd_5865293 := by exact prefixLift 5865293
  have htrace : WordTrace (prefixWord ++ tailWord_5865293) baseStart_5865293 baseEnd_5865293 := by
    simpa [prefixWord, tailWord_5865293, baseEnd_5865293] using wordTrace_append hprefix tailTrace_5865293
  have hstable : (prefixWord ++ tailWord_5865293).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865293).length < 2 ^ (prefixWord ++ tailWord_5865293).sum := by decide
  have hdescent : baseEnd_5865293 < baseStart_5865293 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865293) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865305 : List Nat := [1, 2, 1, 2, 2, 3, 2, 2, 2, 6]
def baseStart_5865305 : Nat := 118140960795 + 5865305 * 2 ^ 59
def prefixEnd_5865305 : Nat := 4983230072969 + 3 ^ 40 * 5865305 * 2
def baseEnd_5865305 : Nat := 1003906883406426566971153

theorem tailTrace_5865305 : CollatzResearch.WordTrace tailWord_5865305 prefixEnd_5865305 1003906883406426566971153 := by
  unfold tailWord_5865305
  simp only [CollatzResearch.WordTrace]
  refine ⟨213925248016009174188557369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142616832010672782792371579 213925248016009174188557369)
  ·
    refine ⟨160443936012006880641418027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213925248016009174188557369 160443936012006880641418027)
    ·
      refine ⟨240665904018010320962127041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160443936012006880641418027 240665904018010320962127041)
      ·
        refine ⟨180499428013507740721595281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240665904018010320962127041 180499428013507740721595281)
        ·
          refine ⟨135374571010130805541196461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180499428013507740721595281 135374571010130805541196461)
          ·
            refine ⟨50765464128799052077948673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135374571010130805541196461 50765464128799052077948673)
            ·
              refine ⟨38074098096599289058461505, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50765464128799052077948673 38074098096599289058461505)
              ·
                refine ⟨28555573572449466793846129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38074098096599289058461505 28555573572449466793846129)
                ·
                  refine ⟨21416680179337100095384597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28555573572449466793846129 21416680179337100095384597)
                  ·
                    refine ⟨1003906883406426566971153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21416680179337100095384597 1003906883406426566971153)
                    ·
                      rfl

theorem cell23_5865305_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 3, 2, 2, 2, 6].length) (baseStart_5865305 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865305 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865305 prefixEnd_5865305 := by exact prefixLift 5865305
  have htrace : WordTrace (prefixWord ++ tailWord_5865305) baseStart_5865305 baseEnd_5865305 := by
    simpa [prefixWord, tailWord_5865305, baseEnd_5865305] using wordTrace_append hprefix tailTrace_5865305
  have hstable : (prefixWord ++ tailWord_5865305).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865305).length < 2 ^ (prefixWord ++ tailWord_5865305).sum := by decide
  have hdescent : baseEnd_5865305 < baseStart_5865305 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865305) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865329 : List Nat := [1, 2, 2, 2, 1, 3, 4, 1, 1, 4, 2]
def baseStart_5865329 : Nat := 118140960795 + 5865329 * 2 ^ 59
def prefixEnd_5865329 : Nat := 4983230072969 + 3 ^ 40 * 5865329 * 2
def baseEnd_5865329 : Nat := 3011732973754987607013349

theorem tailTrace_5865329 : CollatzResearch.WordTrace tailWord_5865329 prefixEnd_5865329 3011732973754987607013349 := by
  unfold tailWord_5865329
  simp only [CollatzResearch.WordTrace]
  refine ⟨213926123367922226287431041, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142617415578614817524954027 213926123367922226287431041)
  ·
    refine ⟨160444592525941669715573281, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213926123367922226287431041 160444592525941669715573281)
    ·
      refine ⟨120333444394456252286679961, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160444592525941669715573281 120333444394456252286679961)
      ·
        refine ⟨90250083295842189215009971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120333444394456252286679961 90250083295842189215009971)
        ·
          refine ⟨135375124943763283822514957, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90250083295842189215009971 135375124943763283822514957)
          ·
            refine ⟨50765671853911231433443109, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135375124943763283822514957 50765671853911231433443109)
            ·
              refine ⟨9518563472608355893770583, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50765671853911231433443109 9518563472608355893770583)
              ·
                refine ⟨14277845208912533840655875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518563472608355893770583 14277845208912533840655875)
                ·
                  refine ⟨21416767813368800760983813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14277845208912533840655875 21416767813368800760983813)
                  ·
                    refine ⟨4015643965006650142684465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21416767813368800760983813 4015643965006650142684465)
                    ·
                      refine ⟨3011732973754987607013349, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015643965006650142684465 3011732973754987607013349)
                      ·
                        rfl

theorem cell23_5865329_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 3, 4, 1, 1, 4, 2].length) (baseStart_5865329 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865329 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865329 prefixEnd_5865329 := by exact prefixLift 5865329
  have htrace : WordTrace (prefixWord ++ tailWord_5865329) baseStart_5865329 baseEnd_5865329 := by
    simpa [prefixWord, tailWord_5865329, baseEnd_5865329] using wordTrace_append hprefix tailTrace_5865329
  have hstable : (prefixWord ++ tailWord_5865329).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865329).length < 2 ^ (prefixWord ++ tailWord_5865329).sum := by decide
  have hdescent : baseEnd_5865329 < baseStart_5865329 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865329) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865395 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 2, 8]
def baseStart_5865395 : Nat := 118140960795 + 5865395 * 2 ^ 59
def prefixEnd_5865395 : Nat := 4983230072969 + 3 ^ 40 * 5865395 * 2
def baseEnd_5865395 : Nat := 1003922287826061449596015

theorem tailTrace_5865395 : CollatzResearch.WordTrace tailWord_5865395 prefixEnd_5865395 1003922287826061449596015 := by
  unfold tailWord_5865395
  simp only [CollatzResearch.WordTrace]
  refine ⟨213928530585683119559333639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142619020390455413039555759 213928530585683119559333639)
  ·
    refine ⟨320892795878524679339000459, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213928530585683119559333639 320892795878524679339000459)
    ·
      refine ⟨481339193817787019008500689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320892795878524679339000459 481339193817787019008500689)
      ·
        refine ⟨361004395363340264256375517, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481339193817787019008500689 361004395363340264256375517)
        ·
          refine ⟨135376648261252599096140819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361004395363340264256375517 135376648261252599096140819)
          ·
            refine ⟨203064972391878898644211229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135376648261252599096140819 203064972391878898644211229)
            ·
              refine ⟨76149364646954586991579211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 203064972391878898644211229 76149364646954586991579211)
              ·
                refine ⟨114224046970431880487368817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76149364646954586991579211 114224046970431880487368817)
                ·
                  refine ⟨85668035227823910365526613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114224046970431880487368817 85668035227823910365526613)
                  ·
                    refine ⟨1003922287826061449596015, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 85668035227823910365526613 1003922287826061449596015)
                    ·
                      rfl

theorem cell23_5865395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 2, 8].length) (baseStart_5865395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865395 prefixEnd_5865395 := by exact prefixLift 5865395
  have htrace : WordTrace (prefixWord ++ tailWord_5865395) baseStart_5865395 baseEnd_5865395 := by
    simpa [prefixWord, tailWord_5865395, baseEnd_5865395] using wordTrace_append hprefix tailTrace_5865395
  have hstable : (prefixWord ++ tailWord_5865395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865395).length < 2 ^ (prefixWord ++ tailWord_5865395).sum := by decide
  have hdescent : baseEnd_5865395 < baseStart_5865395 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865452 : List Nat := [2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 3]
def baseStart_5865452 : Nat := 118140960795 + 5865452 * 2 ^ 59
def prefixEnd_5865452 : Nat := 4983230072969 + 3 ^ 40 * 5865452 * 2
def baseEnd_5865452 : Nat := 3011796131875490625775283

theorem tailTrace_5865452 : CollatzResearch.WordTrace tailWord_5865452 prefixEnd_5865452 3011796131875490625775283 := by
  unfold tailWord_5865452
  simp only [CollatzResearch.WordTrace]
  refine ⟨106965304773238309147079305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142620406364317745529439073 106965304773238309147079305)
  ·
    refine ⟨80223978579928731860309479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106965304773238309147079305 80223978579928731860309479)
    ·
      refine ⟨120335967869893097790464219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80223978579928731860309479 120335967869893097790464219)
      ·
        refine ⟨180503951804839646685696329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120335967869893097790464219 180503951804839646685696329)
        ·
          refine ⟨135377963853629735014272247, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180503951804839646685696329 135377963853629735014272247)
          ·
            refine ⟨203066945780444602521408371, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135377963853629735014272247 203066945780444602521408371)
            ·
              refine ⟨304600418670666903782112557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203066945780444602521408371 304600418670666903782112557)
              ·
                refine ⟨114225157001500088918292209, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 304600418670666903782112557 114225157001500088918292209)
                ·
                  refine ⟨85668867751125066688719157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 114225157001500088918292209 85668867751125066688719157)
                  ·
                    refine ⟨8031456351667975002067421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85668867751125066688719157 8031456351667975002067421)
                    ·
                      refine ⟨3011796131875490625775283, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8031456351667975002067421 3011796131875490625775283)
                      ·
                        rfl

theorem cell23_5865452_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 5, 3].length) (baseStart_5865452 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865452 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865452 prefixEnd_5865452 := by exact prefixLift 5865452
  have htrace : WordTrace (prefixWord ++ tailWord_5865452) baseStart_5865452 baseEnd_5865452 := by
    simpa [prefixWord, tailWord_5865452, baseEnd_5865452] using wordTrace_append hprefix tailTrace_5865452
  have hstable : (prefixWord ++ tailWord_5865452).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865452).length < 2 ^ (prefixWord ++ tailWord_5865452).sum := by decide
  have hdescent : baseEnd_5865452 < baseStart_5865452 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865452) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865453 : List Nat := [1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 4]
def baseStart_5865453 : Nat := 118140960795 + 5865453 * 2 ^ 59
def prefixEnd_5865453 : Nat := 4983230072969 + 3 ^ 40 * 5865453 * 2
def baseEnd_5865453 : Nat := 3011796645356145121862779

theorem tailTrace_5865453 : CollatzResearch.WordTrace tailWord_5865453 prefixEnd_5865453 3011796645356145121862779 := by
  unfold tailWord_5865453
  simp only [CollatzResearch.WordTrace]
  refine ⟨213930646019472995464945013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142620430679648663643296675 213930646019472995464945013)
  ·
    refine ⟨20055998064325593324838595, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 213930646019472995464945013 20055998064325593324838595)
    ·
      refine ⟨30083997096488389987257893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 20055998064325593324838595 30083997096488389987257893)
      ·
        refine ⟨5640749455591573122610855, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30083997096488389987257893 5640749455591573122610855)
        ·
          refine ⟨8461124183387359683916283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5640749455591573122610855 8461124183387359683916283)
          ·
            refine ⟨12691686275081039525874425, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8461124183387359683916283 12691686275081039525874425)
            ·
              refine ⟨9518764706310779644405819, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12691686275081039525874425 9518764706310779644405819)
              ·
                refine ⟨14278147059466169466608729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518764706310779644405819 14278147059466169466608729)
                ·
                  refine ⟨10708610294599627099956547, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14278147059466169466608729 10708610294599627099956547)
                  ·
                    refine ⟨16062915441899440649934821, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10708610294599627099956547 16062915441899440649934821)
                    ·
                      refine ⟨3011796645356145121862779, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16062915441899440649934821 3011796645356145121862779)
                      ·
                        rfl

theorem cell23_5865453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 4, 1, 1, 2, 1, 2, 1, 4].length) (baseStart_5865453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865453 prefixEnd_5865453 := by exact prefixLift 5865453
  have htrace : WordTrace (prefixWord ++ tailWord_5865453) baseStart_5865453 baseEnd_5865453 := by
    simpa [prefixWord, tailWord_5865453, baseEnd_5865453] using wordTrace_append hprefix tailTrace_5865453
  have hstable : (prefixWord ++ tailWord_5865453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865453).length < 2 ^ (prefixWord ++ tailWord_5865453).sum := by decide
  have hdescent : baseEnd_5865453 < baseStart_5865453 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865486 : List Nat := [4, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3]
def baseStart_5865486 : Nat := 118140960795 + 5865486 * 2 ^ 59
def prefixEnd_5865486 : Nat := 4983230072969 + 3 ^ 40 * 5865486 * 2
def baseEnd_5865486 : Nat := 3011813590217743492750127

theorem tailTrace_5865486 : CollatzResearch.WordTrace tailWord_5865486 prefixEnd_5865486 3011813590217743492750127 := by
  unfold tailWord_5865486
  simp only [CollatzResearch.WordTrace]
  refine ⟨26741481203544180262612039, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142621233085568961400597541 26741481203544180262612039)
  ·
    refine ⟨40112221805316270393918059, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26741481203544180262612039 40112221805316270393918059)
    ·
      refine ⟨60168332707974405590877089, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40112221805316270393918059 60168332707974405590877089)
      ·
        refine ⟨45126249530980804193157817, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60168332707974405590877089 45126249530980804193157817)
        ·
          refine ⟨33844687148235603144868363, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45126249530980804193157817 33844687148235603144868363)
          ·
            refine ⟨50767030722353404717302545, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33844687148235603144868363 50767030722353404717302545)
            ·
              refine ⟨38075273041765053537976909, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50767030722353404717302545 38075273041765053537976909)
              ·
                refine ⟨14278227390661895076741341, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38075273041765053537976909 14278227390661895076741341)
                ·
                  refine ⟨5354335271498210653778003, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14278227390661895076741341 5354335271498210653778003)
                  ·
                    refine ⟨8031502907247315980667005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5354335271498210653778003 8031502907247315980667005)
                    ·
                      refine ⟨3011813590217743492750127, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8031502907247315980667005 3011813590217743492750127)
                      ·
                        rfl

theorem cell23_5865486_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 2, 1, 2, 3, 3, 1, 3].length) (baseStart_5865486 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865486 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865486 prefixEnd_5865486 := by exact prefixLift 5865486
  have htrace : WordTrace (prefixWord ++ tailWord_5865486) baseStart_5865486 baseEnd_5865486 := by
    simpa [prefixWord, tailWord_5865486, baseEnd_5865486] using wordTrace_append hprefix tailTrace_5865486
  have hstable : (prefixWord ++ tailWord_5865486).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865486).length < 2 ^ (prefixWord ++ tailWord_5865486).sum := by decide
  have hdescent : baseEnd_5865486 < baseStart_5865486 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865486) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865509 : List Nat := [1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 4]
def baseStart_5865509 : Nat := 118140960795 + 5865509 * 2 ^ 59
def prefixEnd_5865509 : Nat := 4983230072969 + 3 ^ 40 * 5865509 * 2
def baseEnd_5865509 : Nat := 3011825400272796902762521

theorem tailTrace_5865509 : CollatzResearch.WordTrace tailWord_5865509 prefixEnd_5865509 3011825400272796902762521 := by
  unfold tailWord_5865509
  simp only [CollatzResearch.WordTrace]
  refine ⟨213932688507270117028983581, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142621792338180078019322387 213932688507270117028983581)
  ·
    refine ⟨80224758190226293885868843, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213932688507270117028983581 80224758190226293885868843)
    ·
      refine ⟨120337137285339440828803265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80224758190226293885868843 120337137285339440828803265)
      ·
        refine ⟨90252852964004580621602449, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120337137285339440828803265 90252852964004580621602449)
        ·
          refine ⟨67689639723003435466201837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90252852964004580621602449 67689639723003435466201837)
          ·
            refine ⟨25383614896126288299825689, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67689639723003435466201837 25383614896126288299825689)
            ·
              refine ⟨19037711172094716224869267, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25383614896126288299825689 19037711172094716224869267)
              ·
                refine ⟨28556566758142074337303901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19037711172094716224869267 28556566758142074337303901)
                ·
                  refine ⟨10708712534303277876488963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28556566758142074337303901 10708712534303277876488963)
                  ·
                    refine ⟨16063068801454916814733445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10708712534303277876488963 16063068801454916814733445)
                    ·
                      refine ⟨3011825400272796902762521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16063068801454916814733445 3011825400272796902762521)
                      ·
                        rfl

theorem cell23_5865509_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 3, 2, 1, 3, 1, 4].length) (baseStart_5865509 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865509 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865509 prefixEnd_5865509 := by exact prefixLift 5865509
  have htrace : WordTrace (prefixWord ++ tailWord_5865509) baseStart_5865509 baseEnd_5865509 := by
    simpa [prefixWord, tailWord_5865509, baseEnd_5865509] using wordTrace_append hprefix tailTrace_5865509
  have hstable : (prefixWord ++ tailWord_5865509).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865509).length < 2 ^ (prefixWord ++ tailWord_5865509).sum := by decide
  have hdescent : baseEnd_5865509 < baseStart_5865509 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865509) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865532 : List Nat := [2, 2, 2, 2, 2, 1, 12]
def baseStart_5865532 : Nat := 118140960795 + 5865532 * 2 ^ 59
def prefixEnd_5865532 : Nat := 4983230072969 + 3 ^ 40 * 5865532 * 2
def baseEnd_5865532 : Nat := 37183175436146300157715

theorem tailTrace_5865532 : CollatzResearch.WordTrace tailWord_5865532 prefixEnd_5865532 37183175436146300157715 := by
  unfold tailWord_5865532
  simp only [CollatzResearch.WordTrace]
  refine ⟨106966763693093395978535425, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142622351590791194638047233 106966763693093395978535425)
  ·
    refine ⟨80225072769820046983901569, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106966763693093395978535425 80225072769820046983901569)
    ·
      refine ⟨60168804577365035237926177, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80225072769820046983901569 60168804577365035237926177)
      ·
        refine ⟨45126603433023776428444633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60168804577365035237926177 45126603433023776428444633)
        ·
          refine ⟨33844952574767832321333475, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45126603433023776428444633 33844952574767832321333475)
          ·
            refine ⟨50767428862151748482000213, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33844952574767832321333475 50767428862151748482000213)
            ·
              refine ⟨37183175436146300157715, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 12 50767428862151748482000213 37183175436146300157715)
              ·
                rfl

theorem cell23_5865532_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 12].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 2, 1, 12].length) (baseStart_5865532 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865532 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865532 prefixEnd_5865532 := by exact prefixLift 5865532
  have htrace : WordTrace (prefixWord ++ tailWord_5865532) baseStart_5865532 baseEnd_5865532 := by
    simpa [prefixWord, tailWord_5865532, baseEnd_5865532] using wordTrace_append hprefix tailTrace_5865532
  have hstable : (prefixWord ++ tailWord_5865532).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865532).length < 2 ^ (prefixWord ++ tailWord_5865532).sum := by decide
  have hdescent : baseEnd_5865532 < baseStart_5865532 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865532) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865536 : List Nat := [2, 1, 1, 2, 2, 4, 3, 2, 2, 4]
def baseStart_5865536 : Nat := 118140960795 + 5865536 * 2 ^ 59
def prefixEnd_5865536 : Nat := 4983230072969 + 3 ^ 40 * 5865536 * 2
def baseEnd_5865536 : Nat := 1003946421416822765708299

theorem tailTrace_5865536 : CollatzResearch.WordTrace tailWord_5865536 prefixEnd_5865536 1003946421416822765708299 := by
  unfold tailWord_5865536
  simp only [CollatzResearch.WordTrace]
  refine ⟨106966836639086150320108231, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142622448852114867093477641 106966836639086150320108231)
  ·
    refine ⟨160450254958629225480162347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106966836639086150320108231 160450254958629225480162347)
    ·
      refine ⟨240675382437943838220243521, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160450254958629225480162347 240675382437943838220243521)
      ·
        refine ⟨180506536828457878665182641, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240675382437943838220243521 180506536828457878665182641)
        ·
          refine ⟨135379902621343408998886981, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180506536828457878665182641 135379902621343408998886981)
          ·
            refine ⟨25383731741501889187291309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 135379902621343408998886981 25383731741501889187291309)
            ·
              refine ⟨9518899403063208445234241, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25383731741501889187291309 9518899403063208445234241)
              ·
                refine ⟨7139174552297406333925681, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9518899403063208445234241 7139174552297406333925681)
                ·
                  refine ⟨5354380914223054750444261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139174552297406333925681 5354380914223054750444261)
                  ·
                    refine ⟨1003946421416822765708299, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354380914223054750444261 1003946421416822765708299)
                    ·
                      rfl

theorem cell23_5865536_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 4, 3, 2, 2, 4].length) (baseStart_5865536 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865536 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865536 prefixEnd_5865536 := by exact prefixLift 5865536
  have htrace : WordTrace (prefixWord ++ tailWord_5865536) baseStart_5865536 baseEnd_5865536 := by
    simpa [prefixWord, tailWord_5865536, baseEnd_5865536] using wordTrace_append hprefix tailTrace_5865536
  have hstable : (prefixWord ++ tailWord_5865536).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865536).length < 2 ^ (prefixWord ++ tailWord_5865536).sum := by decide
  have hdescent : baseEnd_5865536 < baseStart_5865536 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865536) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865543 : List Nat := [1, 1, 4, 1, 3, 1, 4, 1, 3, 2, 2]
def baseStart_5865543 : Nat := 118140960795 + 5865543 * 2 ^ 59
def prefixEnd_5865543 : Nat := 4983230072969 + 3 ^ 40 * 5865543 * 2
def baseEnd_5865543 : Nat := 3011842858615049769737365

theorem tailTrace_5865543 : CollatzResearch.WordTrace tailWord_5865543 prefixEnd_5865543 3011842858615049769737365 := by
  unfold tailWord_5865543
  simp only [CollatzResearch.WordTrace]
  refine ⟨213933928589146940835721283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142622619059431293890480855 213933928589146940835721283)
  ·
    refine ⟨320900892883720411253581925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213933928589146940835721283 320900892883720411253581925)
    ·
      refine ⟨60168917415697577110046611, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320900892883720411253581925 60168917415697577110046611)
      ·
        refine ⟨90253376123546365665069917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60168917415697577110046611 90253376123546365665069917)
        ·
          refine ⟨33845016046329887124401219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90253376123546365665069917 33845016046329887124401219)
          ·
            refine ⟨50767524069494830686601829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33845016046329887124401219 50767524069494830686601829)
            ·
              refine ⟨9518910763030280753737843, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50767524069494830686601829 9518910763030280753737843)
              ·
                refine ⟨14278366144545421130606765, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9518910763030280753737843 14278366144545421130606765)
                ·
                  refine ⟨5354387304204532923977537, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14278366144545421130606765 5354387304204532923977537)
                  ·
                    refine ⟨4015790478153399692983153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354387304204532923977537 4015790478153399692983153)
                    ·
                      refine ⟨3011842858615049769737365, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015790478153399692983153 3011842858615049769737365)
                      ·
                        rfl

theorem cell23_5865543_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 3, 1, 4, 1, 3, 2, 2].length) (baseStart_5865543 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865543 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865543 prefixEnd_5865543 := by exact prefixLift 5865543
  have htrace : WordTrace (prefixWord ++ tailWord_5865543) baseStart_5865543 baseEnd_5865543 := by
    simpa [prefixWord, tailWord_5865543, baseEnd_5865543] using wordTrace_append hprefix tailTrace_5865543
  have hstable : (prefixWord ++ tailWord_5865543).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865543).length < 2 ^ (prefixWord ++ tailWord_5865543).sum := by decide
  have hdescent : baseEnd_5865543 < baseStart_5865543 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865543) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865549 : List Nat := [1, 6, 1, 1, 1, 1, 2, 10]
def baseStart_5865549 : Nat := 118140960795 + 5865549 * 2 ^ 59
def prefixEnd_5865549 : Nat := 4983230072969 + 3 ^ 40 * 5865549 * 2
def baseEnd_5865549 : Nat := 111549849611073212824531

theorem tailTrace_5865549 : CollatzResearch.WordTrace tailWord_5865549 prefixEnd_5865549 111549849611073212824531 := by
  unfold tailWord_5865549
  simp only [CollatzResearch.WordTrace]
  refine ⟨213934147427125203860439701, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142622764951416802573626467 213934147427125203860439701)
  ·
    refine ⟨10028163160646493930958111, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 213934147427125203860439701 10028163160646493930958111)
    ·
      refine ⟨15042244740969740896437167, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10028163160646493930958111 15042244740969740896437167)
      ·
        refine ⟨22563367111454611344655751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15042244740969740896437167 22563367111454611344655751)
        ·
          refine ⟨33845050667181917016983627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22563367111454611344655751 33845050667181917016983627)
          ·
            refine ⟨50767576000772875525475441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33845050667181917016983627 50767576000772875525475441)
            ·
              refine ⟨38075682000579656644106581, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50767576000772875525475441 38075682000579656644106581)
              ·
                refine ⟨111549849611073212824531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 38075682000579656644106581 111549849611073212824531)
                ·
                  rfl

theorem cell23_5865549_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 1, 1, 1, 2, 10].length) (baseStart_5865549 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865549 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865549 prefixEnd_5865549 := by exact prefixLift 5865549
  have htrace : WordTrace (prefixWord ++ tailWord_5865549) baseStart_5865549 baseEnd_5865549 := by
    simpa [prefixWord, tailWord_5865549, baseEnd_5865549] using wordTrace_append hprefix tailTrace_5865549
  have hstable : (prefixWord ++ tailWord_5865549).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865549).length < 2 ^ (prefixWord ++ tailWord_5865549).sum := by decide
  have hdescent : baseEnd_5865549 < baseStart_5865549 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865549) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865610 : List Nat := [3, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3]
def baseStart_5865610 : Nat := 118140960795 + 5865610 * 2 ^ 59
def prefixEnd_5865610 : Nat := 4983230072969 + 3 ^ 40 * 5865610 * 2
def baseEnd_5865610 : Nat := 3011877261818901007599557

theorem tailTrace_5865610 : CollatzResearch.WordTrace tailWord_5865610 prefixEnd_5865610 3011877261818901007599557 := by
  unfold tailWord_5865610
  simp only [CollatzResearch.WordTrace]
  refine ⟨53484093069976052819602571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142624248186602807518940189 53484093069976052819602571)
  ·
    refine ⟨80226139604964079229403857, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53484093069976052819602571 80226139604964079229403857)
    ·
      refine ⟨60169604703723059422052893, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80226139604964079229403857 60169604703723059422052893)
      ·
        refine ⟨22563601763896147283269835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60169604703723059422052893 22563601763896147283269835)
        ·
          refine ⟨33845402645844220924904753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22563601763896147283269835 33845402645844220924904753)
          ·
            refine ⟨25384051984383165693678565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33845402645844220924904753 25384051984383165693678565)
            ·
              refine ⟨4759509747071843567564731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25384051984383165693678565 4759509747071843567564731)
              ·
                refine ⟨7139264620607765351347097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759509747071843567564731 7139264620607765351347097)
                ·
                  refine ⟨5354448465455824013510323, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139264620607765351347097 5354448465455824013510323)
                  ·
                    refine ⟨8031672698183736020265485, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5354448465455824013510323 8031672698183736020265485)
                    ·
                      refine ⟨3011877261818901007599557, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8031672698183736020265485 3011877261818901007599557)
                      ·
                        rfl

theorem cell23_5865610_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 3, 1, 2, 4, 1, 2, 1, 3].length) (baseStart_5865610 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865610 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865610 prefixEnd_5865610 := by exact prefixLift 5865610
  have htrace : WordTrace (prefixWord ++ tailWord_5865610) baseStart_5865610 baseEnd_5865610 := by
    simpa [prefixWord, tailWord_5865610, baseEnd_5865610] using wordTrace_append hprefix tailTrace_5865610
  have hstable : (prefixWord ++ tailWord_5865610).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865610).length < 2 ^ (prefixWord ++ tailWord_5865610).sum := by decide
  have hdescent : baseEnd_5865610 < baseStart_5865610 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865610) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865616 : List Nat := [2, 1, 1, 1, 1, 1, 6, 3, 1, 4, 2]
def baseStart_5865616 : Nat := 118140960795 + 5865616 * 2 ^ 59
def prefixEnd_5865616 : Nat := 4983230072969 + 3 ^ 40 * 5865616 * 2
def baseEnd_5865616 : Nat := 3011880342702827984124529

theorem tailTrace_5865616 : CollatzResearch.WordTrace tailWord_5865616 prefixEnd_5865616 3011880342702827984124529 := by
  unfold tailWord_5865616
  simp only [CollatzResearch.WordTrace]
  refine ⟨106968295558941237151564351, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142624394078588316202085801 106968295558941237151564351)
  ·
    refine ⟨160452443338411855727346527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106968295558941237151564351 160452443338411855727346527)
    ·
      refine ⟨240678665007617783591019791, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160452443338411855727346527 240678665007617783591019791)
      ·
        refine ⟨361017997511426675386529687, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240678665007617783591019791 361017997511426675386529687)
        ·
          refine ⟨541526996267140013079794531, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361017997511426675386529687 541526996267140013079794531)
          ·
            refine ⟨812290494400710019619691797, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541526996267140013079794531 812290494400710019619691797)
            ·
              refine ⟨38076116925033282169673053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 812290494400710019619691797 38076116925033282169673053)
              ·
                refine ⟨14278543846887480813627395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38076116925033282169673053 14278543846887480813627395)
                ·
                  refine ⟨21417815770331221220441093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14278543846887480813627395 21417815770331221220441093)
                  ·
                    refine ⟨4015840456937103978832705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21417815770331221220441093 4015840456937103978832705)
                    ·
                      refine ⟨3011880342702827984124529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015840456937103978832705 3011880342702827984124529)
                      ·
                        rfl

theorem cell23_5865616_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 6, 3, 1, 4, 2].length) (baseStart_5865616 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865616 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865616 prefixEnd_5865616 := by exact prefixLift 5865616
  have htrace : WordTrace (prefixWord ++ tailWord_5865616) baseStart_5865616 baseEnd_5865616 := by
    simpa [prefixWord, tailWord_5865616, baseEnd_5865616] using wordTrace_append hprefix tailTrace_5865616
  have hstable : (prefixWord ++ tailWord_5865616).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865616).length < 2 ^ (prefixWord ++ tailWord_5865616).sum := by decide
  have hdescent : baseEnd_5865616 < baseStart_5865616 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865616) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865633 : List Nat := [1, 2, 3, 3, 1, 3, 1, 2, 1, 4, 2]
def baseStart_5865633 : Nat := 118140960795 + 5865633 * 2 ^ 59
def prefixEnd_5865633 : Nat := 4983230072969 + 3 ^ 40 * 5865633 * 2
def baseEnd_5865633 : Nat := 3011889071873954417611951

theorem tailTrace_5865633 : CollatzResearch.WordTrace tailWord_5865633 prefixEnd_5865633 3011889071873954417611951 := by
  unfold tailWord_5865633
  simp only [CollatzResearch.WordTrace]
  refine ⟨213937211158820886206497553, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142624807439213924137665035 213937211158820886206497553)
  ·
    refine ⟨160452908369115664654873165, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213937211158820886206497553 160452908369115664654873165)
    ·
      refine ⟨60169840638418374245577437, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160452908369115664654873165 60169840638418374245577437)
      ·
        refine ⟨22563690239406890342091539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60169840638418374245577437 22563690239406890342091539)
        ·
          refine ⟨33845535359110335513137309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22563690239406890342091539 33845535359110335513137309)
          ·
            refine ⟨12692075759666375817426491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 33845535359110335513137309 12692075759666375817426491)
            ·
              refine ⟨19038113639499563726139737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12692075759666375817426491 19038113639499563726139737)
              ·
                refine ⟨14278585229624672794604803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19038113639499563726139737 14278585229624672794604803)
                ·
                  refine ⟨21417877844437009191907205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14278585229624672794604803 21417877844437009191907205)
                  ·
                    refine ⟨4015852095831939223482601, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21417877844437009191907205 4015852095831939223482601)
                    ·
                      refine ⟨3011889071873954417611951, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015852095831939223482601 3011889071873954417611951)
                      ·
                        rfl

theorem cell23_5865633_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 3, 1, 3, 1, 2, 1, 4, 2].length) (baseStart_5865633 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865633 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865633 prefixEnd_5865633 := by exact prefixLift 5865633
  have htrace : WordTrace (prefixWord ++ tailWord_5865633) baseStart_5865633 baseEnd_5865633 := by
    simpa [prefixWord, tailWord_5865633, baseEnd_5865633] using wordTrace_append hprefix tailTrace_5865633
  have hstable : (prefixWord ++ tailWord_5865633).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865633).length < 2 ^ (prefixWord ++ tailWord_5865633).sum := by decide
  have hdescent : baseEnd_5865633 < baseStart_5865633 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865633) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865650 : List Nat := [3, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2]
def baseStart_5865650 : Nat := 118140960795 + 5865650 * 2 ^ 59
def prefixEnd_5865650 : Nat := 4983230072969 + 3 ^ 40 * 5865650 * 2
def baseEnd_5865650 : Nat := 3011897801045080851099373

theorem tailTrace_5865650 : CollatzResearch.WordTrace tailWord_5865650 prefixEnd_5865650 3011897801045080851099373 := by
  unfold tailWord_5865650
  simp only [CollatzResearch.WordTrace]
  refine ⟨53484457799939824527466601, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142625220799839532073244269 53484457799939824527466601)
  ·
    refine ⟨40113343349954868395599951, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53484457799939824527466601 40113343349954868395599951)
    ·
      refine ⟨60170015024932302593399927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40113343349954868395599951 60170015024932302593399927)
      ·
        refine ⟨90255022537398453890099891, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60170015024932302593399927 90255022537398453890099891)
        ·
          refine ⟨135382533806097680835149837, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90255022537398453890099891 135382533806097680835149837)
          ·
            refine ⟨50768450177286630313181189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135382533806097680835149837 50768450177286630313181189)
            ·
              refine ⟨9519084408241243183721473, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50768450177286630313181189 9519084408241243183721473)
              ·
                refine ⟨7139313306180932387791105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9519084408241243183721473 7139313306180932387791105)
                ·
                  refine ⟨5354484979635699290843329, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139313306180932387791105 5354484979635699290843329)
                  ·
                    refine ⟨4015863734726774468132497, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354484979635699290843329 4015863734726774468132497)
                    ·
                      refine ⟨3011897801045080851099373, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4015863734726774468132497 3011897801045080851099373)
                      ·
                        rfl

theorem cell23_5865650_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 4, 2, 2, 2, 2].length) (baseStart_5865650 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865650 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865650 prefixEnd_5865650 := by exact prefixLift 5865650
  have htrace : WordTrace (prefixWord ++ tailWord_5865650) baseStart_5865650 baseEnd_5865650 := by
    simpa [prefixWord, tailWord_5865650, baseEnd_5865650] using wordTrace_append hprefix tailTrace_5865650
  have hstable : (prefixWord ++ tailWord_5865650).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865650).length < 2 ^ (prefixWord ++ tailWord_5865650).sum := by decide
  have hdescent : baseEnd_5865650 < baseStart_5865650 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865650) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865656 : List Nat := [2, 1, 2, 1, 2, 1, 5, 4, 5]
def baseStart_5865656 : Nat := 118140960795 + 5865656 * 2 ^ 59
def prefixEnd_5865656 : Nat := 4983230072969 + 3 ^ 40 * 5865656 * 2
def baseEnd_5865656 : Nat := 334655653547667536402705

theorem tailTrace_5865656 : CollatzResearch.WordTrace tailWord_5865656 prefixEnd_5865656 334655653547667536402705 := by
  unfold tailWord_5865656
  simp only [CollatzResearch.WordTrace]
  refine ⟨106969025018868780567292411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142625366691825040756389881 106969025018868780567292411)
  ·
    refine ⟨160453537528303170850938617, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106969025018868780567292411 160453537528303170850938617)
    ·
      refine ⟨120340153146227378138203963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160453537528303170850938617 120340153146227378138203963)
      ·
        refine ⟨180510229719341067207305945, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120340153146227378138203963 180510229719341067207305945)
        ·
          refine ⟨135382672289505800405479459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 180510229719341067207305945 135382672289505800405479459)
          ·
            refine ⟨203074008434258700608219189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135382672289505800405479459 203074008434258700608219189)
            ·
              refine ⟨19038188290711753182020549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203074008434258700608219189 19038188290711753182020549)
              ·
                refine ⟨3569660304508453721628853, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 19038188290711753182020549 3569660304508453721628853)
                ·
                  refine ⟨334655653547667536402705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 3569660304508453721628853 334655653547667536402705)
                  ·
                    rfl

theorem cell23_5865656_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 4, 5].length) (baseStart_5865656 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865656 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865656 prefixEnd_5865656 := by exact prefixLift 5865656
  have htrace : WordTrace (prefixWord ++ tailWord_5865656) baseStart_5865656 baseEnd_5865656 := by
    simpa [prefixWord, tailWord_5865656, baseEnd_5865656] using wordTrace_append hprefix tailTrace_5865656
  have hstable : (prefixWord ++ tailWord_5865656).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865656).length < 2 ^ (prefixWord ++ tailWord_5865656).sum := by decide
  have hdescent : baseEnd_5865656 < baseStart_5865656 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865656) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865669 : List Nat := [1, 3, 1, 1, 1, 1, 4, 2, 4, 5]
def baseStart_5865669 : Nat := 118140960795 + 5865669 * 2 ^ 59
def prefixEnd_5865669 : Nat := 4983230072969 + 3 ^ 40 * 5865669 * 2
def baseEnd_5865669 : Nat := 1003969185725838758920595

theorem tailTrace_5865669 : CollatzResearch.WordTrace tailWord_5865669 prefixEnd_5865669 1003969185725838758920595 := by
  unfold tailWord_5865669
  simp only [CollatzResearch.WordTrace]
  refine ⟨213938524186690464354808061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142625682791126976236538707 213938524186690464354808061)
  ·
    refine ⟨80226946570008924133053023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213938524186690464354808061 80226946570008924133053023)
    ·
      refine ⟨120340419855013386199579535, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80226946570008924133053023 120340419855013386199579535)
      ·
        refine ⟨180510629782520079299369303, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120340419855013386199579535 180510629782520079299369303)
        ·
          refine ⟨270765944673780118949053955, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180510629782520079299369303 270765944673780118949053955)
          ·
            refine ⟨406148917010670178423580933, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270765944673780118949053955 406148917010670178423580933)
            ·
              refine ⟨76152921939500658454421425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406148917010670178423580933 76152921939500658454421425)
              ·
                refine ⟨57114691454625493840816069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76152921939500658454421425 57114691454625493840816069)
                ·
                  refine ⟨10709004647742280095153013, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57114691454625493840816069 10709004647742280095153013)
                  ·
                    refine ⟨1003969185725838758920595, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10709004647742280095153013 1003969185725838758920595)
                    ·
                      rfl

theorem cell23_5865669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 4, 2, 4, 5].length) (baseStart_5865669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865669 prefixEnd_5865669 := by exact prefixLift 5865669
  have htrace : WordTrace (prefixWord ++ tailWord_5865669) baseStart_5865669 baseEnd_5865669 := by
    simpa [prefixWord, tailWord_5865669, baseEnd_5865669] using wordTrace_append hprefix tailTrace_5865669
  have hstable : (prefixWord ++ tailWord_5865669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865669).length < 2 ^ (prefixWord ++ tailWord_5865669).sum := by decide
  have hdescent : baseEnd_5865669 < baseStart_5865669 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865706 : List Nat := [3, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4]
def baseStart_5865706 : Nat := 118140960795 + 5865706 * 2 ^ 59
def prefixEnd_5865706 : Nat := 4983230072969 + 3 ^ 40 * 5865706 * 2
def baseEnd_5865706 : Nat := 3011926555961732631999115

theorem tailTrace_5865706 : CollatzResearch.WordTrace tailWord_5865706 prefixEnd_5865706 3011926555961732631999115 := by
  unfold tailWord_5865706
  simp only [CollatzResearch.WordTrace]
  refine ⟨53484968421889104918476243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142626582458370946449269981 53484968421889104918476243)
  ·
    refine ⟨80227452632833657377714365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53484968421889104918476243 80227452632833657377714365)
    ·
      refine ⟨30085294737312621516642887, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80227452632833657377714365 30085294737312621516642887)
      ·
        refine ⟨45127942105968932274964331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30085294737312621516642887 45127942105968932274964331)
        ·
          refine ⟨67691913158953398412446497, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45127942105968932274964331 67691913158953398412446497)
          ·
            refine ⟨50768934869215048809334873, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67691913158953398412446497 50768934869215048809334873)
            ·
              refine ⟨38076701151911286607001155, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50768934869215048809334873 38076701151911286607001155)
              ·
                refine ⟨57115051727866929910501733, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38076701151911286607001155 57115051727866929910501733)
                ·
                  refine ⟨10709072198975049358219075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57115051727866929910501733 10709072198975049358219075)
                  ·
                    refine ⟨16063608298462574037328613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10709072198975049358219075 16063608298462574037328613)
                    ·
                      refine ⟨3011926555961732631999115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16063608298462574037328613 3011926555961732631999115)
                      ·
                        rfl

theorem cell23_5865706_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 1, 1, 2, 2, 1, 4, 1, 4].length) (baseStart_5865706 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865706 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865706 prefixEnd_5865706 := by exact prefixLift 5865706
  have htrace : WordTrace (prefixWord ++ tailWord_5865706) baseStart_5865706 baseEnd_5865706 := by
    simpa [prefixWord, tailWord_5865706, baseEnd_5865706] using wordTrace_append hprefix tailTrace_5865706
  have hstable : (prefixWord ++ tailWord_5865706).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865706).length < 2 ^ (prefixWord ++ tailWord_5865706).sum := by decide
  have hdescent : baseEnd_5865706 < baseStart_5865706 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865706) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865719 : List Nat := [1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 4]
def baseStart_5865719 : Nat := 118140960795 + 5865719 * 2 ^ 59
def prefixEnd_5865719 : Nat := 4983230072969 + 3 ^ 40 * 5865719 * 2
def baseEnd_5865719 : Nat := 3011933231210241081136555

theorem tailTrace_5865719 : CollatzResearch.WordTrace tailWord_5865719 prefixEnd_5865719 3011933231210241081136555 := by
  unfold tailWord_5865719
  simp only [CollatzResearch.WordTrace]
  refine ⟨213940347836509322894128211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142626898557672881929418807 213940347836509322894128211)
  ·
    refine ⟨320910521754763984341192317, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213940347836509322894128211 320910521754763984341192317)
    ·
      refine ⟨120341445658036494127947119, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320910521754763984341192317 120341445658036494127947119)
      ·
        refine ⟨180512168487054741191920679, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120341445658036494127947119 180512168487054741191920679)
        ·
          refine ⟨270768252730582111787881019, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180512168487054741191920679 270768252730582111787881019)
          ·
            refine ⟨406152379095873167681821529, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270768252730582111787881019 406152379095873167681821529)
            ·
              refine ⟨304614284321904875761366147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 406152379095873167681821529 304614284321904875761366147)
              ·
                refine ⟨456921426482857313642049221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304614284321904875761366147 456921426482857313642049221)
                ·
                  refine ⟨85672767465535746307884229, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 456921426482857313642049221 85672767465535746307884229)
                  ·
                    refine ⟨16063643899787952432728293, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 85672767465535746307884229 16063643899787952432728293)
                    ·
                      refine ⟨3011933231210241081136555, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16063643899787952432728293 3011933231210241081136555)
                      ·
                        rfl

theorem cell23_5865719_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 2, 1, 4, 4, 4].length) (baseStart_5865719 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865719 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865719 prefixEnd_5865719 := by exact prefixLift 5865719
  have htrace : WordTrace (prefixWord ++ tailWord_5865719) baseStart_5865719 baseEnd_5865719 := by
    simpa [prefixWord, tailWord_5865719, baseEnd_5865719] using wordTrace_append hprefix tailTrace_5865719
  have hstable : (prefixWord ++ tailWord_5865719).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865719).length < 2 ^ (prefixWord ++ tailWord_5865719).sum := by decide
  have hdescent : baseEnd_5865719 < baseStart_5865719 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865719) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865780 : List Nat := [2, 5, 1, 1, 1, 2, 4, 1, 6]
def baseStart_5865780 : Nat := 118140960795 + 5865780 * 2 ^ 59
def prefixEnd_5865780 : Nat := 4983230072969 + 3 ^ 40 * 5865780 * 2
def baseEnd_5865780 : Nat := 334662728170018371385975

theorem tailTrace_5865780 : CollatzResearch.WordTrace tailWord_5865780 prefixEnd_5865780 334662728170018371385975 := by
  unfold tailWord_5865780
  simp only [CollatzResearch.WordTrace]
  refine ⟨106971286344644165156049397, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142628381792858886874732529 106971286344644165156049397)
  ·
    refine ⟨10028558094810390483379631, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106971286344644165156049397 10028558094810390483379631)
    ·
      refine ⟨15042837142215585725069447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10028558094810390483379631 15042837142215585725069447)
      ·
        refine ⟨22564255713323378587604171, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15042837142215585725069447 22564255713323378587604171)
        ·
          refine ⟨33846383569985067881406257, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22564255713323378587604171 33846383569985067881406257)
          ·
            refine ⟨25384787677488800911054693, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33846383569985067881406257 25384787677488800911054693)
            ·
              refine ⟨4759647689529150170822755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 25384787677488800911054693 4759647689529150170822755)
              ·
                refine ⟨7139471534293725256234133, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759647689529150170822755 7139471534293725256234133)
                ·
                  refine ⟨334662728170018371385975, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 7139471534293725256234133 334662728170018371385975)
                  ·
                    rfl

theorem cell23_5865780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 2, 4, 1, 6].length) (baseStart_5865780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865780 prefixEnd_5865780 := by exact prefixLift 5865780
  have htrace : WordTrace (prefixWord ++ tailWord_5865780) baseStart_5865780 baseEnd_5865780 := by
    simpa [prefixWord, tailWord_5865780, baseEnd_5865780] using wordTrace_append hprefix tailTrace_5865780
  have hstable : (prefixWord ++ tailWord_5865780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865780).length < 2 ^ (prefixWord ++ tailWord_5865780).sum := by decide
  have hdescent : baseEnd_5865780 < baseStart_5865780 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865816 : List Nat := [2, 1, 2, 2, 1, 1, 2, 5, 1, 1, 5]
def baseStart_5865816 : Nat := 118140960795 + 5865816 * 2 ^ 59
def prefixEnd_5865816 : Nat := 4983230072969 + 3 ^ 40 * 5865816 * 2
def baseEnd_5865816 : Nat := 3011983038833727201623609

theorem tailTrace_5865816 : CollatzResearch.WordTrace tailWord_5865816 prefixEnd_5865816 3011983038833727201623609 := by
  unfold tailWord_5865816
  simp only [CollatzResearch.WordTrace]
  refine ⟨106971942858578954230204651, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142629257144771938973606201 106971942858578954230204651)
  ·
    refine ⟨160457914287868431345306977, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106971942858578954230204651 160457914287868431345306977)
    ·
      refine ⟨120343435715901323508980233, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160457914287868431345306977 120343435715901323508980233)
      ·
        refine ⟨90257576786925992631735175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120343435715901323508980233 90257576786925992631735175)
        ·
          refine ⟨135386365180388988947602763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90257576786925992631735175 135386365180388988947602763)
          ·
            refine ⟨203079547770583483421404145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135386365180388988947602763 203079547770583483421404145)
            ·
              refine ⟨152309660827937612566053109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203079547770583483421404145 152309660827937612566053109)
              ·
                refine ⟨14279030702619151178067479, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152309660827937612566053109 14279030702619151178067479)
                ·
                  refine ⟨21418546053928726767101219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14279030702619151178067479 21418546053928726767101219)
                  ·
                    refine ⟨32127819080893090150651829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21418546053928726767101219 32127819080893090150651829)
                    ·
                      refine ⟨3011983038833727201623609, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32127819080893090150651829 3011983038833727201623609)
                      ·
                        rfl

theorem cell23_5865816_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 1, 2, 5, 1, 1, 5].length) (baseStart_5865816 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865816 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865816 prefixEnd_5865816 := by exact prefixLift 5865816
  have htrace : WordTrace (prefixWord ++ tailWord_5865816) baseStart_5865816 baseEnd_5865816 := by
    simpa [prefixWord, tailWord_5865816, baseEnd_5865816] using wordTrace_append hprefix tailTrace_5865816
  have hstable : (prefixWord ++ tailWord_5865816).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865816).length < 2 ^ (prefixWord ++ tailWord_5865816).sum := by decide
  have hdescent : baseEnd_5865816 < baseStart_5865816 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865816) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865823 : List Nat := [1, 1, 2, 3, 1, 2, 3, 4, 2, 4]
def baseStart_5865823 : Nat := 118140960795 + 5865823 * 2 ^ 59
def prefixEnd_5865823 : Nat := 4983230072969 + 3 ^ 40 * 5865823 * 2
def baseEnd_5865823 : Nat := 1003995544399436224745359

theorem tailTrace_5865823 : CollatzResearch.WordTrace tailWord_5865823 prefixEnd_5865823 1003995544399436224745359 := by
  unfold tailWord_5865823
  simp only [CollatzResearch.WordTrace]
  refine ⟨213944141028132548655914123, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142629427352088365770609415 213944141028132548655914123)
  ·
    refine ⟨320916211542198822983871185, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213944141028132548655914123 320916211542198822983871185)
    ·
      refine ⟨240687158656649117237903389, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320916211542198822983871185 240687158656649117237903389)
      ·
        refine ⟨90257684496243418964213771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240687158656649117237903389 90257684496243418964213771)
        ·
          refine ⟨135386526744365128446320657, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90257684496243418964213771 135386526744365128446320657)
          ·
            refine ⟨101539895058273846334740493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 135386526744365128446320657 101539895058273846334740493)
            ·
              refine ⟨38077460646852692375527685, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101539895058273846334740493 38077460646852692375527685)
              ·
                refine ⟨7139523871284879820411441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38077460646852692375527685 7139523871284879820411441)
                ·
                  refine ⟨5354642903463659865308581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139523871284879820411441 5354642903463659865308581)
                  ·
                    refine ⟨1003995544399436224745359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354642903463659865308581 1003995544399436224745359)
                    ·
                      rfl

theorem cell23_5865823_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 2, 3, 4, 2, 4].length) (baseStart_5865823 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865823 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865823 prefixEnd_5865823 := by exact prefixLift 5865823
  have htrace : WordTrace (prefixWord ++ tailWord_5865823) baseStart_5865823 baseEnd_5865823 := by
    simpa [prefixWord, tailWord_5865823, baseEnd_5865823] using wordTrace_append hprefix tailTrace_5865823
  have hstable : (prefixWord ++ tailWord_5865823).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865823).length < 2 ^ (prefixWord ++ tailWord_5865823).sum := by decide
  have hdescent : baseEnd_5865823 < baseStart_5865823 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865823) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865853 : List Nat := [1, 4, 1, 1, 2, 4, 3, 7]
def baseStart_5865853 : Nat := 118140960795 + 5865853 * 2 ^ 59
def prefixEnd_5865853 : Nat := 4983230072969 + 3 ^ 40 * 5865853 * 2
def baseEnd_5865853 : Nat := 111555631022886798402257

theorem tailTrace_5865853 : CollatzResearch.WordTrace tailWord_5865853 prefixEnd_5865853 111555631022886798402257 := by
  unfold tailWord_5865853
  simp only [CollatzResearch.WordTrace]
  refine ⟨213945235218023863779506213, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142630156812015909186337475 213945235218023863779506213)
  ·
    refine ⟨40114731603379474458657415, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213945235218023863779506213 40114731603379474458657415)
    ·
      refine ⟨60172097405069211687986123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40114731603379474458657415 60172097405069211687986123)
      ·
        refine ⟨90258146107603817531979185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60172097405069211687986123 90258146107603817531979185)
        ·
          refine ⟨67693609580702863148984389, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90258146107603817531979185 67693609580702863148984389)
          ·
            refine ⟨12692551796381786840434573, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 67693609580702863148984389 12692551796381786840434573)
            ·
              refine ⟨4759706923643170065162965, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12692551796381786840434573 4759706923643170065162965)
              ·
                refine ⟨111555631022886798402257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 4759706923643170065162965 111555631022886798402257)
                ·
                  rfl

theorem cell23_5865853_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 4, 3, 7].length) (baseStart_5865853 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865853 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865853 prefixEnd_5865853 := by exact prefixLift 5865853
  have htrace : WordTrace (prefixWord ++ tailWord_5865853) baseStart_5865853 baseEnd_5865853 := by
    simpa [prefixWord, tailWord_5865853, baseEnd_5865853] using wordTrace_append hprefix tailTrace_5865853
  have hstable : (prefixWord ++ tailWord_5865853).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865853).length < 2 ^ (prefixWord ++ tailWord_5865853).sum := by decide
  have hdescent : baseEnd_5865853 < baseStart_5865853 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865853) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865863 : List Nat := [1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 3]
def baseStart_5865863 : Nat := 118140960795 + 5865863 * 2 ^ 59
def prefixEnd_5865863 : Nat := 4983230072969 + 3 ^ 40 * 5865863 * 2
def baseEnd_5865863 : Nat := 3012007172424488517735893

theorem tailTrace_5865863 : CollatzResearch.WordTrace tailWord_5865863 prefixEnd_5865863 3012007172424488517735893 := by
  unfold tailWord_5865863
  simp only [CollatzResearch.WordTrace]
  refine ⟨213945599947987635487370243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142630399965325090324913495 213945599947987635487370243)
  ·
    refine ⟨320918399921981453231055365, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213945599947987635487370243 320918399921981453231055365)
    ·
      refine ⟨60172199985371522480822881, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320918399921981453231055365 60172199985371522480822881)
      ·
        refine ⟨45129149989028641860617161, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60172199985371522480822881 45129149989028641860617161)
        ·
          refine ⟨33846862491771481395462871, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45129149989028641860617161 33846862491771481395462871)
          ·
            refine ⟨50770293737657222093194307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33846862491771481395462871 50770293737657222093194307)
            ·
              refine ⟨76155440606485833139791461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50770293737657222093194307 76155440606485833139791461)
              ·
                refine ⟨14279145113716093713710899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 76155440606485833139791461 14279145113716093713710899)
                ·
                  refine ⟨21418717670574140570566349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14279145113716093713710899 21418717670574140570566349)
                  ·
                    refine ⟨8032019126465302713962381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 21418717670574140570566349 8032019126465302713962381)
                    ·
                      refine ⟨3012007172424488517735893, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8032019126465302713962381 3012007172424488517735893)
                      ·
                        rfl

theorem cell23_5865863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 2, 2, 1, 1, 4, 1, 3, 3].length) (baseStart_5865863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865863 prefixEnd_5865863 := by exact prefixLift 5865863
  have htrace : WordTrace (prefixWord ++ tailWord_5865863) baseStart_5865863 baseEnd_5865863 := by
    simpa [prefixWord, tailWord_5865863, baseEnd_5865863] using wordTrace_append hprefix tailTrace_5865863
  have hstable : (prefixWord ++ tailWord_5865863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865863).length < 2 ^ (prefixWord ++ tailWord_5865863).sum := by decide
  have hdescent : baseEnd_5865863 < baseStart_5865863 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865864 : List Nat := [2, 1, 3, 3, 1, 1, 4, 3, 1, 2, 2]
def baseStart_5865864 : Nat := 118140960795 + 5865864 * 2 ^ 59
def prefixEnd_5865864 : Nat := 4983230072969 + 3 ^ 40 * 5865864 * 2
def baseEnd_5865864 : Nat := 3012007685905143013823389

theorem tailTrace_5865864 : CollatzResearch.WordTrace tailWord_5865864 prefixEnd_5865864 3012007685905143013823389 := by
  unfold tailWord_5865864
  simp only [CollatzResearch.WordTrace]
  refine ⟨106972818210492006329078323, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142630424280656008438771097 106972818210492006329078323)
  ·
    refine ⟨160459227315738009493617485, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106972818210492006329078323 160459227315738009493617485)
    ·
      refine ⟨60172210243401753560106557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160459227315738009493617485 60172210243401753560106557)
      ·
        refine ⟨22564578841275657585039959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 60172210243401753560106557 22564578841275657585039959)
        ·
          refine ⟨33846868261913486377559939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22564578841275657585039959 33846868261913486377559939)
          ·
            refine ⟨50770302392870229566339909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33846868261913486377559939 50770302392870229566339909)
            ·
              refine ⟨9519431698663168043688733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50770302392870229566339909 9519431698663168043688733)
              ·
                refine ⟨3569786886998688016383275, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9519431698663168043688733 3569786886998688016383275)
                ·
                  refine ⟨5354680330498032024574913, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569786886998688016383275 5354680330498032024574913)
                  ·
                    refine ⟨4016010247873524018431185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5354680330498032024574913 4016010247873524018431185)
                    ·
                      refine ⟨3012007685905143013823389, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016010247873524018431185 3012007685905143013823389)
                      ·
                        rfl

theorem cell23_5865864_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 4, 3, 1, 2, 2].length) (baseStart_5865864 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865864 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865864 prefixEnd_5865864 := by exact prefixLift 5865864
  have htrace : WordTrace (prefixWord ++ tailWord_5865864) baseStart_5865864 baseEnd_5865864 := by
    simpa [prefixWord, tailWord_5865864, baseEnd_5865864] using wordTrace_append hprefix tailTrace_5865864
  have hstable : (prefixWord ++ tailWord_5865864).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865864).length < 2 ^ (prefixWord ++ tailWord_5865864).sum := by decide
  have hdescent : baseEnd_5865864 < baseStart_5865864 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865864) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865867 : List Nat := [1, 1, 1, 1, 4, 6, 2, 1, 1, 2, 3]
def baseStart_5865867 : Nat := 118140960795 + 5865867 * 2 ^ 59
def prefixEnd_5865867 : Nat := 4983230072969 + 3 ^ 40 * 5865867 * 2
def baseEnd_5865867 : Nat := 3012009226347106502085875

theorem tailTrace_5865867 : CollatzResearch.WordTrace tailWord_5865867 prefixEnd_5865867 3012009226347106502085875 := by
  unfold tailWord_5865867
  simp only [CollatzResearch.WordTrace]
  refine ⟨213945745839973144170515855, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142630497226648762780343903 213945745839973144170515855)
  ·
    refine ⟨320918618759959716255773783, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213945745839973144170515855 320918618759959716255773783)
    ·
      refine ⟨481377928139939574383660675, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320918618759959716255773783 481377928139939574383660675)
      ·
        refine ⟨722066892209909361575491013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481377928139939574383660675 722066892209909361575491013)
        ·
          refine ⟨135387542289358005295404565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 722066892209909361575491013 135387542289358005295404565)
          ·
            refine ⟨6346291044813656498222089, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135387542289358005295404565 6346291044813656498222089)
            ·
              refine ⟨4759718283610242373666567, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6346291044813656498222089 4759718283610242373666567)
              ·
                refine ⟨7139577425415363560499851, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4759718283610242373666567 7139577425415363560499851)
                ·
                  refine ⟨10709366138123045340749777, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7139577425415363560499851 10709366138123045340749777)
                  ·
                    refine ⟨8032024603592284005562333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10709366138123045340749777 8032024603592284005562333)
                    ·
                      refine ⟨3012009226347106502085875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8032024603592284005562333 3012009226347106502085875)
                      ·
                        rfl

theorem cell23_5865867_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 6, 2, 1, 1, 2, 3].length) (baseStart_5865867 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865867 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865867 prefixEnd_5865867 := by exact prefixLift 5865867
  have htrace : WordTrace (prefixWord ++ tailWord_5865867) baseStart_5865867 baseEnd_5865867 := by
    simpa [prefixWord, tailWord_5865867, baseEnd_5865867] using wordTrace_append hprefix tailTrace_5865867
  have hstable : (prefixWord ++ tailWord_5865867).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865867).length < 2 ^ (prefixWord ++ tailWord_5865867).sum := by decide
  have hdescent : baseEnd_5865867 < baseStart_5865867 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865867) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865953 : List Nat := [1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 3]
def baseStart_5865953 : Nat := 118140960795 + 5865953 * 2 ^ 59
def prefixEnd_5865953 : Nat := 4983230072969 + 3 ^ 40 * 5865953 * 2
def baseEnd_5865953 : Nat := 3012053385683393165610479

theorem tailTrace_5865953 : CollatzResearch.WordTrace tailWord_5865953 prefixEnd_5865953 3012053385683393165610479 := by
  unfold tailWord_5865953
  simp only [CollatzResearch.WordTrace]
  refine ⟨213948882517661580858146513, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142632588345107720572097675 213948882517661580858146513)
  ·
    refine ⟨160461661888246185643609885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213948882517661580858146513 160461661888246185643609885)
    ·
      refine ⟨60173123208092319616353707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160461661888246185643609885 60173123208092319616353707)
      ·
        refine ⟨90259684812138479424530561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60173123208092319616353707 90259684812138479424530561)
        ·
          refine ⟨67694763609103859568397921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90259684812138479424530561 67694763609103859568397921)
          ·
            refine ⟨50771072706827894676298441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 67694763609103859568397921 50771072706827894676298441)
            ·
              refine ⟨38078304530120921007223831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50771072706827894676298441 38078304530120921007223831)
              ·
                refine ⟨57117456795181381510835747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38078304530120921007223831 57117456795181381510835747)
                ·
                  refine ⟨85676185192772072266253621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57117456795181381510835747 85676185192772072266253621)
                  ·
                    refine ⟨8032142361822381774961277, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85676185192772072266253621 8032142361822381774961277)
                    ·
                      refine ⟨3012053385683393165610479, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8032142361822381774961277 3012053385683393165610479)
                      ·
                        rfl

theorem cell23_5865953_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 2, 2, 1, 1, 5, 3].length) (baseStart_5865953 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865953 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865953 prefixEnd_5865953 := by exact prefixLift 5865953
  have htrace : WordTrace (prefixWord ++ tailWord_5865953) baseStart_5865953 baseEnd_5865953 := by
    simpa [prefixWord, tailWord_5865953, baseEnd_5865953] using wordTrace_append hprefix tailTrace_5865953
  have hstable : (prefixWord ++ tailWord_5865953).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865953).length < 2 ^ (prefixWord ++ tailWord_5865953).sum := by decide
  have hdescent : baseEnd_5865953 < baseStart_5865953 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865953) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5865993 : List Nat := [1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 4]
def baseStart_5865993 : Nat := 118140960795 + 5865993 * 2 ^ 59
def prefixEnd_5865993 : Nat := 4983230072969 + 3 ^ 40 * 5865993 * 2
def baseEnd_5865993 : Nat := 3012073924909573009110295

theorem tailTrace_5865993 : CollatzResearch.WordTrace tailWord_5865993 prefixEnd_5865993 3012073924909573009110295 := by
  unfold tailWord_5865993
  simp only [CollatzResearch.WordTrace]
  refine ⟨213950341437516667689602633, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142633560958344445126401755 213950341437516667689602633)
  ·
    refine ⟨160462756078137500767201975, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213950341437516667689602633 160462756078137500767201975)
    ·
      refine ⟨240694134117206251150802963, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160462756078137500767201975 240694134117206251150802963)
      ·
        refine ⟨361041201175809376726204445, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240694134117206251150802963 361041201175809376726204445)
        ·
          refine ⟨135390450440928516272326667, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361041201175809376726204445 135390450440928516272326667)
          ·
            refine ⟨203085675661392774408490001, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135390450440928516272326667 203085675661392774408490001)
            ·
              refine ⟨152314256746044580806367501, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203085675661392774408490001 152314256746044580806367501)
              ·
                refine ⟨57117846279766717802387813, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 152314256746044580806367501 57117846279766717802387813)
                ·
                  refine ⟨10709596177456259587947715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 57117846279766717802387813 10709596177456259587947715)
                  ·
                    refine ⟨16064394266184389381921573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10709596177456259587947715 16064394266184389381921573)
                    ·
                      refine ⟨3012073924909573009110295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16064394266184389381921573 3012073924909573009110295)
                      ·
                        rfl

theorem cell23_5865993_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 3, 1, 2, 3, 4, 1, 4].length) (baseStart_5865993 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5865993 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5865993 prefixEnd_5865993 := by exact prefixLift 5865993
  have htrace : WordTrace (prefixWord ++ tailWord_5865993) baseStart_5865993 baseEnd_5865993 := by
    simpa [prefixWord, tailWord_5865993, baseEnd_5865993] using wordTrace_append hprefix tailTrace_5865993
  have hstable : (prefixWord ++ tailWord_5865993).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5865993).length < 2 ^ (prefixWord ++ tailWord_5865993).sum := by decide
  have hdescent : baseEnd_5865993 < baseStart_5865993 := by decide
  rcases family_descends (prefixWord ++ tailWord_5865993) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866010 : List Nat := [3, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2]
def baseStart_5866010 : Nat := 118140960795 + 5866010 * 2 ^ 59
def prefixEnd_5866010 : Nat := 4983230072969 + 3 ^ 40 * 5866010 * 2
def baseEnd_5866010 : Nat := 3012082654080699442597717

theorem tailTrace_5866010 : CollatzResearch.WordTrace tailWord_5866010 prefixEnd_5866010 3012082654080699442597717 := by
  unfold tailWord_5866010
  simp only [CollatzResearch.WordTrace]
  refine ⟨53487740369613769898242871, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142633974318970053061980989 53487740369613769898242871)
  ·
    refine ⟨80231610554420654847364307, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53487740369613769898242871 80231610554420654847364307)
    ·
      refine ⟨120347415831630982271046461, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80231610554420654847364307 120347415831630982271046461)
      ·
        refine ⟨45130280936861618351642423, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 120347415831630982271046461 45130280936861618351642423)
        ·
          refine ⟨67695421405292427527463635, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45130280936861618351642423 67695421405292427527463635)
          ·
            refine ⟨101543132107938641291195453, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67695421405292427527463635 101543132107938641291195453)
            ·
              refine ⟨38078674540476990484198295, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101543132107938641291195453 38078674540476990484198295)
              ·
                refine ⟨57118011810715485726297443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38078674540476990484198295 57118011810715485726297443)
                ·
                  refine ⟨85677017716073228589446165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57118011810715485726297443 85677017716073228589446165)
                  ·
                    refine ⟨4016110205440932590130289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 85677017716073228589446165 4016110205440932590130289)
                    ·
                      refine ⟨3012082654080699442597717, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016110205440932590130289 3012082654080699442597717)
                      ·
                        rfl

theorem cell23_5866010_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 1, 3, 1, 1, 6, 2].length) (baseStart_5866010 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866010 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866010 prefixEnd_5866010 := by exact prefixLift 5866010
  have htrace : WordTrace (prefixWord ++ tailWord_5866010) baseStart_5866010 baseEnd_5866010 := by
    simpa [prefixWord, tailWord_5866010, baseEnd_5866010] using wordTrace_append hprefix tailTrace_5866010
  have hstable : (prefixWord ++ tailWord_5866010).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866010).length < 2 ^ (prefixWord ++ tailWord_5866010).sum := by decide
  have hdescent : baseEnd_5866010 < baseStart_5866010 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866010) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866053 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 6]
def baseStart_5866053 : Nat := 118140960795 + 5866053 * 2 ^ 59
def prefixEnd_5866053 : Nat := 4983230072969 + 3 ^ 40 * 5866053 * 2
def baseEnd_5866053 : Nat := 3012104733748842774360019

theorem tailTrace_5866053 : CollatzResearch.WordTrace tailWord_5866053 prefixEnd_5866053 3012104733748842774360019 := by
  unfold tailWord_5866053
  simp only [CollatzResearch.WordTrace]
  refine ⟨213952529817299297936786813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142635019878199531957857875 213952529817299297936786813)
  ·
    refine ⟨80232198681487236726295055, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213952529817299297936786813 80232198681487236726295055)
    ·
      refine ⟨120348298022230855089442583, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80232198681487236726295055 120348298022230855089442583)
      ·
        refine ⟨180522447033346282634163875, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120348298022230855089442583 180522447033346282634163875)
        ·
          refine ⟨270783670550019423951245813, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180522447033346282634163875 270783670550019423951245813)
          ·
            refine ⟨25385969114064320995429295, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270783670550019423951245813 25385969114064320995429295)
            ·
              refine ⟨38078953671096481493143943, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25385969114064320995429295 38078953671096481493143943)
              ·
                refine ⟨57118430506644722239715915, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38078953671096481493143943 57118430506644722239715915)
                ·
                  refine ⟨85677645759967083359573873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57118430506644722239715915 85677645759967083359573873)
                  ·
                    refine ⟨64258234319975312519680405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 85677645759967083359573873 64258234319975312519680405)
                    ·
                      refine ⟨3012104733748842774360019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 64258234319975312519680405 3012104733748842774360019)
                      ·
                        rfl

theorem cell23_5866053_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 1, 2, 6].length) (baseStart_5866053 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866053 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866053 prefixEnd_5866053 := by exact prefixLift 5866053
  have htrace : WordTrace (prefixWord ++ tailWord_5866053) baseStart_5866053 baseEnd_5866053 := by
    simpa [prefixWord, tailWord_5866053, baseEnd_5866053] using wordTrace_append hprefix tailTrace_5866053
  have hstable : (prefixWord ++ tailWord_5866053).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866053).length < 2 ^ (prefixWord ++ tailWord_5866053).sum := by decide
  have hdescent : baseEnd_5866053 < baseStart_5866053 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866053) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866054 : List Nat := [6, 1, 1, 1, 2, 1, 1, 3, 3, 4]
def baseStart_5866054 : Nat := 118140960795 + 5866054 * 2 ^ 59
def prefixEnd_5866054 : Nat := 4983230072969 + 3 ^ 40 * 5866054 * 2
def baseEnd_5866054 : Nat := 1004035082409832423482505

theorem tailTrace_5866054 : CollatzResearch.WordTrace tailWord_5866054 prefixEnd_5866054 1004035082409832423482505 := by
  unfold tailWord_5866054
  simp only [CollatzResearch.WordTrace]
  refine ⟨6686017696571739847111663, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 142635044193530450071715477 6686017696571739847111663)
  ·
    refine ⟨10029026544857609770667495, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 6686017696571739847111663 10029026544857609770667495)
    ·
      refine ⟨15043539817286414656001243, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10029026544857609770667495 15043539817286414656001243)
      ·
        refine ⟨22565309725929621984001865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15043539817286414656001243 22565309725929621984001865)
        ·
          refine ⟨16923982294447216488001399, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22565309725929621984001865 16923982294447216488001399)
          ·
            refine ⟨25385973441670824732002099, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16923982294447216488001399 25385973441670824732002099)
            ·
              refine ⟨38078960162506237098003149, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25385973441670824732002099 38078960162506237098003149)
              ·
                refine ⟨14279610060939838911751181, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 38078960162506237098003149 14279610060939838911751181)
                ·
                  refine ⟨5354853772852439591906693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14279610060939838911751181 5354853772852439591906693)
                  ·
                    refine ⟨1004035082409832423482505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354853772852439591906693 1004035082409832423482505)
                    ·
                      rfl

theorem cell23_5866054_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 1, 2, 1, 1, 3, 3, 4].length) (baseStart_5866054 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866054 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866054 prefixEnd_5866054 := by exact prefixLift 5866054
  have htrace : WordTrace (prefixWord ++ tailWord_5866054) baseStart_5866054 baseEnd_5866054 := by
    simpa [prefixWord, tailWord_5866054, baseEnd_5866054] using wordTrace_append hprefix tailTrace_5866054
  have hstable : (prefixWord ++ tailWord_5866054).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866054).length < 2 ^ (prefixWord ++ tailWord_5866054).sum := by decide
  have hdescent : baseEnd_5866054 < baseStart_5866054 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866054) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866063 : List Nat := [1, 1, 2, 1, 1, 2, 4, 1, 5, 5]
def baseStart_5866063 : Nat := 118140960795 + 5866063 * 2 ^ 59
def prefixEnd_5866063 : Nat := 4983230072969 + 3 ^ 40 * 5866063 * 2
def baseEnd_5866063 : Nat := 1004036622851795911744991

theorem tailTrace_5866063 : CollatzResearch.WordTrace tailWord_5866063 prefixEnd_5866063 1004036622851795911744991 := by
  unfold tailWord_5866063
  simp only [CollatzResearch.WordTrace]
  refine ⟨213952894547263069644650843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142635263031508713096433895 213952894547263069644650843)
  ·
    refine ⟨320929341820894604466976265, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213952894547263069644650843 320929341820894604466976265)
    ·
      refine ⟨240697006365670953350232199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320929341820894604466976265 240697006365670953350232199)
      ·
        refine ⟨361045509548506430025348299, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240697006365670953350232199 361045509548506430025348299)
        ·
          refine ⟨541568264322759645038022449, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361045509548506430025348299 541568264322759645038022449)
          ·
            refine ⟨406176198242069733778516837, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541568264322759645038022449 406176198242069733778516837)
            ·
              refine ⟨76158037170388075083471907, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 406176198242069733778516837 76158037170388075083471907)
              ·
                refine ⟨114237055755582112625207861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76158037170388075083471907 114237055755582112625207861)
                ·
                  refine ⟨10709723977085823058613237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114237055755582112625207861 10709723977085823058613237)
                  ·
                    refine ⟨1004036622851795911744991, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10709723977085823058613237 1004036622851795911744991)
                    ·
                      rfl

theorem cell23_5866063_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 2, 4, 1, 5, 5].length) (baseStart_5866063 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866063 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866063 prefixEnd_5866063 := by exact prefixLift 5866063
  have htrace : WordTrace (prefixWord ++ tailWord_5866063) baseStart_5866063 baseEnd_5866063 := by
    simpa [prefixWord, tailWord_5866063, baseEnd_5866063] using wordTrace_append hprefix tailTrace_5866063
  have hstable : (prefixWord ++ tailWord_5866063).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866063).length < 2 ^ (prefixWord ++ tailWord_5866063).sum := by decide
  have hdescent : baseEnd_5866063 < baseStart_5866063 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866063) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866080 : List Nat := [2, 1, 1, 3, 2, 1, 3, 4, 1, 5]
def baseStart_5866080 : Nat := 118140960795 + 5866080 * 2 ^ 59
def prefixEnd_5866080 : Nat := 4983230072969 + 3 ^ 40 * 5866080 * 2
def baseEnd_5866080 : Nat := 1004039532575504722907465

theorem tailTrace_5866080 : CollatzResearch.WordTrace tailWord_5866080 prefixEnd_5866080 1004039532575504722907465 := by
  unfold tailWord_5866080
  simp only [CollatzResearch.WordTrace]
  refine ⟨106976757294100740774009847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142635676392134321032013129 106976757294100740774009847)
  ·
    refine ⟨160465135941151111161014771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106976757294100740774009847 160465135941151111161014771)
    ·
      refine ⟨240697703911726666741522157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160465135941151111161014771 240697703911726666741522157)
      ·
        refine ⟨90261638966897500028070809, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240697703911726666741522157 90261638966897500028070809)
        ·
          refine ⟨67696229225173125021053107, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90261638966897500028070809 67696229225173125021053107)
          ·
            refine ⟨101544343837759687531579661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67696229225173125021053107 101544343837759687531579661)
            ·
              refine ⟨38079128939159882824342373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 101544343837759687531579661 38079128939159882824342373)
              ·
                refine ⟨7139836676092478029564195, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 38079128939159882824342373 7139836676092478029564195)
                ·
                  refine ⟨10709755014138717044346293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7139836676092478029564195 10709755014138717044346293)
                  ·
                    refine ⟨1004039532575504722907465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10709755014138717044346293 1004039532575504722907465)
                    ·
                      rfl

theorem cell23_5866080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 2, 1, 3, 4, 1, 5].length) (baseStart_5866080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866080 prefixEnd_5866080 := by exact prefixLift 5866080
  have htrace : WordTrace (prefixWord ++ tailWord_5866080) baseStart_5866080 baseEnd_5866080 := by
    simpa [prefixWord, tailWord_5866080, baseEnd_5866080] using wordTrace_append hprefix tailTrace_5866080
  have hstable : (prefixWord ++ tailWord_5866080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866080).length < 2 ^ (prefixWord ++ tailWord_5866080).sum := by decide
  have hdescent : baseEnd_5866080 < baseStart_5866080 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866087 : List Nat := [1, 1, 5, 1, 1, 1, 1, 5, 2, 3, 2]
def baseStart_5866087 : Nat := 118140960795 + 5866087 * 2 ^ 59
def prefixEnd_5866087 : Nat := 4983230072969 + 3 ^ 40 * 5866087 * 2
def baseEnd_5866087 : Nat := 3012122192091095641334863

theorem tailTrace_5866087 : CollatzResearch.WordTrace tailWord_5866087 prefixEnd_5866087 3012122192091095641334863 := by
  unfold tailWord_5866087
  simp only [CollatzResearch.WordTrace]
  refine ⟨213953769899176121743524515, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142635846599450747829016343 213953769899176121743524515)
  ·
    refine ⟨320930654848764182615286773, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213953769899176121743524515 320930654848764182615286773)
    ·
      refine ⟨30087248892071642120183135, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 320930654848764182615286773 30087248892071642120183135)
      ·
        refine ⟨45130873338107463180274703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30087248892071642120183135 45130873338107463180274703)
        ·
          refine ⟨67696310007161194770412055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45130873338107463180274703 67696310007161194770412055)
          ·
            refine ⟨101544465010741792155618083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67696310007161194770412055 101544465010741792155618083)
            ·
              refine ⟨152316697516112688233427125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101544465010741792155618083 152316697516112688233427125)
              ·
                refine ⟨14279690392135564521883793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 152316697516112688233427125 14279690392135564521883793)
                ·
                  refine ⟨10709767794101673391412845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14279690392135564521883793 10709767794101673391412845)
                  ·
                    refine ⟨4016162922788127521779817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10709767794101673391412845 4016162922788127521779817)
                    ·
                      refine ⟨3012122192091095641334863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016162922788127521779817 3012122192091095641334863)
                      ·
                        rfl

theorem cell23_5866087_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 1, 1, 1, 5, 2, 3, 2].length) (baseStart_5866087 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866087 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866087 prefixEnd_5866087 := by exact prefixLift 5866087
  have htrace : WordTrace (prefixWord ++ tailWord_5866087) baseStart_5866087 baseEnd_5866087 := by
    simpa [prefixWord, tailWord_5866087, baseEnd_5866087] using wordTrace_append hprefix tailTrace_5866087
  have hstable : (prefixWord ++ tailWord_5866087).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866087).length < 2 ^ (prefixWord ++ tailWord_5866087).sum := by decide
  have hdescent : baseEnd_5866087 < baseStart_5866087 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866087) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866088 : List Nat := [2, 1, 4, 3, 3, 1, 1, 3, 1, 4]
def baseStart_5866088 : Nat := 118140960795 + 5866088 * 2 ^ 59
def prefixEnd_5866088 : Nat := 4983230072969 + 3 ^ 40 * 5866088 * 2
def baseEnd_5866088 : Nat := 1004040901857250045807453

theorem tailTrace_5866088 : CollatzResearch.WordTrace tailWord_5866088 prefixEnd_5866088 1004040901857250045807453 := by
  unfold tailWord_5866088
  simp only [CollatzResearch.WordTrace]
  refine ⟨106976903186086249457155459, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142635870914781665942873945 106976903186086249457155459)
  ·
    refine ⟨160465354779129374185733189, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106976903186086249457155459 160465354779129374185733189)
    ·
      refine ⟨30087254021086757659824973, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160465354779129374185733189 30087254021086757659824973)
      ·
        refine ⟨11282720257907534122434365, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 30087254021086757659824973 11282720257907534122434365)
        ·
          refine ⟨4231020096715325295912887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11282720257907534122434365 4231020096715325295912887)
          ·
            refine ⟨6346530145072987943869331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231020096715325295912887 6346530145072987943869331)
            ·
              refine ⟨9519795217609481915803997, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6346530145072987943869331 9519795217609481915803997)
              ·
                refine ⟨3569923206603555718426499, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 9519795217609481915803997 3569923206603555718426499)
                ·
                  refine ⟨5354884809905333577639749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 3569923206603555718426499 5354884809905333577639749)
                  ·
                    refine ⟨1004040901857250045807453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354884809905333577639749 1004040901857250045807453)
                    ·
                      rfl

theorem cell23_5866088_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 3, 3, 1, 1, 3, 1, 4].length) (baseStart_5866088 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866088 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866088 prefixEnd_5866088 := by exact prefixLift 5866088
  have htrace : WordTrace (prefixWord ++ tailWord_5866088) baseStart_5866088 baseEnd_5866088 := by
    simpa [prefixWord, tailWord_5866088, baseEnd_5866088] using wordTrace_append hprefix tailTrace_5866088
  have hstable : (prefixWord ++ tailWord_5866088).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866088).length < 2 ^ (prefixWord ++ tailWord_5866088).sum := by decide
  have hdescent : baseEnd_5866088 < baseStart_5866088 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866088) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866140 : List Nat := [2, 2, 3, 2, 2, 1, 2, 9]
def baseStart_5866140 : Nat := 118140960795 + 5866140 * 2 ^ 59
def prefixEnd_5866140 : Nat := 4983230072969 + 3 ^ 40 * 5866140 * 2
def baseEnd_5866140 : Nat := 111561089132066071628597

theorem tailTrace_5866140 : CollatzResearch.WordTrace tailWord_5866140 prefixEnd_5866140 111561089132066071628597 := by
  unfold tailWord_5866140
  simp only [CollatzResearch.WordTrace]
  refine ⟨106977851483992055897601937, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142637135311989407863469249 106977851483992055897601937)
  ·
    refine ⟨80233388612994041923201453, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 106977851483992055897601937 80233388612994041923201453)
    ·
      refine ⟨30087520729872765721200545, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80233388612994041923201453 30087520729872765721200545)
      ·
        refine ⟨22565640547404574290900409, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30087520729872765721200545 22565640547404574290900409)
        ·
          refine ⟨16924230410553430718175307, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 22565640547404574290900409 16924230410553430718175307)
          ·
            refine ⟨25386345615830146077262961, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16924230410553430718175307 25386345615830146077262961)
            ·
              refine ⟨19039759211872609557947221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25386345615830146077262961 19039759211872609557947221)
              ·
                refine ⟨111561089132066071628597, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 19039759211872609557947221 111561089132066071628597)
                ·
                  rfl

theorem cell23_5866140_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 2, 1, 2, 9].length) (baseStart_5866140 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866140 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866140 prefixEnd_5866140 := by exact prefixLift 5866140
  have htrace : WordTrace (prefixWord ++ tailWord_5866140) baseStart_5866140 baseEnd_5866140 := by
    simpa [prefixWord, tailWord_5866140, baseEnd_5866140] using wordTrace_append hprefix tailTrace_5866140
  have hstable : (prefixWord ++ tailWord_5866140).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866140).length < 2 ^ (prefixWord ++ tailWord_5866140).sum := by decide
  have hdescent : baseEnd_5866140 < baseStart_5866140 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866140) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866153 : List Nat := [1, 2, 1, 1, 1, 1, 2, 4, 1, 9]
def baseStart_5866153 : Nat := 118140960795 + 5866153 * 2 ^ 59
def prefixEnd_5866153 : Nat := 4983230072969 + 3 ^ 40 * 5866153 * 2
def baseEnd_5866153 : Nat := 1004052027271430794369853

theorem tailTrace_5866153 : CollatzResearch.WordTrace tailWord_5866153 prefixEnd_5866153 1004052027271430794369853 := by
  unfold tailWord_5866153
  simp only [CollatzResearch.WordTrace]
  refine ⟨213956177116937015015427113, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142637451411291343343618075 213956177116937015015427113)
  ·
    refine ⟨160467132837702761261570335, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213956177116937015015427113 160467132837702761261570335)
    ·
      refine ⟨240700699256554141892355503, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160467132837702761261570335 240700699256554141892355503)
      ·
        refine ⟨361051048884831212838533255, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240700699256554141892355503 361051048884831212838533255)
        ·
          refine ⟨541576573327246819257799883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361051048884831212838533255 541576573327246819257799883)
          ·
            refine ⟨812364859990870228886699825, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541576573327246819257799883 812364859990870228886699825)
            ·
              refine ⟨609273644993152671665024869, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 812364859990870228886699825 609273644993152671665024869)
              ·
                refine ⟨114238808436216125937192163, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609273644993152671665024869 114238808436216125937192163)
                ·
                  refine ⟨171358212654324188905788245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 114238808436216125937192163 171358212654324188905788245)
                  ·
                    refine ⟨1004052027271430794369853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 171358212654324188905788245 1004052027271430794369853)
                    ·
                      rfl

theorem cell23_5866153_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 2, 4, 1, 9].length) (baseStart_5866153 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866153 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866153 prefixEnd_5866153 := by exact prefixLift 5866153
  have htrace : WordTrace (prefixWord ++ tailWord_5866153) baseStart_5866153 baseEnd_5866153 := by
    simpa [prefixWord, tailWord_5866153, baseEnd_5866153] using wordTrace_append hprefix tailTrace_5866153
  have hstable : (prefixWord ++ tailWord_5866153).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866153).length < 2 ^ (prefixWord ++ tailWord_5866153).sum := by decide
  have hdescent : baseEnd_5866153 < baseStart_5866153 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866153) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866161 : List Nat := [1, 2, 2, 6, 1, 1, 2, 2, 2, 4]
def baseStart_5866161 : Nat := 118140960795 + 5866161 * 2 ^ 59
def prefixEnd_5866161 : Nat := 4983230072969 + 3 ^ 40 * 5866161 * 2
def baseEnd_5866161 : Nat := 1004053396553176117269841

theorem tailTrace_5866161 : CollatzResearch.WordTrace tailWord_5866161 prefixEnd_5866161 1004053396553176117269841 := by
  unfold tailWord_5866161
  simp only [CollatzResearch.WordTrace]
  refine ⟨213956468900908032381718337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142637645933938688254478891 213956468900908032381718337)
  ·
    refine ⟨160467351675681024286288753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213956468900908032381718337 160467351675681024286288753)
    ·
      refine ⟨120350513756760768214716565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160467351675681024286288753 120350513756760768214716565)
      ·
        refine ⟨5641430332348161010064839, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 120350513756760768214716565 5641430332348161010064839)
        ·
          refine ⟨8462145498522241515097259, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5641430332348161010064839 8462145498522241515097259)
          ·
            refine ⟨12693218247783362272645889, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462145498522241515097259 12693218247783362272645889)
            ·
              refine ⟨9519913685837521704484417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12693218247783362272645889 9519913685837521704484417)
              ·
                refine ⟨7139935264378141278363313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9519913685837521704484417 7139935264378141278363313)
                ·
                  refine ⟨5354951448283605958772485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139935264378141278363313 5354951448283605958772485)
                  ·
                    refine ⟨1004053396553176117269841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5354951448283605958772485 1004053396553176117269841)
                    ·
                      rfl

theorem cell23_5866161_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 6, 1, 1, 2, 2, 2, 4].length) (baseStart_5866161 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866161 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866161 prefixEnd_5866161 := by exact prefixLift 5866161
  have htrace : WordTrace (prefixWord ++ tailWord_5866161) baseStart_5866161 baseEnd_5866161 := by
    simpa [prefixWord, tailWord_5866161, baseEnd_5866161] using wordTrace_append hprefix tailTrace_5866161
  have hstable : (prefixWord ++ tailWord_5866161).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866161).length < 2 ^ (prefixWord ++ tailWord_5866161).sum := by decide
  have hdescent : baseEnd_5866161 < baseStart_5866161 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866161) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866184 : List Nat := [2, 1, 3, 1, 2, 3, 2, 3, 2, 1, 3]
def baseStart_5866184 : Nat := 118140960795 + 5866184 * 2 ^ 59
def prefixEnd_5866184 : Nat := 4983230072969 + 3 ^ 40 * 5866184 * 2
def baseEnd_5866184 : Nat := 3012171999714581761821917

theorem tailTrace_5866184 : CollatzResearch.WordTrace tailWord_5866184 prefixEnd_5866184 3012171999714581761821917 := by
  unfold tailWord_5866184
  simp only [CollatzResearch.WordTrace]
  refine ⟨106978653889912353654902803, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142638205186549804873203737 106978653889912353654902803)
  ·
    refine ⟨160467980834868530482354205, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106978653889912353654902803 160467980834868530482354205)
    ·
      refine ⟨60175492813075698930882827, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160467980834868530482354205 60175492813075698930882827)
      ·
        refine ⟨90263239219613548396324241, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60175492813075698930882827 90263239219613548396324241)
        ·
          refine ⟨67697429414710161297243181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90263239219613548396324241 67697429414710161297243181)
          ·
            refine ⟨25386536030516310486466193, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67697429414710161297243181 25386536030516310486466193)
            ·
              refine ⟨19039902022887232864849645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25386536030516310486466193 19039902022887232864849645)
              ·
                refine ⟨7139963258582712324318617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19039902022887232864849645 7139963258582712324318617)
                ·
                  refine ⟨5354972443937034243238963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7139963258582712324318617 5354972443937034243238963)
                  ·
                    refine ⟨8032458665905551364858445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5354972443937034243238963 8032458665905551364858445)
                    ·
                      refine ⟨3012171999714581761821917, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8032458665905551364858445 3012171999714581761821917)
                      ·
                        rfl

theorem cell23_5866184_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 2, 3, 2, 3, 2, 1, 3].length) (baseStart_5866184 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866184 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866184 prefixEnd_5866184 := by exact prefixLift 5866184
  have htrace : WordTrace (prefixWord ++ tailWord_5866184) baseStart_5866184 baseEnd_5866184 := by
    simpa [prefixWord, tailWord_5866184, baseEnd_5866184] using wordTrace_append hprefix tailTrace_5866184
  have hstable : (prefixWord ++ tailWord_5866184).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866184).length < 2 ^ (prefixWord ++ tailWord_5866184).sum := by decide
  have hdescent : baseEnd_5866184 < baseStart_5866184 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866184) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866211 : List Nat := [1, 1, 1, 7, 1, 2, 1, 3, 1, 3, 2]
def baseStart_5866211 : Nat := 118140960795 + 5866211 * 2 ^ 59
def prefixEnd_5866211 : Nat := 4983230072969 + 3 ^ 40 * 5866211 * 2
def baseEnd_5866211 : Nat := 3012185863692253156184293

theorem tailTrace_5866211 : CollatzResearch.WordTrace tailWord_5866211 prefixEnd_5866211 3012185863692253156184293 := by
  unfold tailWord_5866211
  simp only [CollatzResearch.WordTrace]
  refine ⟨213958292550726890921038487, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142638861700484593947358991 213958292550726890921038487)
  ·
    refine ⟨320937438826090336381557731, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213958292550726890921038487 320937438826090336381557731)
    ·
      refine ⟨481406158239135504572336597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320937438826090336381557731 481406158239135504572336597)
      ·
        refine ⟨11282956833729738388414139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 7 481406158239135504572336597 11282956833729738388414139)
        ·
          refine ⟨16924435250594607582621209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11282956833729738388414139 16924435250594607582621209)
          ·
            refine ⟨12693326437945955686965907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16924435250594607582621209 12693326437945955686965907)
            ·
              refine ⟨19039989656918933530448861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12693326437945955686965907 19039989656918933530448861)
              ·
                refine ⟨7139996121344600073918323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19039989656918933530448861 7139996121344600073918323)
                ·
                  refine ⟨10709994182016900110877485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7139996121344600073918323 10709994182016900110877485)
                  ·
                    refine ⟨4016247818256337541579057, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10709994182016900110877485 4016247818256337541579057)
                    ·
                      refine ⟨3012185863692253156184293, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016247818256337541579057 3012185863692253156184293)
                      ·
                        rfl

theorem cell23_5866211_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 7, 1, 2, 1, 3, 1, 3, 2].length) (baseStart_5866211 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866211 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866211 prefixEnd_5866211 := by exact prefixLift 5866211
  have htrace : WordTrace (prefixWord ++ tailWord_5866211) baseStart_5866211 baseEnd_5866211 := by
    simpa [prefixWord, tailWord_5866211, baseEnd_5866211] using wordTrace_append hprefix tailTrace_5866211
  have hstable : (prefixWord ++ tailWord_5866211).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866211).length < 2 ^ (prefixWord ++ tailWord_5866211).sum := by decide
  have hdescent : baseEnd_5866211 < baseStart_5866211 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866211) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866224 : List Nat := [2, 1, 1, 1, 3, 1, 5, 1, 4, 2, 2]
def baseStart_5866224 : Nat := 118140960795 + 5866224 * 2 ^ 59
def prefixEnd_5866224 : Nat := 4983230072969 + 3 ^ 40 * 5866224 * 2
def baseEnd_5866224 : Nat := 3012192538940761605321733

theorem tailTrace_5866224 : CollatzResearch.WordTrace tailWord_5866224 prefixEnd_5866224 3012192538940761605321733 := by
  unfold tailWord_5866224
  simp only [CollatzResearch.WordTrace]
  refine ⟨106979383349839897070630863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142639177799786529427507817 106979383349839897070630863)
  ·
    refine ⟨160469075024759845605946295, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106979383349839897070630863 160469075024759845605946295)
    ·
      refine ⟨240703612537139768408919443, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160469075024759845605946295 240703612537139768408919443)
      ·
        refine ⟨361055418805709652613379165, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240703612537139768408919443 361055418805709652613379165)
        ·
          refine ⟨135395782052141119730017187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361055418805709652613379165 135395782052141119730017187)
          ·
            refine ⟨203093673078211679595025781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135395782052141119730017187 203093673078211679595025781)
            ·
              refine ⟨19040031851082344962033667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 203093673078211679595025781 19040031851082344962033667)
              ·
                refine ⟨28560047776623517443050501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19040031851082344962033667 28560047776623517443050501)
                ·
                  refine ⟨5355008958116909520571969, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28560047776623517443050501 5355008958116909520571969)
                  ·
                    refine ⟨4016256718587682140428977, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5355008958116909520571969 4016256718587682140428977)
                    ·
                      refine ⟨3012192538940761605321733, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016256718587682140428977 3012192538940761605321733)
                      ·
                        rfl

theorem cell23_5866224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 1, 5, 1, 4, 2, 2].length) (baseStart_5866224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866224 prefixEnd_5866224 := by exact prefixLift 5866224
  have htrace : WordTrace (prefixWord ++ tailWord_5866224) baseStart_5866224 baseEnd_5866224 := by
    simpa [prefixWord, tailWord_5866224, baseEnd_5866224] using wordTrace_append hprefix tailTrace_5866224
  have hstable : (prefixWord ++ tailWord_5866224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866224).length < 2 ^ (prefixWord ++ tailWord_5866224).sum := by decide
  have hdescent : baseEnd_5866224 < baseStart_5866224 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866247 : List Nat := [1, 1, 4, 4, 1, 1, 2, 2, 7]
def baseStart_5866247 : Nat := 118140960795 + 5866247 * 2 ^ 59
def prefixEnd_5866247 : Nat := 4983230072969 + 3 ^ 40 * 5866247 * 2
def baseEnd_5866247 : Nat := 334689372110646112814903

theorem tailTrace_5866247 : CollatzResearch.WordTrace tailWord_5866247 prefixEnd_5866247 334689372110646112814903 := by
  unfold tailWord_5866247
  simp only [CollatzResearch.WordTrace]
  refine ⟨213959605578596469069348995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142639737052397646046232663 213959605578596469069348995)
  ·
    refine ⟨320939408367894703604023493, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213959605578596469069348995 320939408367894703604023493)
    ·
      refine ⟨60176139068980256925754405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320939408367894703604023493 60176139068980256925754405)
      ·
        refine ⟨11283026075433798173578951, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 60176139068980256925754405 11283026075433798173578951)
        ·
          refine ⟨16924539113150697260368427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 11283026075433798173578951 16924539113150697260368427)
          ·
            refine ⟨25386808669726045890552641, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 16924539113150697260368427 25386808669726045890552641)
            ·
              refine ⟨19040106502294534417914481, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25386808669726045890552641 19040106502294534417914481)
              ·
                refine ⟨14280079876720900813435861, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19040106502294534417914481 14280079876720900813435861)
                ·
                  refine ⟨334689372110646112814903, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14280079876720900813435861 334689372110646112814903)
                  ·
                    rfl

theorem cell23_5866247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 4, 1, 1, 2, 2, 7].length) (baseStart_5866247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866247 prefixEnd_5866247 := by exact prefixLift 5866247
  have htrace : WordTrace (prefixWord ++ tailWord_5866247) baseStart_5866247 baseEnd_5866247 := by
    simpa [prefixWord, tailWord_5866247, baseEnd_5866247] using wordTrace_append hprefix tailTrace_5866247
  have hstable : (prefixWord ++ tailWord_5866247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866247).length < 2 ^ (prefixWord ++ tailWord_5866247).sum := by decide
  have hdescent : baseEnd_5866247 < baseStart_5866247 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866277 : List Nat := [1, 3, 1, 2, 3, 1, 3, 2, 2, 5]
def baseStart_5866277 : Nat := 118140960795 + 5866277 * 2 ^ 59
def prefixEnd_5866277 : Nat := 4983230072969 + 3 ^ 40 * 5866277 * 2
def baseEnd_5866277 : Nat := 1004073251138483299319663

theorem tailTrace_5866277 : CollatzResearch.WordTrace tailWord_5866277 prefixEnd_5866277 1004073251138483299319663 := by
  unfold tailWord_5866277
  simp only [CollatzResearch.WordTrace]
  refine ⟨213960699768487784192941085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142640466512325189461960723 213960699768487784192941085)
  ·
    refine ⟨80235262413182919072352907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213960699768487784192941085 80235262413182919072352907)
    ·
      refine ⟨120352893619774378608529361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80235262413182919072352907 120352893619774378608529361)
      ·
        refine ⟨90264670214830783956397021, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120352893619774378608529361 90264670214830783956397021)
        ·
          refine ⟨33849251330561543983648883, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 90264670214830783956397021 33849251330561543983648883)
          ·
            refine ⟨50773876995842315975473325, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33849251330561543983648883 50773876995842315975473325)
            ·
              refine ⟨19040203873440868490802497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 50773876995842315975473325 19040203873440868490802497)
              ·
                refine ⟨14280152905080651368101873, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19040203873440868490802497 14280152905080651368101873)
                ·
                  refine ⟨10710114678810488526076405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14280152905080651368101873 10710114678810488526076405)
                  ·
                    refine ⟨1004073251138483299319663, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10710114678810488526076405 1004073251138483299319663)
                    ·
                      rfl

theorem cell23_5866277_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 2, 2, 5].length) (baseStart_5866277 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866277 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866277 prefixEnd_5866277 := by exact prefixLift 5866277
  have htrace : WordTrace (prefixWord ++ tailWord_5866277) baseStart_5866277 baseEnd_5866277 := by
    simpa [prefixWord, tailWord_5866277, baseEnd_5866277] using wordTrace_append hprefix tailTrace_5866277
  have hstable : (prefixWord ++ tailWord_5866277).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866277).length < 2 ^ (prefixWord ++ tailWord_5866277).sum := by decide
  have hdescent : baseEnd_5866277 < baseStart_5866277 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866277) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866292 : List Nat := [2, 5, 1, 1, 3, 2, 2, 1, 2, 2, 2]
def baseStart_5866292 : Nat := 118140960795 + 5866292 * 2 ^ 59
def prefixEnd_5866292 : Nat := 4983230072969 + 3 ^ 40 * 5866292 * 2
def baseEnd_5866292 : Nat := 3012227455625267339271421

theorem tailTrace_5866292 : CollatzResearch.WordTrace tailWord_5866292 prefixEnd_5866292 3012227455625267339271421 := by
  unfold tailWord_5866292
  simp only [CollatzResearch.WordTrace]
  refine ⟨106980623431716720877368565, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142640831242288961169824753 106980623431716720877368565)
  ·
    refine ⟨10029433446723442582253303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 106980623431716720877368565 10029433446723442582253303)
    ·
      refine ⟨15044150170085163873379955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 10029433446723442582253303 15044150170085163873379955)
      ·
        refine ⟨22566225255127745810069933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 15044150170085163873379955 22566225255127745810069933)
        ·
          refine ⟨8462334470672904678776225, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22566225255127745810069933 8462334470672904678776225)
          ·
            refine ⟨6346750853004678509082169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8462334470672904678776225 6346750853004678509082169)
            ·
              refine ⟨4760063139753508881811627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 6346750853004678509082169 4760063139753508881811627)
              ·
                refine ⟨7140094709630263322717441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760063139753508881811627 7140094709630263322717441)
                ·
                  refine ⟨5355071032222697492038081, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 7140094709630263322717441 5355071032222697492038081)
                  ·
                    refine ⟨4016303274167023119028561, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 5355071032222697492038081 4016303274167023119028561)
                    ·
                      refine ⟨3012227455625267339271421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016303274167023119028561 3012227455625267339271421)
                      ·
                        rfl

theorem cell23_5866292_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 3, 2, 2, 1, 2, 2, 2].length) (baseStart_5866292 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866292 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866292 prefixEnd_5866292 := by exact prefixLift 5866292
  have htrace : WordTrace (prefixWord ++ tailWord_5866292) baseStart_5866292 baseEnd_5866292 := by
    simpa [prefixWord, tailWord_5866292, baseEnd_5866292] using wordTrace_append hprefix tailTrace_5866292
  have hstable : (prefixWord ++ tailWord_5866292).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866292).length < 2 ^ (prefixWord ++ tailWord_5866292).sum := by decide
  have hdescent : baseEnd_5866292 < baseStart_5866292 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866292) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866307 : List Nat := [1, 1, 1, 3, 1, 4, 2, 1, 5, 4]
def baseStart_5866307 : Nat := 118140960795 + 5866307 * 2 ^ 59
def prefixEnd_5866307 : Nat := 4983230072969 + 3 ^ 40 * 5866307 * 2
def baseEnd_5866307 : Nat := 1004078385945028260194617

theorem tailTrace_5866307 : CollatzResearch.WordTrace tailWord_5866307 prefixEnd_5866307 1004078385945028260194617 := by
  unfold tailWord_5866307
  simp only [CollatzResearch.WordTrace]
  refine ⟨213961793958379099316533175, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142641195972252732877688783 213961793958379099316533175)
  ·
    refine ⟨320942690937568648974799763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213961793958379099316533175 320942690937568648974799763)
    ·
      refine ⟨481414036406352973462199645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320942690937568648974799763 481414036406352973462199645)
      ·
        refine ⟨180530263652382365048324867, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 481414036406352973462199645 180530263652382365048324867)
        ·
          refine ⟨270795395478573547572487301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180530263652382365048324867 270795395478573547572487301)
          ·
            refine ⟨50774136652232540169841369, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270795395478573547572487301 50774136652232540169841369)
            ·
              refine ⟨38080602489174405127381027, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50774136652232540169841369 38080602489174405127381027)
              ·
                refine ⟨57120903733761607691071541, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38080602489174405127381027 57120903733761607691071541)
                ·
                  refine ⟨5355084725040150721037957, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57120903733761607691071541 5355084725040150721037957)
                  ·
                    refine ⟨1004078385945028260194617, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355084725040150721037957 1004078385945028260194617)
                    ·
                      rfl

theorem cell23_5866307_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 4, 2, 1, 5, 4].length) (baseStart_5866307 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866307 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866307 prefixEnd_5866307 := by exact prefixLift 5866307
  have htrace : WordTrace (prefixWord ++ tailWord_5866307) baseStart_5866307 baseEnd_5866307 := by
    simpa [prefixWord, tailWord_5866307, baseEnd_5866307] using wordTrace_append hprefix tailTrace_5866307
  have hstable : (prefixWord ++ tailWord_5866307).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866307).length < 2 ^ (prefixWord ++ tailWord_5866307).sum := by decide
  have hdescent : baseEnd_5866307 < baseStart_5866307 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866307) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866320 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 10]
def baseStart_5866320 : Nat := 118140960795 + 5866320 * 2 ^ 59
def prefixEnd_5866320 : Nat := 4983230072969 + 3 ^ 40 * 5866320 * 2
def baseEnd_5866320 : Nat := 334693537009288136635699

theorem tailTrace_5866320 : CollatzResearch.WordTrace tailWord_5866320 prefixEnd_5866320 334693537009288136635699 := by
  unfold tailWord_5866320
  simp only [CollatzResearch.WordTrace]
  refine ⟨106981134053666001268378207, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142641512071554668357837609 106981134053666001268378207)
  ·
    refine ⟨160471701080499001902567311, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106981134053666001268378207 160471701080499001902567311)
    ·
      refine ⟨240707551620748502853850967, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160471701080499001902567311 240707551620748502853850967)
      ·
        refine ⟨361061327431122754280776451, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240707551620748502853850967 361061327431122754280776451)
        ·
          refine ⟨541591991146684131421164677, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361061327431122754280776451 541591991146684131421164677)
          ·
            refine ⟨101548498340003274641468377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 541591991146684131421164677 101548498340003274641468377)
            ·
              refine ⟨76161373755002455981101283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101548498340003274641468377 76161373755002455981101283)
              ·
                refine ⟨114242060632503683971651925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76161373755002455981101283 114242060632503683971651925)
                ·
                  refine ⟨334693537009288136635699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 114242060632503683971651925 334693537009288136635699)
                  ·
                    rfl

theorem cell23_5866320_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 10].length) (baseStart_5866320 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866320 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866320 prefixEnd_5866320 := by exact prefixLift 5866320
  have htrace : WordTrace (prefixWord ++ tailWord_5866320) baseStart_5866320 baseEnd_5866320 := by
    simpa [prefixWord, tailWord_5866320, baseEnd_5866320] using wordTrace_append hprefix tailTrace_5866320
  have hstable : (prefixWord ++ tailWord_5866320).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866320).length < 2 ^ (prefixWord ++ tailWord_5866320).sum := by decide
  have hdescent : baseEnd_5866320 < baseStart_5866320 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866320) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866367 : List Nat := [1, 1, 2, 2, 1, 1, 6, 1, 3, 5]
def baseStart_5866367 : Nat := 118140960795 + 5866367 * 2 ^ 59
def prefixEnd_5866367 : Nat := 4983230072969 + 3 ^ 40 * 5866367 * 2
def baseEnd_5866367 : Nat := 1004088655558118181944525

theorem tailTrace_5866367 : CollatzResearch.WordTrace tailWord_5866367 prefixEnd_5866367 1004088655558118181944525 := by
  unfold tailWord_5866367
  simp only [CollatzResearch.WordTrace]
  refine ⟨213963982338161729563717355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142642654892107819709144903 213963982338161729563717355)
  ·
    refine ⟨320945973507242594345576033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213963982338161729563717355 320945973507242594345576033)
    ·
      refine ⟨240709480130431945759182025, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320945973507242594345576033 240709480130431945759182025)
      ·
        refine ⟨180532110097823959319386519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240709480130431945759182025 180532110097823959319386519)
        ·
          refine ⟨270798165146735938979079779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180532110097823959319386519 270798165146735938979079779)
          ·
            refine ⟨406197247720103908468619669, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 270798165146735938979079779 406197247720103908468619669)
            ·
              refine ⟨19040495986879870709466547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 406197247720103908468619669 19040495986879870709466547)
              ·
                refine ⟨28560743980319806064199821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19040495986879870709466547 28560743980319806064199821)
                ·
                  refine ⟨10710278992619927274074933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 28560743980319806064199821 10710278992619927274074933)
                  ·
                    refine ⟨1004088655558118181944525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10710278992619927274074933 1004088655558118181944525)
                    ·
                      rfl

theorem cell23_5866367_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 6, 1, 3, 5].length) (baseStart_5866367 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866367 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866367 prefixEnd_5866367 := by exact prefixLift 5866367
  have htrace : WordTrace (prefixWord ++ tailWord_5866367) baseStart_5866367 baseEnd_5866367 := by
    simpa [prefixWord, tailWord_5866367, baseEnd_5866367] using wordTrace_append hprefix tailTrace_5866367
  have hstable : (prefixWord ++ tailWord_5866367).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866367).length < 2 ^ (prefixWord ++ tailWord_5866367).sum := by decide
  have hdescent : baseEnd_5866367 < baseStart_5866367 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866367) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866387 : List Nat := [1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 4]
def baseStart_5866387 : Nat := 118140960795 + 5866387 * 2 ^ 59
def prefixEnd_5866387 : Nat := 4983230072969 + 3 ^ 40 * 5866387 * 2
def baseEnd_5866387 : Nat := 3012276236287444467583483

theorem tailTrace_5866387 : CollatzResearch.WordTrace tailWord_5866387 prefixEnd_5866387 3012276236287444467583483 := by
  unfold tailWord_5866387
  simp only [CollatzResearch.WordTrace]
  refine ⟨213964711798089272979445415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142643141198726181986296943 213964711798089272979445415)
  ·
    refine ⟨320947067697133909469168123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213964711798089272979445415 320947067697133909469168123)
    ·
      refine ⟨481420601545700864203752185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320947067697133909469168123 481420601545700864203752185)
      ·
        refine ⟨361065451159275648152814139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481420601545700864203752185 361065451159275648152814139)
        ·
          refine ⟨541598176738913472229221209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361065451159275648152814139 541598176738913472229221209)
          ·
            refine ⟨406198632554185104171915907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 541598176738913472229221209 406198632554185104171915907)
            ·
              refine ⟨609297948831277656257873861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 406198632554185104171915907 609297948831277656257873861)
              ·
                refine ⟨114243365405864560548351349, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 609297948831277656257873861 114243365405864560548351349)
                ·
                  refine ⟨10710315506799802551407939, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 114243365405864560548351349 10710315506799802551407939)
                  ·
                    refine ⟨16065473260199703827111909, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10710315506799802551407939 16065473260199703827111909)
                    ·
                      refine ⟨3012276236287444467583483, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16065473260199703827111909 3012276236287444467583483)
                      ·
                        rfl

theorem cell23_5866387_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 4, 5, 1, 4].length) (baseStart_5866387 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866387 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866387 prefixEnd_5866387 := by exact prefixLift 5866387
  have htrace : WordTrace (prefixWord ++ tailWord_5866387) baseStart_5866387 baseEnd_5866387 := by
    simpa [prefixWord, tailWord_5866387, baseEnd_5866387] using wordTrace_append hprefix tailTrace_5866387
  have hstable : (prefixWord ++ tailWord_5866387).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866387).length < 2 ^ (prefixWord ++ tailWord_5866387).sum := by decide
  have hdescent : baseEnd_5866387 < baseStart_5866387 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866387) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866421 : List Nat := [1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 4]
def baseStart_5866421 : Nat := 118140960795 + 5866421 * 2 ^ 59
def prefixEnd_5866421 : Nat := 4983230072969 + 3 ^ 40 * 5866421 * 2
def baseEnd_5866421 : Nat := 3012293694629697334558327

theorem tailTrace_5866421 : CollatzResearch.WordTrace tailWord_5866421 prefixEnd_5866421 3012293694629697334558327 := by
  unfold tailWord_5866421
  simp only [CollatzResearch.WordTrace]
  refine ⟨213965951879966096786183117, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142643967919977397857455411 213965951879966096786183117)
  ·
    refine ⟨80237231954987286294818669, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213965951879966096786183117 80237231954987286294818669)
    ·
      refine ⟨30088961983120232360557001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 80237231954987286294818669 30088961983120232360557001)
      ·
        refine ⟨22566721487340174270417751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 30088961983120232360557001 22566721487340174270417751)
        ·
          refine ⟨33850082231010261405626627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 22566721487340174270417751 33850082231010261405626627)
          ·
            refine ⟨50775123346515392108439941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 33850082231010261405626627 50775123346515392108439941)
            ·
              refine ⟨9520335627471636020332489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50775123346515392108439941 9520335627471636020332489)
              ·
                refine ⟨7140251720603727015249367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9520335627471636020332489 7140251720603727015249367)
                ·
                  refine ⟨10710377580905590522874051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7140251720603727015249367 10710377580905590522874051)
                  ·
                    refine ⟨16065566371358385784311077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10710377580905590522874051 16065566371358385784311077)
                    ·
                      refine ⟨3012293694629697334558327, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16065566371358385784311077 3012293694629697334558327)
                      ·
                        rfl

theorem cell23_5866421_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 1, 4, 2, 1, 1, 4].length) (baseStart_5866421 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866421 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866421 prefixEnd_5866421 := by exact prefixLift 5866421
  have htrace : WordTrace (prefixWord ++ tailWord_5866421) baseStart_5866421 baseEnd_5866421 := by
    simpa [prefixWord, tailWord_5866421, baseEnd_5866421] using wordTrace_append hprefix tailTrace_5866421
  have hstable : (prefixWord ++ tailWord_5866421).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866421).length < 2 ^ (prefixWord ++ tailWord_5866421).sum := by decide
  have hdescent : baseEnd_5866421 < baseStart_5866421 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866421) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866464 : List Nat := [2, 1, 1, 3, 1, 1, 1, 1, 1, 9, 2]
def baseStart_5866464 : Nat := 118140960795 + 5866464 * 2 ^ 59
def prefixEnd_5866464 : Nat := 4983230072969 + 3 ^ 40 * 5866464 * 2
def baseEnd_5866464 : Nat := 3012315774297840666320629

theorem tailTrace_5866464 : CollatzResearch.WordTrace tailWord_5866464 prefixEnd_5866464 3012315774297840666320629 := by
  unfold tailWord_5866464
  simp only [CollatzResearch.WordTrace]
  refine ⟨106983760109405157564999223, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142645013479206876753332297 106983760109405157564999223)
  ·
    refine ⟨160475640164107736347498835, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106983760109405157564999223 160475640164107736347498835)
    ·
      refine ⟨240713460246161604521248253, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160475640164107736347498835 240713460246161604521248253)
      ·
        refine ⟨90267547592310601695468095, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 240713460246161604521248253 90267547592310601695468095)
        ·
          refine ⟨135401321388465902543202143, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90267547592310601695468095 135401321388465902543202143)
          ·
            refine ⟨203101982082698853814803215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 135401321388465902543202143 203101982082698853814803215)
            ·
              refine ⟨304652973124048280722204823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203101982082698853814803215 304652973124048280722204823)
              ·
                refine ⟨456979459686072421083307235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 304652973124048280722204823 456979459686072421083307235)
                ·
                  refine ⟨685469189529108631624960853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 456979459686072421083307235 685469189529108631624960853)
                  ·
                    refine ⟨4016421032397120888427505, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 685469189529108631624960853 4016421032397120888427505)
                    ·
                      refine ⟨3012315774297840666320629, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016421032397120888427505 3012315774297840666320629)
                      ·
                        rfl

theorem cell23_5866464_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 9, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 1, 1, 1, 1, 1, 9, 2].length) (baseStart_5866464 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866464 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866464 prefixEnd_5866464 := by exact prefixLift 5866464
  have htrace : WordTrace (prefixWord ++ tailWord_5866464) baseStart_5866464 baseEnd_5866464 := by
    simpa [prefixWord, tailWord_5866464, baseEnd_5866464] using wordTrace_append hprefix tailTrace_5866464
  have hstable : (prefixWord ++ tailWord_5866464).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866464).length < 2 ^ (prefixWord ++ tailWord_5866464).sum := by decide
  have hdescent : baseEnd_5866464 < baseStart_5866464 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866464) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866544 : List Nat := [2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3]
def baseStart_5866544 : Nat := 118140960795 + 5866544 * 2 ^ 59
def prefixEnd_5866544 : Nat := 4983230072969 + 3 ^ 40 * 5866544 * 2
def baseEnd_5866544 : Nat := 3012356852750200353320261

theorem tailTrace_5866544 : CollatzResearch.WordTrace tailWord_5866544 prefixEnd_5866544 3012356852750200353320261 := by
  unfold tailWord_5866544
  simp only [CollatzResearch.WordTrace]
  refine ⟨106985219029260244396455343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142646958705680325861940457 106985219029260244396455343)
  ·
    refine ⟨160477828543890366594683015, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106985219029260244396455343 160477828543890366594683015)
    ·
      refine ⟨240716742815835549892024523, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160477828543890366594683015 240716742815835549892024523)
      ·
        refine ⟨361075114223753324838036785, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240716742815835549892024523 361075114223753324838036785)
        ·
          refine ⟨270806335667814993628527589, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361075114223753324838036785 270806335667814993628527589)
          ·
            refine ⟨50776187937715311305348923, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 270806335667814993628527589 50776187937715311305348923)
            ·
              refine ⟨76164281906572966958023385, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50776187937715311305348923 76164281906572966958023385)
              ·
                refine ⟨57123211429929725218517539, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76164281906572966958023385 57123211429929725218517539)
                ·
                  refine ⟨85684817144894587827776309, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57123211429929725218517539 85684817144894587827776309)
                  ·
                    refine ⟨8032951607333867608854029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 85684817144894587827776309 8032951607333867608854029)
                    ·
                      refine ⟨3012356852750200353320261, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8032951607333867608854029 3012356852750200353320261)
                      ·
                        rfl

theorem cell23_5866544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 4, 1, 2, 1, 5, 3].length) (baseStart_5866544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866544 prefixEnd_5866544 := by exact prefixLift 5866544
  have htrace : WordTrace (prefixWord ++ tailWord_5866544) baseStart_5866544 baseEnd_5866544 := by
    simpa [prefixWord, tailWord_5866544, baseEnd_5866544] using wordTrace_append hprefix tailTrace_5866544
  have hstable : (prefixWord ++ tailWord_5866544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866544).length < 2 ^ (prefixWord ++ tailWord_5866544).sum := by decide
  have hdescent : baseEnd_5866544 < baseStart_5866544 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866574 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7]
def baseStart_5866574 : Nat := 118140960795 + 5866574 * 2 ^ 59
def prefixEnd_5866574 : Nat := 4983230072969 + 3 ^ 40 * 5866574 * 2
def baseEnd_5866574 : Nat := 3012372257169835235945123

theorem tailTrace_5866574 : CollatzResearch.WordTrace tailWord_5866574 prefixEnd_5866574 3012372257169835235945123 := by
  unfold tailWord_5866574
  simp only [CollatzResearch.WordTrace]
  refine ⟨26746441531051475489562847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142647688165607869277668517 26746441531051475489562847)
  ·
    refine ⟨40119662296577213234344271, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26746441531051475489562847 40119662296577213234344271)
    ·
      refine ⟨60179493444865819851516407, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40119662296577213234344271 60179493444865819851516407)
      ·
        refine ⟨90269240167298729777274611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60179493444865819851516407 90269240167298729777274611)
        ·
          refine ⟨135403860250948094665911917, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90269240167298729777274611 135403860250948094665911917)
          ·
            refine ⟨50776447594105535499716969, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135403860250948094665911917 50776447594105535499716969)
            ·
              refine ⟨38082335695579151624787727, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50776447594105535499716969 38082335695579151624787727)
              ·
                refine ⟨57123503543368727437181591, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 38082335695579151624787727 57123503543368727437181591)
                ·
                  refine ⟨85685255315053091155772387, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 57123503543368727437181591 85685255315053091155772387)
                  ·
                    refine ⟨128527882972579636733658581, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85685255315053091155772387 128527882972579636733658581)
                    ·
                      refine ⟨3012372257169835235945123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128527882972579636733658581 3012372257169835235945123)
                      ·
                        rfl

theorem cell23_5866574_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 1, 1, 7].length) (baseStart_5866574 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866574 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866574 prefixEnd_5866574 := by exact prefixLift 5866574
  have htrace : WordTrace (prefixWord ++ tailWord_5866574) baseStart_5866574 baseEnd_5866574 := by
    simpa [prefixWord, tailWord_5866574, baseEnd_5866574] using wordTrace_append hprefix tailTrace_5866574
  have hstable : (prefixWord ++ tailWord_5866574).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866574).length < 2 ^ (prefixWord ++ tailWord_5866574).sum := by decide
  have hdescent : baseEnd_5866574 < baseStart_5866574 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866574) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866584 : List Nat := [2, 1, 2, 2, 1, 3, 1, 1, 3, 3, 4]
def baseStart_5866584 : Nat := 118140960795 + 5866584 * 2 ^ 59
def prefixEnd_5866584 : Nat := 4983230072969 + 3 ^ 40 * 5866584 * 2
def baseEnd_5866584 : Nat := 3012377391976380196820077

theorem tailTrace_5866584 : CollatzResearch.WordTrace tailWord_5866584 prefixEnd_5866584 3012377391976380196820077 := by
  unfold tailWord_5866584
  simp only [CollatzResearch.WordTrace]
  refine ⟨106985948489187787812183403, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142647931318917050416244537 106985948489187787812183403)
  ·
    refine ⟨160478922733781681718275105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106985948489187787812183403 160478922733781681718275105)
    ·
      refine ⟨120359192050336261288706329, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160478922733781681718275105 120359192050336261288706329)
      ·
        refine ⟨90269394037752195966529747, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120359192050336261288706329 90269394037752195966529747)
        ·
          refine ⟨135404091056628293949794621, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90269394037752195966529747 135404091056628293949794621)
          ·
            refine ⟨50776534146235610231172983, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135404091056628293949794621 50776534146235610231172983)
            ·
              refine ⟨76164801219353415346759475, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 50776534146235610231172983 76164801219353415346759475)
              ·
                refine ⟨114247201829030123020139213, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 76164801219353415346759475 114247201829030123020139213)
                ·
                  refine ⟨42842700685886296132552205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 114247201829030123020139213 42842700685886296132552205)
                  ·
                    refine ⟨16066012757207361049707077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 42842700685886296132552205 16066012757207361049707077)
                    ·
                      refine ⟨3012377391976380196820077, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16066012757207361049707077 3012377391976380196820077)
                      ·
                        rfl

theorem cell23_5866584_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 1, 3, 1, 1, 3, 3, 4].length) (baseStart_5866584 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866584 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866584 prefixEnd_5866584 := by exact prefixLift 5866584
  have htrace : WordTrace (prefixWord ++ tailWord_5866584) baseStart_5866584 baseEnd_5866584 := by
    simpa [prefixWord, tailWord_5866584, baseEnd_5866584] using wordTrace_append hprefix tailTrace_5866584
  have hstable : (prefixWord ++ tailWord_5866584).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866584).length < 2 ^ (prefixWord ++ tailWord_5866584).sum := by decide
  have hdescent : baseEnd_5866584 < baseStart_5866584 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866584) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866624 : List Nat := [2, 1, 1, 2, 1, 3, 4, 1, 8]
def baseStart_5866624 : Nat := 118140960795 + 5866624 * 2 ^ 59
def prefixEnd_5866624 : Nat := 4983230072969 + 3 ^ 40 * 5866624 * 2
def baseEnd_5866624 : Nat := 334710881244728893368877

theorem tailTrace_5866624 : CollatzResearch.WordTrace tailWord_5866624 prefixEnd_5866624 334710881244728893368877 := by
  unfold tailWord_5866624
  simp only [CollatzResearch.WordTrace]
  refine ⟨106986677949115331227911463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142648903932153774970548617 106986677949115331227911463)
  ·
    refine ⟨160480016923672996841867195, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106986677949115331227911463 160480016923672996841867195)
    ·
      refine ⟨240720025385509495262800793, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160480016923672996841867195 240720025385509495262800793)
      ·
        refine ⟨180540019039132121447100595, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240720025385509495262800793 180540019039132121447100595)
        ·
          refine ⟨270810028558698182170650893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180540019039132121447100595 270810028558698182170650893)
          ·
            refine ⟨101553760709511818313994085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270810028558698182170650893 101553760709511818313994085)
            ·
              refine ⟨19041330133033465933873891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 101553760709511818313994085 19041330133033465933873891)
              ·
                refine ⟨28561995199550198900810837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19041330133033465933873891 28561995199550198900810837)
                ·
                  refine ⟨334710881244728893368877, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 28561995199550198900810837 334710881244728893368877)
                  ·
                    rfl

theorem cell23_5866624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 3, 4, 1, 8].length) (baseStart_5866624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866624 prefixEnd_5866624 := by exact prefixLift 5866624
  have htrace : WordTrace (prefixWord ++ tailWord_5866624) baseStart_5866624 baseEnd_5866624 := by
    simpa [prefixWord, tailWord_5866624, baseEnd_5866624] using wordTrace_append hprefix tailTrace_5866624
  have hstable : (prefixWord ++ tailWord_5866624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866624).length < 2 ^ (prefixWord ++ tailWord_5866624).sum := by decide
  have hdescent : baseEnd_5866624 < baseStart_5866624 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866628 : List Nat := [2, 3, 2, 1, 2, 2, 3, 1, 3, 4]
def baseStart_5866628 : Nat := 118140960795 + 5866628 * 2 ^ 59
def prefixEnd_5866628 : Nat := 4983230072969 + 3 ^ 40 * 5866628 * 2
def baseEnd_5866628 : Nat := 1004133328375059341556625

theorem tailTrace_5866628 : CollatzResearch.WordTrace tailWord_5866628 prefixEnd_5866628 1004133328375059341556625 := by
  unfold tailWord_5866628
  simp only [CollatzResearch.WordTrace]
  refine ⟨106986750895108085569484269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142649001193477447425979025 106986750895108085569484269)
  ·
    refine ⟨40120031585665532088556601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 106986750895108085569484269 40120031585665532088556601)
    ·
      refine ⟨30090023689249149066417451, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40120031585665532088556601 30090023689249149066417451)
      ·
        refine ⟨45135035533873723599626177, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30090023689249149066417451 45135035533873723599626177)
        ·
          refine ⟨33851276650405292699719633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45135035533873723599626177 33851276650405292699719633)
          ·
            refine ⟨25388457487803969524789725, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 33851276650405292699719633 25388457487803969524789725)
            ·
              refine ⟨9520671557926488571796147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 25388457487803969524789725 9520671557926488571796147)
              ·
                refine ⟨14281007336889732857694221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9520671557926488571796147 14281007336889732857694221)
                ·
                  refine ⟨5355377751333649821635333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14281007336889732857694221 5355377751333649821635333)
                  ·
                    refine ⟨1004133328375059341556625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355377751333649821635333 1004133328375059341556625)
                    ·
                      rfl

theorem cell23_5866628_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 2, 1, 2, 2, 3, 1, 3, 4].length) (baseStart_5866628 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866628 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866628 prefixEnd_5866628 := by exact prefixLift 5866628
  have htrace : WordTrace (prefixWord ++ tailWord_5866628) baseStart_5866628 baseEnd_5866628 := by
    simpa [prefixWord, tailWord_5866628, baseEnd_5866628] using wordTrace_append hprefix tailTrace_5866628
  have hstable : (prefixWord ++ tailWord_5866628).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866628).length < 2 ^ (prefixWord ++ tailWord_5866628).sum := by decide
  have hdescent : baseEnd_5866628 < baseStart_5866628 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866628) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866655 : List Nat := [1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 3]
def baseStart_5866655 : Nat := 118140960795 + 5866655 * 2 ^ 59
def prefixEnd_5866655 : Nat := 4983230072969 + 3 ^ 40 * 5866655 * 2
def baseEnd_5866655 : Nat := 3012413849102849419032251

theorem tailTrace_5866655 : CollatzResearch.WordTrace tailWord_5866655 prefixEnd_5866655 3012413849102849419032251 := by
  unfold tailWord_5866655
  simp only [CollatzResearch.WordTrace]
  refine ⟨213974486561118354750201419, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142649657707412236500134279 213974486561118354750201419)
  ·
    refine ⟨320961729841677532125302129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213974486561118354750201419 320961729841677532125302129)
    ·
      refine ⟨240721297381258149093976597, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320961729841677532125302129 240721297381258149093976597)
      ·
        refine ⟨11283810814746475738780153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 240721297381258149093976597 11283810814746475738780153)
        ·
          refine ⟨8462858111059856804085115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 11283810814746475738780153 8462858111059856804085115)
          ·
            refine ⟨12694287166589785206127673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462858111059856804085115 12694287166589785206127673)
            ·
              refine ⟨9520715374942338904595755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 12694287166589785206127673 9520715374942338904595755)
              ·
                refine ⟨14281073062413508356893633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9520715374942338904595755 14281073062413508356893633)
                ·
                  refine ⟨10710804796810131267670225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14281073062413508356893633 10710804796810131267670225)
                  ·
                    refine ⟨8033103597607598450752669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 10710804796810131267670225 8033103597607598450752669)
                    ·
                      refine ⟨3012413849102849419032251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8033103597607598450752669 3012413849102849419032251)
                      ·
                        rfl

theorem cell23_5866655_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 2, 1, 2, 1, 2, 2, 3].length) (baseStart_5866655 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866655 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866655 prefixEnd_5866655 := by exact prefixLift 5866655
  have htrace : WordTrace (prefixWord ++ tailWord_5866655) baseStart_5866655 baseEnd_5866655 := by
    simpa [prefixWord, tailWord_5866655, baseEnd_5866655] using wordTrace_append hprefix tailTrace_5866655
  have hstable : (prefixWord ++ tailWord_5866655).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866655).length < 2 ^ (prefixWord ++ tailWord_5866655).sum := by decide
  have hdescent : baseEnd_5866655 < baseStart_5866655 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866655) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866671 : List Nat := [1, 1, 2, 1, 2, 3, 2, 5, 1, 5]
def baseStart_5866671 : Nat := 118140960795 + 5866671 * 2 ^ 59
def prefixEnd_5866671 : Nat := 4983230072969 + 3 ^ 40 * 5866671 * 2
def baseEnd_5866671 : Nat := 1004140688264440452144059

theorem tailTrace_5866671 : CollatzResearch.WordTrace tailWord_5866671 prefixEnd_5866671 1004140688264440452144059 := by
  unfold tailWord_5866671
  simp only [CollatzResearch.WordTrace]
  refine ⟨213975070129060389482783867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142650046752706926321855911 213975070129060389482783867)
  ·
    refine ⟨320962605193590584224175801, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213975070129060389482783867 320962605193590584224175801)
    ·
      refine ⟨240721953895192938168131851, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 320962605193590584224175801 240721953895192938168131851)
      ·
        refine ⟨361082930842789407252197777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240721953895192938168131851 361082930842789407252197777)
        ·
          refine ⟨270812198132092055439148333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361082930842789407252197777 270812198132092055439148333)
          ·
            refine ⟨101554574299534520789680625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270812198132092055439148333 101554574299534520789680625)
            ·
              refine ⟨76165930724650890592260469, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101554574299534520789680625 76165930724650890592260469)
              ·
                refine ⟨7140556005436020993024419, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 76165930724650890592260469 7140556005436020993024419)
                ·
                  refine ⟨10710834008154031489536629, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7140556005436020993024419 10710834008154031489536629)
                  ·
                    refine ⟨1004140688264440452144059, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10710834008154031489536629 1004140688264440452144059)
                    ·
                      rfl

theorem cell23_5866671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 3, 2, 5, 1, 5].length) (baseStart_5866671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866671 prefixEnd_5866671 := by exact prefixLift 5866671
  have htrace : WordTrace (prefixWord ++ tailWord_5866671) baseStart_5866671 baseEnd_5866671 := by
    simpa [prefixWord, tailWord_5866671, baseEnd_5866671] using wordTrace_append hprefix tailTrace_5866671
  have hstable : (prefixWord ++ tailWord_5866671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866671).length < 2 ^ (prefixWord ++ tailWord_5866671).sum := by decide
  have hdescent : baseEnd_5866671 < baseStart_5866671 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866712 : List Nat := [2, 1, 2, 2, 5, 2, 1, 1, 2, 3, 2]
def baseStart_5866712 : Nat := 118140960795 + 5866712 * 2 ^ 59
def prefixEnd_5866712 : Nat := 4983230072969 + 3 ^ 40 * 5866712 * 2
def baseEnd_5866712 : Nat := 3012443117500155696019489

theorem tailTrace_5866712 : CollatzResearch.WordTrace tailWord_5866712 prefixEnd_5866712 3012443117500155696019489 := by
  unfold tailWord_5866712
  simp only [CollatzResearch.WordTrace]
  refine ⟨106988282760955926742513195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142651043681274568990017593 106988282760955926742513195)
  ·
    refine ⟨160482424141433890113769793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106988282760955926742513195 160482424141433890113769793)
    ·
      refine ⟨120361818106075417585327345, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 160482424141433890113769793 120361818106075417585327345)
      ·
        refine ⟨90271363579556563188995509, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120361818106075417585327345 90271363579556563188995509)
        ·
          refine ⟨8462940335583427798968329, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90271363579556563188995509 8462940335583427798968329)
          ·
            refine ⟨6347205251687570849226247, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 8462940335583427798968329 6347205251687570849226247)
            ·
              refine ⟨9520807877531356273839371, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347205251687570849226247 9520807877531356273839371)
              ·
                refine ⟨14281211816297034410759057, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9520807877531356273839371 14281211816297034410759057)
                ·
                  refine ⟨10710908862222775808069293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 14281211816297034410759057 10710908862222775808069293)
                  ·
                    refine ⟨4016590823333540928025985, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10710908862222775808069293 4016590823333540928025985)
                    ·
                      refine ⟨3012443117500155696019489, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016590823333540928025985 3012443117500155696019489)
                      ·
                        rfl

theorem cell23_5866712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 2, 5, 2, 1, 1, 2, 3, 2].length) (baseStart_5866712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866712 prefixEnd_5866712 := by exact prefixLift 5866712
  have htrace : WordTrace (prefixWord ++ tailWord_5866712) baseStart_5866712 baseEnd_5866712 := by
    simpa [prefixWord, tailWord_5866712, baseEnd_5866712] using wordTrace_append hprefix tailTrace_5866712
  have hstable : (prefixWord ++ tailWord_5866712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866712).length < 2 ^ (prefixWord ++ tailWord_5866712).sum := by decide
  have hdescent : baseEnd_5866712 < baseStart_5866712 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866725 : List Nat := [1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 4]
def baseStart_5866725 : Nat := 118140960795 + 5866725 * 2 ^ 59
def prefixEnd_5866725 : Nat := 4983230072969 + 3 ^ 40 * 5866725 * 2
def baseEnd_5866725 : Nat := 3012449792748664145156929

theorem tailTrace_5866725 : CollatzResearch.WordTrace tailWord_5866725 prefixEnd_5866725 3012449792748664145156929 := by
  unfold tailWord_5866725
  simp only [CollatzResearch.WordTrace]
  refine ⟨213977039670864756705249629, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142651359780576504470166419 213977039670864756705249629)
  ·
    refine ⟨80241389876574283764468611, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213977039670864756705249629 80241389876574283764468611)
    ·
      refine ⟨120362084814861425646702917, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80241389876574283764468611 120362084814861425646702917)
      ·
        refine ⟨22567890902786517308756797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 120362084814861425646702917 22567890902786517308756797)
        ·
          refine ⟨8462959088544943990783799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 22567890902786517308756797 8462959088544943990783799)
          ·
            refine ⟨12694438632817415986175699, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8462959088544943990783799 12694438632817415986175699)
            ·
              refine ⟨19041657949226123979263549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12694438632817415986175699 19041657949226123979263549)
              ·
                refine ⟨7140621730959796492223831, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 19041657949226123979263549 7140621730959796492223831)
                ·
                  refine ⟨10710932596439694738335747, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7140621730959796492223831 10710932596439694738335747)
                  ·
                    refine ⟨16066398894659542107503621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10710932596439694738335747 16066398894659542107503621)
                    ·
                      refine ⟨3012449792748664145156929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16066398894659542107503621 3012449792748664145156929)
                      ·
                        rfl

theorem cell23_5866725_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 3, 1, 1, 3, 1, 1, 4].length) (baseStart_5866725 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866725 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866725 prefixEnd_5866725 := by exact prefixLift 5866725
  have htrace : WordTrace (prefixWord ++ tailWord_5866725) baseStart_5866725 baseEnd_5866725 := by
    simpa [prefixWord, tailWord_5866725, baseEnd_5866725] using wordTrace_append hprefix tailTrace_5866725
  have hstable : (prefixWord ++ tailWord_5866725).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866725).length < 2 ^ (prefixWord ++ tailWord_5866725).sum := by decide
  have hdescent : baseEnd_5866725 < baseStart_5866725 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866725) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866768 : List Nat := [2, 1, 1, 1, 1, 1, 1, 1, 9, 3, 2]
def baseStart_5866768 : Nat := 118140960795 + 5866768 * 2 ^ 59
def prefixEnd_5866768 : Nat := 4983230072969 + 3 ^ 40 * 5866768 * 2
def baseEnd_5866768 : Nat := 3012471872416807476919231

theorem tailTrace_5866768 : CollatzResearch.WordTrace tailWord_5866768 prefixEnd_5866768 3012471872416807476919231 := by
  unfold tailWord_5866768
  simp only [CollatzResearch.WordTrace]
  refine ⟨106989304004854487524532479, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142652405339805983366043305 106989304004854487524532479)
  ·
    refine ⟨160483956007281731286798719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106989304004854487524532479 160483956007281731286798719)
    ·
      refine ⟨240725934010922596930198079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160483956007281731286798719 240725934010922596930198079)
      ·
        refine ⟨361088901016383895395297119, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240725934010922596930198079 361088901016383895395297119)
        ·
          refine ⟨541633351524575843092945679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 361088901016383895395297119 541633351524575843092945679)
          ·
            refine ⟨812450027286863764639418519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 541633351524575843092945679 812450027286863764639418519)
            ·
              refine ⟨1218675040930295646959127779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812450027286863764639418519 1218675040930295646959127779)
              ·
                refine ⟨1828012561395443470438691669, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218675040930295646959127779 1828012561395443470438691669)
                ·
                  refine ⟨10711011101926426584601709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 9 1828012561395443470438691669 10711011101926426584601709)
                  ·
                    refine ⟨4016629163222409969225641, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 10711011101926426584601709 4016629163222409969225641)
                    ·
                      refine ⟨3012471872416807476919231, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016629163222409969225641 3012471872416807476919231)
                      ·
                        rfl

theorem cell23_5866768_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 9, 3, 2].length) (baseStart_5866768 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866768 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866768 prefixEnd_5866768 := by exact prefixLift 5866768
  have htrace : WordTrace (prefixWord ++ tailWord_5866768) baseStart_5866768 baseEnd_5866768 := by
    simpa [prefixWord, tailWord_5866768, baseEnd_5866768] using wordTrace_append hprefix tailTrace_5866768
  have hstable : (prefixWord ++ tailWord_5866768).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866768).length < 2 ^ (prefixWord ++ tailWord_5866768).sum := by decide
  have hdescent : baseEnd_5866768 < baseStart_5866768 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866768) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866782 : List Nat := [4, 3, 2, 1, 3, 1, 9]
def baseStart_5866782 : Nat := 118140960795 + 5866782 * 2 ^ 59
def prefixEnd_5866782 : Nat := 4983230072969 + 3 ^ 40 * 5866782 * 2
def baseEnd_5866782 : Nat := 37191099520320622495607

theorem tailTrace_5866782 : CollatzResearch.WordTrace tailWord_5866782 prefixEnd_5866782 37191099520320622495607 := by
  unfold tailWord_5866782
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747389828957281930009325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142652745754438836960049733 26747389828957281930009325)
  ·
    refine ⟨10030271185858980723753497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 26747389828957281930009325 10030271185858980723753497)
    ·
      refine ⟨7522703389394235542815123, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 10030271185858980723753497 7522703389394235542815123)
      ·
        refine ⟨11284055084091353314222685, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 7522703389394235542815123 11284055084091353314222685)
        ·
          refine ⟨4231520656534257492833507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 11284055084091353314222685 4231520656534257492833507)
          ·
            refine ⟨6347280984801386239250261, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4231520656534257492833507 6347280984801386239250261)
            ·
              refine ⟨37191099520320622495607, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 6347280984801386239250261 37191099520320622495607)
              ·
                rfl

theorem cell23_5866782_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 2, 1, 3, 1, 9].length) (baseStart_5866782 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866782 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866782 prefixEnd_5866782 := by exact prefixLift 5866782
  have htrace : WordTrace (prefixWord ++ tailWord_5866782) baseStart_5866782 baseEnd_5866782 := by
    simpa [prefixWord, tailWord_5866782, baseEnd_5866782] using wordTrace_append hprefix tailTrace_5866782
  have hstable : (prefixWord ++ tailWord_5866782).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866782).length < 2 ^ (prefixWord ++ tailWord_5866782).sum := by decide
  have hdescent : baseEnd_5866782 < baseStart_5866782 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866782) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866811 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4]
def baseStart_5866811 : Nat := 118140960795 + 5866811 * 2 ^ 59
def prefixEnd_5866811 : Nat := 4983230072969 + 3 ^ 40 * 5866811 * 2
def baseEnd_5866811 : Nat := 3012493952084950808681533

theorem tailTrace_5866811 : CollatzResearch.WordTrace tailWord_5866811 prefixEnd_5866811 3012493952084950808681533 := by
  unfold tailWord_5866811
  simp only [CollatzResearch.WordTrace]
  refine ⟨213980176348553193392880287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142653450899035462261920191 213980176348553193392880287)
  ·
    refine ⟨320970264522829790089320431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213980176348553193392880287 320970264522829790089320431)
    ·
      refine ⟨481455396784244685133980647, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320970264522829790089320431 481455396784244685133980647)
      ·
        refine ⟨722183095176367027700970971, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481455396784244685133980647 722183095176367027700970971)
        ·
          refine ⟨1083274642764550541551456457, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 722183095176367027700970971 1083274642764550541551456457)
          ·
            refine ⟨812455982073412906163592343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1083274642764550541551456457 812455982073412906163592343)
            ·
              refine ⟨1218683973110119359245388515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 812455982073412906163592343 1218683973110119359245388515)
              ·
                refine ⟨1828025959665179038868082773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1218683973110119359245388515 1828025959665179038868082773)
                ·
                  refine ⟨21422179214826316861735345, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 1828025959665179038868082773 21422179214826316861735345)
                  ·
                    refine ⟨16066634411119737646301509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21422179214826316861735345 16066634411119737646301509)
                    ·
                      refine ⟨3012493952084950808681533, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16066634411119737646301509 3012493952084950808681533)
                      ·
                        rfl

theorem cell23_5866811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 8, 2, 4].length) (baseStart_5866811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866811 prefixEnd_5866811 := by exact prefixLift 5866811
  have htrace : WordTrace (prefixWord ++ tailWord_5866811) baseStart_5866811 baseEnd_5866811 := by
    simpa [prefixWord, tailWord_5866811, baseEnd_5866811] using wordTrace_append hprefix tailTrace_5866811
  have hstable : (prefixWord ++ tailWord_5866811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866811).length < 2 ^ (prefixWord ++ tailWord_5866811).sum := by decide
  have hdescent : baseEnd_5866811 < baseStart_5866811 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866821 : List Nat := [1, 3, 1, 1, 1, 2, 1, 6, 7]
def baseStart_5866821 : Nat := 118140960795 + 5866821 * 2 ^ 59
def prefixEnd_5866821 : Nat := 4983230072969 + 3 ^ 40 * 5866821 * 2
def baseEnd_5866821 : Nat := 334722120765721752172943

theorem tailTrace_5866821 : CollatzResearch.WordTrace tailWord_5866821 prefixEnd_5866821 334722120765721752172943 := by
  unfold tailWord_5866821
  simp only [CollatzResearch.WordTrace]
  refine ⟨213980541078516965100744317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142653694052344643400496211 213980541078516965100744317)
  ·
    refine ⟨80242702904443861912779119, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 213980541078516965100744317 80242702904443861912779119)
    ·
      refine ⟨120364054356665792869168679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 80242702904443861912779119 120364054356665792869168679)
      ·
        refine ⟨180546081534998689303753019, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 120364054356665792869168679 180546081534998689303753019)
        ·
          refine ⟨270819122302498033955629529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180546081534998689303753019 270819122302498033955629529)
          ·
            refine ⟨203114341726873525466722147, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270819122302498033955629529 203114341726873525466722147)
            ·
              refine ⟨304671512590310288200083221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 203114341726873525466722147 304671512590310288200083221)
              ·
                refine ⟨14281477152670794759378901, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 304671512590310288200083221 14281477152670794759378901)
                ·
                  refine ⟨334722120765721752172943, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 14281477152670794759378901 334722120765721752172943)
                  ·
                    rfl

theorem cell23_5866821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 2, 1, 6, 7].length) (baseStart_5866821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866821 prefixEnd_5866821 := by exact prefixLift 5866821
  have htrace : WordTrace (prefixWord ++ tailWord_5866821) baseStart_5866821 baseEnd_5866821 := by
    simpa [prefixWord, tailWord_5866821, baseEnd_5866821] using wordTrace_append hprefix tailTrace_5866821
  have hstable : (prefixWord ++ tailWord_5866821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866821).length < 2 ^ (prefixWord ++ tailWord_5866821).sum := by decide
  have hdescent : baseEnd_5866821 < baseStart_5866821 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866862 : List Nat := [4, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4]
def baseStart_5866862 : Nat := 118140960795 + 5866862 * 2 ^ 59
def prefixEnd_5866862 : Nat := 4983230072969 + 3 ^ 40 * 5866862 * 2
def baseEnd_5866862 : Nat := 3012520139598330109143799

theorem tailTrace_5866862 : CollatzResearch.WordTrace tailWord_5866862 prefixEnd_5866862 3012520139598330109143799 := by
  unfold tailWord_5866862
  simp only [CollatzResearch.WordTrace]
  refine ⟨26747754558921053637873355, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 142654690980912286068657893 26747754558921053637873355)
  ·
    refine ⟨40121631838381580456810033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 26747754558921053637873355 40121631838381580456810033)
    ·
      refine ⟨30091223878786185342607525, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40121631838381580456810033 30091223878786185342607525)
      ·
        refine ⟨5642104477272409751738911, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 30091223878786185342607525 5642104477272409751738911)
        ·
          refine ⟨8463156715908614627608367, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 5642104477272409751738911 8463156715908614627608367)
          ·
            refine ⟨12694735073862921941412551, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463156715908614627608367 12694735073862921941412551)
            ·
              refine ⟨19042102610794382912118827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12694735073862921941412551 19042102610794382912118827)
              ·
                refine ⟨28563153916191574368178241, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19042102610794382912118827 28563153916191574368178241)
                ·
                  refine ⟨21422365437143680776133681, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28563153916191574368178241 21422365437143680776133681)
                  ·
                    refine ⟨16066774077857760582100261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 21422365437143680776133681 16066774077857760582100261)
                    ·
                      refine ⟨3012520139598330109143799, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16066774077857760582100261 3012520139598330109143799)
                      ·
                        rfl

theorem cell23_5866862_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 4, 1, 1, 1, 1, 2, 2, 4].length) (baseStart_5866862 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866862 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866862 prefixEnd_5866862 := by exact prefixLift 5866862
  have htrace : WordTrace (prefixWord ++ tailWord_5866862) baseStart_5866862 baseEnd_5866862 := by
    simpa [prefixWord, tailWord_5866862, baseEnd_5866862] using wordTrace_append hprefix tailTrace_5866862
  have hstable : (prefixWord ++ tailWord_5866862).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866862).length < 2 ^ (prefixWord ++ tailWord_5866862).sum := by decide
  have hdescent : baseEnd_5866862 < baseStart_5866862 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866862) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866905 : List Nat := [1, 2, 1, 2, 1, 5, 1, 2, 2, 4, 2]
def baseStart_5866905 : Nat := 118140960795 + 5866905 * 2 ^ 59
def prefixEnd_5866905 : Nat := 4983230072969 + 3 ^ 40 * 5866905 * 2
def baseEnd_5866905 : Nat := 3012542219266473440906101

theorem tailTrace_5866905 : CollatzResearch.WordTrace tailWord_5866905 prefixEnd_5866905 3012542219266473440906101 := by
  unfold tailWord_5866905
  simp only [CollatzResearch.WordTrace]
  refine ⟨213983604810212647446802169, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142655736540141764964534779 213983604810212647446802169)
  ·
    refine ⟨160487703607659485585101627, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213983604810212647446802169 160487703607659485585101627)
    ·
      refine ⟨240731555411489228377652441, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160487703607659485585101627 240731555411489228377652441)
      ·
        refine ⟨180548666558616921283239331, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 240731555411489228377652441 180548666558616921283239331)
        ·
          refine ⟨270822999837925381924858997, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 180548666558616921283239331 270822999837925381924858997)
          ·
            refine ⟨25389656234805504555455531, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 270822999837925381924858997 25389656234805504555455531)
            ·
              refine ⟨38084484352208256833183297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 25389656234805504555455531 38084484352208256833183297)
              ·
                refine ⟨28563363264156192624887473, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38084484352208256833183297 28563363264156192624887473)
                ·
                  refine ⟨21422522448117144468665605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28563363264156192624887473 21422522448117144468665605)
                  ·
                    refine ⟨4016722959021964587874801, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 21422522448117144468665605 4016722959021964587874801)
                    ·
                      refine ⟨3012542219266473440906101, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4016722959021964587874801 3012542219266473440906101)
                      ·
                        rfl

theorem cell23_5866905_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 2, 2, 4, 2].length) (baseStart_5866905 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866905 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866905 prefixEnd_5866905 := by exact prefixLift 5866905
  have htrace : WordTrace (prefixWord ++ tailWord_5866905) baseStart_5866905 baseEnd_5866905 := by
    simpa [prefixWord, tailWord_5866905, baseEnd_5866905] using wordTrace_append hprefix tailTrace_5866905
  have hstable : (prefixWord ++ tailWord_5866905).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866905).length < 2 ^ (prefixWord ++ tailWord_5866905).sum := by decide
  have hdescent : baseEnd_5866905 < baseStart_5866905 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866905) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866915 : List Nat := [1, 1, 1, 4, 1, 3, 4, 1, 3, 4]
def baseStart_5866915 : Nat := 118140960795 + 5866915 * 2 ^ 59
def prefixEnd_5866915 : Nat := 4983230072969 + 3 ^ 40 * 5866915 * 2
def baseEnd_5866915 : Nat := 1004182451357672800593685

theorem tailTrace_5866915 : CollatzResearch.WordTrace tailWord_5866915 prefixEnd_5866915 1004182451357672800593685 := by
  unfold tailWord_5866915
  simp only [CollatzResearch.WordTrace]
  refine ⟨213983969540176419154666199, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142655979693450946103110799 213983969540176419154666199)
  ·
    refine ⟨320975954310264628731999299, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213983969540176419154666199 320975954310264628731999299)
    ·
      refine ⟨481463931465396943097998949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320975954310264628731999299 481463931465396943097998949)
      ·
        refine ⟨90274487149761926830874803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 481463931465396943097998949 90274487149761926830874803)
        ·
          refine ⟨135411730724642890246312205, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90274487149761926830874803 135411730724642890246312205)
          ·
            refine ⟨50779399021741083842367077, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135411730724642890246312205 50779399021741083842367077)
            ·
              refine ⟨9521137316576453220443827, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 50779399021741083842367077 9521137316576453220443827)
              ·
                refine ⟨14281705974864679830665741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 9521137316576453220443827 14281705974864679830665741)
                ·
                  refine ⟨5355639740574254936499653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 14281705974864679830665741 5355639740574254936499653)
                  ·
                    refine ⟨1004182451357672800593685, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 5355639740574254936499653 1004182451357672800593685)
                    ·
                      rfl

theorem cell23_5866915_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 1, 3, 4, 1, 3, 4].length) (baseStart_5866915 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866915 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866915 prefixEnd_5866915 := by exact prefixLift 5866915
  have htrace : WordTrace (prefixWord ++ tailWord_5866915) baseStart_5866915 baseEnd_5866915 := by
    simpa [prefixWord, tailWord_5866915, baseEnd_5866915] using wordTrace_append hprefix tailTrace_5866915
  have hstable : (prefixWord ++ tailWord_5866915).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866915).length < 2 ^ (prefixWord ++ tailWord_5866915).sum := by decide
  have hdescent : baseEnd_5866915 < baseStart_5866915 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866915) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866955 : List Nat := [1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 3]
def baseStart_5866955 : Nat := 118140960795 + 5866955 * 2 ^ 59
def prefixEnd_5866955 : Nat := 4983230072969 + 3 ^ 40 * 5866955 * 2
def baseEnd_5866955 : Nat := 3012567893299198245280871

theorem tailTrace_5866955 : CollatzResearch.WordTrace tailWord_5866955 prefixEnd_5866955 3012567893299198245280871 := by
  unfold tailWord_5866955
  simp only [CollatzResearch.WordTrace]
  refine ⟨213985428460031505986122319, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142656952306687670657414879 213985428460031505986122319)
  ·
    refine ⟨320978142690047258979183479, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213985428460031505986122319 320978142690047258979183479)
    ·
      refine ⟨481467214035070888468775219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320978142690047258979183479 481467214035070888468775219)
      ·
        refine ⟨722200821052606332703162829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 481467214035070888468775219 722200821052606332703162829)
        ·
          refine ⟨270825307894727374763686061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 722200821052606332703162829 270825307894727374763686061)
          ·
            refine ⟨101559490460522765536382273, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 270825307894727374763686061 101559490460522765536382273)
            ·
              refine ⟨76169617845392074152286705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 101559490460522765536382273 76169617845392074152286705)
              ·
                refine ⟨57127213384044055614215029, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 76169617845392074152286705 57127213384044055614215029)
                ·
                  refine ⟨5355676254754130213832659, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 57127213384044055614215029 5355676254754130213832659)
                  ·
                    refine ⟨8033514382131195320748989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5355676254754130213832659 8033514382131195320748989)
                    ·
                      refine ⟨3012567893299198245280871, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8033514382131195320748989 3012567893299198245280871)
                      ·
                        rfl

theorem cell23_5866955_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 3, 2, 2, 5, 1, 3].length) (baseStart_5866955 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866955 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866955 prefixEnd_5866955 := by exact prefixLift 5866955
  have htrace : WordTrace (prefixWord ++ tailWord_5866955) baseStart_5866955 baseEnd_5866955 := by
    simpa [prefixWord, tailWord_5866955, baseEnd_5866955] using wordTrace_append hprefix tailTrace_5866955
  have hstable : (prefixWord ++ tailWord_5866955).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866955).length < 2 ^ (prefixWord ++ tailWord_5866955).sum := by decide
  have hdescent : baseEnd_5866955 < baseStart_5866955 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866955) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866992 : List Nat := [2, 1, 1, 1, 3, 6, 1, 2, 1, 5]
def baseStart_5866992 : Nat := 118140960795 + 5866992 * 2 ^ 59
def prefixEnd_5866992 : Nat := 4983230072969 + 3 ^ 40 * 5866992 * 2
def baseEnd_5866992 : Nat := 1004195630694471533506067

theorem tailTrace_5866992 : CollatzResearch.WordTrace tailWord_5866992 prefixEnd_5866992 1004195630694471533506067 := by
  unfold tailWord_5866992
  simp only [CollatzResearch.WordTrace]
  refine ⟨106993388980448730652609615, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 142657851973931640870146153 106993388980448730652609615)
  ·
    refine ⟨160490083470673095978914423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 106993388980448730652609615 160490083470673095978914423)
    ·
      refine ⟨240735125206009643968371635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 160490083470673095978914423 240735125206009643968371635)
      ·
        refine ⟨361102687809014465952557453, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 240735125206009643968371635 361102687809014465952557453)
        ·
          refine ⟨135413507928380424732209045, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 361102687809014465952557453 135413507928380424732209045)
          ·
            refine ⟨6347508184142832409322299, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 135413507928380424732209045 6347508184142832409322299)
            ·
              refine ⟨9521262276214248613983449, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 6347508184142832409322299 9521262276214248613983449)
              ·
                refine ⟨7140946707160686460487587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 9521262276214248613983449 7140946707160686460487587)
                ·
                  refine ⟨10711420060741029690731381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7140946707160686460487587 10711420060741029690731381)
                  ·
                    refine ⟨1004195630694471533506067, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10711420060741029690731381 1004195630694471533506067)
                    ·
                      rfl

theorem cell23_5866992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 3, 6, 1, 2, 1, 5].length) (baseStart_5866992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866992 prefixEnd_5866992 := by exact prefixLift 5866992
  have htrace : WordTrace (prefixWord ++ tailWord_5866992) baseStart_5866992 baseEnd_5866992 := by
    simpa [prefixWord, tailWord_5866992, baseEnd_5866992] using wordTrace_append hprefix tailTrace_5866992
  have hstable : (prefixWord ++ tailWord_5866992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866992).length < 2 ^ (prefixWord ++ tailWord_5866992).sum := by decide
  have hdescent : baseEnd_5866992 < baseStart_5866992 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5866995 : List Nat := [1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 4]
def baseStart_5866995 : Nat := 118140960795 + 5866995 * 2 ^ 59
def prefixEnd_5866995 : Nat := 4983230072969 + 3 ^ 40 * 5866995 * 2
def baseEnd_5866995 : Nat := 3012588432525378088780687

theorem tailTrace_5866995 : CollatzResearch.WordTrace tailWord_5866995 prefixEnd_5866995 3012588432525378088780687 := by
  unfold tailWord_5866995
  simp only [CollatzResearch.WordTrace]
  refine ⟨213986887379886592817578439, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142657924919924395211718959 213986887379886592817578439)
  ·
    refine ⟨320980331069829889226367659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213986887379886592817578439 320980331069829889226367659)
    ·
      refine ⟨481470496604744833839551489, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 320980331069829889226367659 481470496604744833839551489)
      ·
        refine ⟨361102872453558625379663617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 481470496604744833839551489 361102872453558625379663617)
        ·
          refine ⟨270827154340168969034747713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 361102872453558625379663617 270827154340168969034747713)
          ·
            refine ⟨203120365755126726776060785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 270827154340168969034747713 203120365755126726776060785)
            ·
              refine ⟨152340274316345045082045589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 203120365755126726776060785 152340274316345045082045589)
              ·
                refine ⟨7140950358578673988220887, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 152340274316345045082045589 7140950358578673988220887)
                ·
                  refine ⟨10711425537868010982331331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7140950358578673988220887 10711425537868010982331331)
                  ·
                    refine ⟨16067138306802016473496997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 10711425537868010982331331 16067138306802016473496997)
                    ·
                      refine ⟨3012588432525378088780687, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 16067138306802016473496997 3012588432525378088780687)
                      ·
                        rfl

theorem cell23_5866995_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 2, 2, 6, 1, 1, 4].length) (baseStart_5866995 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5866995 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5866995 prefixEnd_5866995 := by exact prefixLift 5866995
  have htrace : WordTrace (prefixWord ++ tailWord_5866995) baseStart_5866995 baseEnd_5866995 := by
    simpa [prefixWord, tailWord_5866995, baseEnd_5866995] using wordTrace_append hprefix tailTrace_5866995
  have hstable : (prefixWord ++ tailWord_5866995).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5866995).length < 2 ^ (prefixWord ++ tailWord_5866995).sum := by decide
  have hdescent : baseEnd_5866995 < baseStart_5866995 := by decide
  rcases family_descends (prefixWord ++ tailWord_5866995) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867005 : List Nat := [1, 4, 1, 1, 1, 5, 1, 2, 1, 6]
def baseStart_5867005 : Nat := 118140960795 + 5867005 * 2 ^ 59
def prefixEnd_5867005 : Nat := 4983230072969 + 3 ^ 40 * 5867005 * 2
def baseEnd_5867005 : Nat := 1004197855777307683218547

theorem tailTrace_5867005 : CollatzResearch.WordTrace tailWord_5867005 prefixEnd_5867005 1004197855777307683218547 := by
  unfold tailWord_5867005
  simp only [CollatzResearch.WordTrace]
  refine ⟨213987252109850364525442469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142658168073233576350294979 213987252109850364525442469)
  ·
    refine ⟨40122609770596943348520463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213987252109850364525442469 40122609770596943348520463)
    ·
      refine ⟨60183914655895415022780695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40122609770596943348520463 60183914655895415022780695)
      ·
        refine ⟨90275871983843122534171043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60183914655895415022780695 90275871983843122534171043)
        ·
          refine ⟨135413807975764683801256565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90275871983843122534171043 135413807975764683801256565)
          ·
            refine ⟨12695044497727939106367803, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 135413807975764683801256565 12695044497727939106367803)
            ·
              refine ⟨19042566746591908659551705, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12695044497727939106367803 19042566746591908659551705)
              ·
                refine ⟨14281925059943931494663779, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 19042566746591908659551705 14281925059943931494663779)
                ·
                  refine ⟨21422887589915897241995669, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 14281925059943931494663779 21422887589915897241995669)
                  ·
                    refine ⟨1004197855777307683218547, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21422887589915897241995669 1004197855777307683218547)
                    ·
                      rfl

theorem cell23_5867005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 2, 1, 6].length) (baseStart_5867005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867005 prefixEnd_5867005 := by exact prefixLift 5867005
  have htrace : WordTrace (prefixWord ++ tailWord_5867005) baseStart_5867005 baseEnd_5867005 := by
    simpa [prefixWord, tailWord_5867005, baseEnd_5867005] using wordTrace_append hprefix tailTrace_5867005
  have hstable : (prefixWord ++ tailWord_5867005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867005).length < 2 ^ (prefixWord ++ tailWord_5867005).sum := by decide
  have hdescent : baseEnd_5867005 < baseStart_5867005 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867009 : List Nat := [1, 2, 4, 1, 4, 1, 3, 1, 1, 5]
def baseStart_5867009 : Nat := 118140960795 + 5867009 * 2 ^ 59
def prefixEnd_5867009 : Nat := 4983230072969 + 3 ^ 40 * 5867009 * 2
def baseEnd_5867009 : Nat := 1004198540418180344668541

theorem tailTrace_5867009 : CollatzResearch.WordTrace tailWord_5867009 prefixEnd_5867009 1004198540418180344668541 := by
  unfold tailWord_5867009
  simp only [CollatzResearch.WordTrace]
  refine ⟨213987398001835873208588081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142658265334557248805725387 213987398001835873208588081)
  ·
    refine ⟨160490548501376904906441061, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213987398001835873208588081 160490548501376904906441061)
    ·
      refine ⟨30091977844008169669957699, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 160490548501376904906441061 30091977844008169669957699)
      ·
        refine ⟨45137966766012254504936549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30091977844008169669957699 45137966766012254504936549)
        ·
          refine ⟨8463368768627297719675603, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 45137966766012254504936549 8463368768627297719675603)
          ·
            refine ⟨12695053152940946579513405, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463368768627297719675603 12695053152940946579513405)
            ·
              refine ⟨4760644932352854967317527, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 12695053152940946579513405 4760644932352854967317527)
              ·
                refine ⟨7140967398529282450976291, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 4760644932352854967317527 7140967398529282450976291)
                ·
                  refine ⟨10711451097793923676464437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 7140967398529282450976291 10711451097793923676464437)
                  ·
                    refine ⟨1004198540418180344668541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 10711451097793923676464437 1004198540418180344668541)
                    ·
                      rfl

theorem cell23_5867009_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 3, 1, 1, 5].length) (baseStart_5867009 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867009 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867009 prefixEnd_5867009 := by exact prefixLift 5867009
  have htrace : WordTrace (prefixWord ++ tailWord_5867009) baseStart_5867009 baseEnd_5867009 := by
    simpa [prefixWord, tailWord_5867009, baseEnd_5867009] using wordTrace_append hprefix tailTrace_5867009
  have hstable : (prefixWord ++ tailWord_5867009).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867009).length < 2 ^ (prefixWord ++ tailWord_5867009).sum := by decide
  have hdescent : baseEnd_5867009 < baseStart_5867009 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867009) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867018 : List Nat := [3, 1, 2, 2, 2, 13]
def baseStart_5867018 : Nat := 118140960795 + 5867018 * 2 ^ 59
def prefixEnd_5867018 : Nat := 4983230072969 + 3 ^ 40 * 5867018 * 2
def baseEnd_5867018 : Nat := 12397531862470911517667

theorem tailTrace_5867018 : CollatzResearch.WordTrace tailWord_5867018 prefixEnd_5867018 12397531862470911517667 := by
  unfold tailWord_5867018
  simp only [CollatzResearch.WordTrace]
  refine ⟨53496931564700816936416427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142658484172535511830443805 53496931564700816936416427)
  ·
    refine ⟨80245397347051225404624641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 53496931564700816936416427 80245397347051225404624641)
    ·
      refine ⟨60184048010288419053468481, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 80245397347051225404624641 60184048010288419053468481)
      ·
        refine ⟨45138036007716314290101361, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60184048010288419053468481 45138036007716314290101361)
        ·
          refine ⟨33853527005787235717576021, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 45138036007716314290101361 33853527005787235717576021)
          ·
            refine ⟨12397531862470911517667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 13 33853527005787235717576021 12397531862470911517667)
            ·
              rfl

theorem cell23_5867018_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 2, 13].length) (baseStart_5867018 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867018 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867018 prefixEnd_5867018 := by exact prefixLift 5867018
  have htrace : WordTrace (prefixWord ++ tailWord_5867018) baseStart_5867018 baseEnd_5867018 := by
    simpa [prefixWord, tailWord_5867018, baseEnd_5867018] using wordTrace_append hprefix tailTrace_5867018
  have hstable : (prefixWord ++ tailWord_5867018).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867018).length < 2 ^ (prefixWord ++ tailWord_5867018).sum := by decide
  have hdescent : baseEnd_5867018 < baseStart_5867018 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867018) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867079 : List Nat := [1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 3]
def baseStart_5867079 : Nat := 118140960795 + 5867079 * 2 ^ 59
def prefixEnd_5867079 : Nat := 4983230072969 + 3 ^ 40 * 5867079 * 2
def baseEnd_5867079 : Nat := 3012631564900355760130301

theorem tailTrace_5867079 : CollatzResearch.WordTrace tailWord_5867079 prefixEnd_5867079 3012631564900355760130301 := by
  unfold tailWord_5867079
  simp only [CollatzResearch.WordTrace]
  refine ⟨213989951111582275163636291, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142659967407721516775757527 213989951111582275163636291)
  ·
    refine ⟨320984926667373412745454437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213989951111582275163636291 320984926667373412745454437)
    ·
      refine ⟨60184673750132514889772707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 320984926667373412745454437 60184673750132514889772707)
      ·
        refine ⟨90277010625198772334659061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60184673750132514889772707 90277010625198772334659061)
        ·
          refine ⟨8463469746112384906374287, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 90277010625198772334659061 8463469746112384906374287)
          ·
            refine ⟨12695204619168577359561431, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 8463469746112384906374287 12695204619168577359561431)
            ·
              refine ⟨19042806928752866039342147, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12695204619168577359561431 19042806928752866039342147)
              ·
                refine ⟨28564210393129299059013221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19042806928752866039342147 28564210393129299059013221)
                ·
                  refine ⟨5355789448711743573564979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 28564210393129299059013221 5355789448711743573564979)
                  ·
                    refine ⟨8033684173067615360347469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 5355789448711743573564979 8033684173067615360347469)
                    ·
                      refine ⟨3012631564900355760130301, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 8033684173067615360347469 3012631564900355760130301)
                      ·
                        rfl

theorem cell23_5867079_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 5, 1, 1, 1, 4, 1, 3].length) (baseStart_5867079 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867079 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867079 prefixEnd_5867079 := by exact prefixLift 5867079
  have htrace : WordTrace (prefixWord ++ tailWord_5867079) baseStart_5867079 baseEnd_5867079 := by
    simpa [prefixWord, tailWord_5867079, baseEnd_5867079] using wordTrace_append hprefix tailTrace_5867079
  have hstable : (prefixWord ++ tailWord_5867079).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867079).length < 2 ^ (prefixWord ++ tailWord_5867079).sum := by decide
  have hdescent : baseEnd_5867079 < baseStart_5867079 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867079) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867095 : List Nat := [1, 1, 3, 2, 2, 3, 2, 1, 2, 6]
def baseStart_5867095 : Nat := 118140960795 + 5867095 * 2 ^ 59
def prefixEnd_5867095 : Nat := 4983230072969 + 3 ^ 40 * 5867095 * 2
def baseEnd_5867095 : Nat := 1004213260196942565843409

theorem tailTrace_5867095 : CollatzResearch.WordTrace tailWord_5867095 prefixEnd_5867095 1004213260196942565843409 := by
  unfold tailWord_5867095
  simp only [CollatzResearch.WordTrace]
  refine ⟨213990534679524309896218739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142660356453016206597479159 213990534679524309896218739)
  ·
    refine ⟨320985802019286464844328109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 213990534679524309896218739 320985802019286464844328109)
    ·
      refine ⟨120369675757232424316623041, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 320985802019286464844328109 120369675757232424316623041)
      ·
        refine ⟨90277256817924318237467281, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 120369675757232424316623041 90277256817924318237467281)
        ·
          refine ⟨67707942613443238678100461, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 90277256817924318237467281 67707942613443238678100461)
          ·
            refine ⟨25390478480041214504287673, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 67707942613443238678100461 25390478480041214504287673)
            ·
              refine ⟨19042858860030910878215755, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 25390478480041214504287673 19042858860030910878215755)
              ·
                refine ⟨28564288290046366317323633, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19042858860030910878215755 28564288290046366317323633)
                ·
                  refine ⟨21423216217534774737992725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28564288290046366317323633 21423216217534774737992725)
                  ·
                    refine ⟨1004213260196942565843409, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 21423216217534774737992725 1004213260196942565843409)
                    ·
                      rfl

theorem cell23_5867095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 2, 3, 2, 1, 2, 6].length) (baseStart_5867095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867095 prefixEnd_5867095 := by exact prefixLift 5867095
  have htrace : WordTrace (prefixWord ++ tailWord_5867095) baseStart_5867095 baseEnd_5867095 := by
    simpa [prefixWord, tailWord_5867095, baseEnd_5867095] using wordTrace_append hprefix tailTrace_5867095
  have hstable : (prefixWord ++ tailWord_5867095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867095).length < 2 ^ (prefixWord ++ tailWord_5867095).sum := by decide
  have hdescent : baseEnd_5867095 < baseStart_5867095 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867105 : List Nat := [1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 5]
def baseStart_5867105 : Nat := 118140960795 + 5867105 * 2 ^ 59
def prefixEnd_5867105 : Nat := 4983230072969 + 3 ^ 40 * 5867105 * 2
def baseEnd_5867105 : Nat := 3012644915397372658405181

theorem tailTrace_5867105 : CollatzResearch.WordTrace tailWord_5867105 prefixEnd_5867105 3012644915397372658405181 := by
  unfold tailWord_5867105
  simp only [CollatzResearch.WordTrace]
  refine ⟨213990899409488081604082769, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142660599606325387736055179 213990899409488081604082769)
  ·
    refine ⟨160493174557116061203062077, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 213990899409488081604082769 160493174557116061203062077)
    ·
      refine ⟨60184940458918522951148279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 160493174557116061203062077 60184940458918522951148279)
      ·
        refine ⟨90277410688377784426722419, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 60184940458918522951148279 90277410688377784426722419)
        ·
          refine ⟨135416116032566676640083629, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 90277410688377784426722419 135416116032566676640083629)
          ·
            refine ⟨50781043512212503740031361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 135416116032566676640083629 50781043512212503740031361)
            ·
              refine ⟨38085782634159377805023521, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 50781043512212503740031361 38085782634159377805023521)
              ·
                refine ⟨28564336975619533353767641, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 38085782634159377805023521 28564336975619533353767641)
                ·
                  refine ⟨21423252731714650015325731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28564336975619533353767641 21423252731714650015325731)
                  ·
                    refine ⟨32134879097571975022988597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21423252731714650015325731 32134879097571975022988597)
                    ·
                      refine ⟨3012644915397372658405181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32134879097571975022988597 3012644915397372658405181)
                      ·
                        rfl

theorem cell23_5867105_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 2, 2, 1, 5].length) (baseStart_5867105 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867105 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867105 prefixEnd_5867105 := by exact prefixLift 5867105
  have htrace : WordTrace (prefixWord ++ tailWord_5867105) baseStart_5867105 baseEnd_5867105 := by
    simpa [prefixWord, tailWord_5867105, baseEnd_5867105] using wordTrace_append hprefix tailTrace_5867105
  have hstable : (prefixWord ++ tailWord_5867105).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867105).length < 2 ^ (prefixWord ++ tailWord_5867105).sum := by decide
  have hdescent : baseEnd_5867105 < baseStart_5867105 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867105) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867122 : List Nat := [3, 2, 1, 2, 3, 2, 1, 1, 2, 1, 5]
def baseStart_5867122 : Nat := 118140960795 + 5867122 * 2 ^ 59
def prefixEnd_5867122 : Nat := 4983230072969 + 3 ^ 40 * 5867122 * 2
def baseEnd_5867122 : Nat := 3012653644568499091892603

theorem tailTrace_5867122 : CollatzResearch.WordTrace tailWord_5867122 prefixEnd_5867122 3012653644568499091892603 := by
  unfold tailWord_5867122
  simp only [CollatzResearch.WordTrace]
  refine ⟨53497879862606623376862905, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 142661012966950995671634413 53497879862606623376862905)
  ·
    refine ⟨40123409896954967532647179, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 53497879862606623376862905 40123409896954967532647179)
    ·
      refine ⟨60185114845432451298970769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 40123409896954967532647179 60185114845432451298970769)
      ·
        refine ⟨45138836134074338474228077, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 60185114845432451298970769 45138836134074338474228077)
        ·
          refine ⟨16927063550277876927835529, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 45138836134074338474228077 16927063550277876927835529)
          ·
            refine ⟨12695297662708407695876647, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 16927063550277876927835529 12695297662708407695876647)
            ·
              refine ⟨19042946494062611543814971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 12695297662708407695876647 19042946494062611543814971)
              ·
                refine ⟨28564419741093917315722457, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 19042946494062611543814971 28564419741093917315722457)
                ·
                  refine ⟨21423314805820437986791843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 28564419741093917315722457 21423314805820437986791843)
                  ·
                    refine ⟨32134972208730656980187765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 21423314805820437986791843 32134972208730656980187765)
                    ·
                      refine ⟨3012653644568499091892603, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 32134972208730656980187765 3012653644568499091892603)
                      ·
                        rfl

theorem cell23_5867122_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 1, 2, 1, 5].length) (baseStart_5867122 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867122 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867122 prefixEnd_5867122 := by exact prefixLift 5867122
  have htrace : WordTrace (prefixWord ++ tailWord_5867122) baseStart_5867122 baseEnd_5867122 := by
    simpa [prefixWord, tailWord_5867122, baseEnd_5867122] using wordTrace_append hprefix tailTrace_5867122
  have hstable : (prefixWord ++ tailWord_5867122).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867122).length < 2 ^ (prefixWord ++ tailWord_5867122).sum := by decide
  have hdescent : baseEnd_5867122 < baseStart_5867122 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867122) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_5867165 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 7]
def baseStart_5867165 : Nat := 118140960795 + 5867165 * 2 ^ 59
def prefixEnd_5867165 : Nat := 4983230072969 + 3 ^ 40 * 5867165 * 2
def baseEnd_5867165 : Nat := 3012675724236642423654905

theorem tailTrace_5867165 : CollatzResearch.WordTrace tailWord_5867165 prefixEnd_5867165 3012675724236642423654905 := by
  unfold tailWord_5867165
  simp only [CollatzResearch.WordTrace]
  refine ⟨213993087789270711851266949, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 142662058526180474567511299 213993087789270711851266949)
  ·
    refine ⟨40123703960488258472112553, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 213993087789270711851266949 40123703960488258472112553)
    ·
      refine ⟨30092777970366193854084415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 40123703960488258472112553 30092777970366193854084415)
      ·
        refine ⟨45139166955549290781126623, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 30092777970366193854084415 45139166955549290781126623)
        ·
          refine ⟨67708750433323936171689935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 45139166955549290781126623 67708750433323936171689935)
          ·
            refine ⟨101563125649985904257534903, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 67708750433323936171689935 101563125649985904257534903)
            ·
              refine ⟨152344688474978856386302355, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 101563125649985904257534903 152344688474978856386302355)
              ·
                refine ⟨228517032712468284579453533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 152344688474978856386302355 228517032712468284579453533)
                ·
                  refine ⟨85693887267175606717295075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 228517032712468284579453533 85693887267175606717295075)
                  ·
                    refine ⟨128540830900763410075942613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 85693887267175606717295075 128540830900763410075942613)
                    ·
                      refine ⟨3012675724236642423654905, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 128540830900763410075942613 3012675724236642423654905)
                      ·
                        rfl

theorem cell23_5867165_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 3, 1, 7].length) (baseStart_5867165 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_5867165 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_5867165 prefixEnd_5867165 := by exact prefixLift 5867165
  have htrace : WordTrace (prefixWord ++ tailWord_5867165) baseStart_5867165 baseEnd_5867165 := by
    simpa [prefixWord, tailWord_5867165, baseEnd_5867165] using wordTrace_append hprefix tailTrace_5867165
  have hstable : (prefixWord ++ tailWord_5867165).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_5867165).length < 2 ^ (prefixWord ++ tailWord_5867165).sum := by decide
  have hdescent : baseEnd_5867165 < baseStart_5867165 := by decide
  rcases family_descends (prefixWord ++ tailWord_5867165) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
