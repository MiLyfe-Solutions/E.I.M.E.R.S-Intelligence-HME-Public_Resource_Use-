import V185TrunkScan23Chunk1152

open CollatzResearch V185TrunkScan12 V185TrunkScan13Incremental V185TrunkScan14Incremental V185TrunkScan15Incremental V185TrunkScan16Incremental V185TrunkScan17Incremental V185TrunkScan18Incremental V185TrunkScan19Incremental V185TrunkScan20Incremental V185TrunkScan21Incremental V185TrunkScan22Incremental

namespace V185TrunkScan23Incremental

def tailWord_6829674 : List Nat := [3, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4]
def baseStart_6829674 : Nat := 118140960795 + 6829674 * 2 ^ 59
def prefixEnd_6829674 : Nat := 4983230072969 + 3 ^ 40 * 6829674 * 2
def baseEnd_6829674 : Nat := 3506905475515017102765907

theorem tailTrace_6829674 : CollatzResearch.WordTrace tailWord_6829674 prefixEnd_6829674 3506905475515017102765907 := by
  unfold tailWord_6829674
  simp only [CollatzResearch.WordTrace]
  refine ⟨62274668764816247075308019, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166065783372843325534154717 62274668764816247075308019)
  ·
    refine ⟨93412003147224370612962029, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62274668764816247075308019 93412003147224370612962029)
    ·
      refine ⟨35029501180209138979860761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93412003147224370612962029 35029501180209138979860761)
      ·
        refine ⟨26272125885156854234895571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35029501180209138979860761 26272125885156854234895571)
        ·
          refine ⟨39408188827735281352343357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26272125885156854234895571 39408188827735281352343357)
          ·
            refine ⟨14778070810400730507128759, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39408188827735281352343357 14778070810400730507128759)
            ·
              refine ⟨22167106215601095760693139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14778070810400730507128759 22167106215601095760693139)
              ·
                refine ⟨33250659323401643641039709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22167106215601095760693139 33250659323401643641039709)
                ·
                  refine ⟨12468997246275616365389891, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33250659323401643641039709 12468997246275616365389891)
                  ·
                    refine ⟨18703495869413424548084837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12468997246275616365389891 18703495869413424548084837)
                    ·
                      refine ⟨3506905475515017102765907, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18703495869413424548084837 3506905475515017102765907)
                      ·
                        rfl

theorem cell23_6829674_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 2, 1, 3, 1, 1, 3, 1, 4].length) (baseStart_6829674 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829674 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829674 prefixEnd_6829674 := by exact prefixLift 6829674
  have htrace : WordTrace (prefixWord ++ tailWord_6829674) baseStart_6829674 baseEnd_6829674 := by
    simpa [prefixWord, tailWord_6829674, baseEnd_6829674] using wordTrace_append hprefix tailTrace_6829674
  have hstable : (prefixWord ++ tailWord_6829674).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829674).length < 2 ^ (prefixWord ++ tailWord_6829674).sum := by decide
  have hdescent : baseEnd_6829674 < baseStart_6829674 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829674) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829678 : List Nat := [4, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2]
def baseStart_6829678 : Nat := 118140960795 + 6829678 * 2 ^ 59
def prefixEnd_6829678 : Nat := 4983230072969 + 3 ^ 40 * 6829678 * 2
def baseEnd_6829678 : Nat := 3506907529437635087115889

theorem tailTrace_6829678 : CollatzResearch.WordTrace tailWord_6829678 prefixEnd_6829678 3506907529437635087115889 := by
  unfold tailWord_6829678
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137352618906312123047211, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166065880634166997989585125 31137352618906312123047211)
  ·
    refine ⟨46706028928359468184570817, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31137352618906312123047211 46706028928359468184570817)
    ·
      refine ⟨35029521696269601138428113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46706028928359468184570817 35029521696269601138428113)
      ·
        refine ⟨26272141272202200853821085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35029521696269601138428113 26272141272202200853821085)
        ·
          refine ⟨9852052977075825320182907, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26272141272202200853821085 9852052977075825320182907)
          ·
            refine ⟨14778079465613737980274361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9852052977075825320182907 14778079465613737980274361)
            ·
              refine ⟨11083559599210303485205771, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14778079465613737980274361 11083559599210303485205771)
              ·
                refine ⟨16625339398815455227808657, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083559599210303485205771 16625339398815455227808657)
                ·
                  refine ⟨12469004549111591420856493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16625339398815455227808657 12469004549111591420856493)
                  ·
                    refine ⟨4675876705916846782821185, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12469004549111591420856493 4675876705916846782821185)
                    ·
                      refine ⟨3506907529437635087115889, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675876705916846782821185 3506907529437635087115889)
                      ·
                        rfl

theorem cell23_6829678_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 3, 1, 2, 1, 2, 3, 2].length) (baseStart_6829678 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829678 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829678 prefixEnd_6829678 := by exact prefixLift 6829678
  have htrace : WordTrace (prefixWord ++ tailWord_6829678) baseStart_6829678 baseEnd_6829678 := by
    simpa [prefixWord, tailWord_6829678, baseEnd_6829678] using wordTrace_append hprefix tailTrace_6829678
  have hstable : (prefixWord ++ tailWord_6829678).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829678).length < 2 ^ (prefixWord ++ tailWord_6829678).sum := by decide
  have hdescent : baseEnd_6829678 < baseStart_6829678 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829678) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829707 : List Nat := [1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 3]
def baseStart_6829707 : Nat := 118140960795 + 6829707 * 2 ^ 59
def prefixEnd_6829707 : Nat := 4983230072969 + 3 ^ 40 * 6829707 * 2
def baseEnd_6829707 : Nat := 3506922420376615473653255

theorem tailTrace_6829707 : CollatzResearch.WordTrace tailWord_6829707 prefixEnd_6829707 3506922420376615473653255 := by
  unfold tailWord_6829707
  simp only [CollatzResearch.WordTrace]
  refine ⟨249099878668145434937183375, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166066585778763623291455583 249099878668145434937183375)
  ·
    refine ⟨373649818002218152405775063, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249099878668145434937183375 373649818002218152405775063)
    ·
      refine ⟨560474727003327228608662595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373649818002218152405775063 560474727003327228608662595)
      ·
        refine ⟨840712090504990842912993893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560474727003327228608662595 840712090504990842912993893)
        ·
          refine ⟨157633516969685783046186355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 840712090504990842912993893 157633516969685783046186355)
          ·
            refine ⟨236450275454528674569279533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157633516969685783046186355 236450275454528674569279533)
            ·
              refine ⟨88668853295448252963479825, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236450275454528674569279533 88668853295448252963479825)
              ·
                refine ⟨66501639971586189722609869, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88668853295448252963479825 66501639971586189722609869)
                ·
                  refine ⟨24938114989344821145978701, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66501639971586189722609869 24938114989344821145978701)
                  ·
                    refine ⟨9351793121004307929742013, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24938114989344821145978701 9351793121004307929742013)
                    ·
                      refine ⟨3506922420376615473653255, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9351793121004307929742013 3506922420376615473653255)
                      ·
                        rfl

theorem cell23_6829707_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 3, 2, 3, 3, 3].length) (baseStart_6829707 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829707 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829707 prefixEnd_6829707 := by exact prefixLift 6829707
  have htrace : WordTrace (prefixWord ++ tailWord_6829707) baseStart_6829707 baseEnd_6829707 := by
    simpa [prefixWord, tailWord_6829707, baseEnd_6829707] using wordTrace_append hprefix tailTrace_6829707
  have hstable : (prefixWord ++ tailWord_6829707).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829707).length < 2 ^ (prefixWord ++ tailWord_6829707).sum := by decide
  have hdescent : baseEnd_6829707 < baseStart_6829707 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829707) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829708 : List Nat := [2, 2, 1, 2, 1, 1, 5, 4, 1, 2, 2]
def baseStart_6829708 : Nat := 118140960795 + 6829708 * 2 ^ 59
def prefixEnd_6829708 : Nat := 4983230072969 + 3 ^ 40 * 6829708 * 2
def baseEnd_6829708 : Nat := 3506922933857269969740751

theorem tailTrace_6829708 : CollatzResearch.WordTrace tailWord_6829708 prefixEnd_6829708 3506922933857269969740751 := by
  unfold tailWord_6829708
  simp only [CollatzResearch.WordTrace]
  refine ⟨124549957570570906053984889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166066610094094541405313185 124549957570570906053984889)
  ·
    refine ⟨93412468177928179540488667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124549957570570906053984889 93412468177928179540488667)
    ·
      refine ⟨140118702266892269310733001, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93412468177928179540488667 140118702266892269310733001)
      ·
        refine ⟨105089026700169201983049751, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140118702266892269310733001 105089026700169201983049751)
        ·
          refine ⟨157633540050253802974574627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105089026700169201983049751 157633540050253802974574627)
          ·
            refine ⟨236450310075380704461861941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157633540050253802974574627 236450310075380704461861941)
            ·
              refine ⟨22167216569566941043299557, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236450310075380704461861941 22167216569566941043299557)
              ·
                refine ⟨4156353106793801445618667, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22167216569566941043299557 4156353106793801445618667)
                ·
                  refine ⟨6234529660190702168428001, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156353106793801445618667 6234529660190702168428001)
                  ·
                    refine ⟨4675897245143026626321001, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6234529660190702168428001 4675897245143026626321001)
                    ·
                      refine ⟨3506922933857269969740751, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675897245143026626321001 3506922933857269969740751)
                      ·
                        rfl

theorem cell23_6829708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 1, 5, 4, 1, 2, 2].length) (baseStart_6829708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829708 prefixEnd_6829708 := by exact prefixLift 6829708
  have htrace : WordTrace (prefixWord ++ tailWord_6829708) baseStart_6829708 baseEnd_6829708 := by
    simpa [prefixWord, tailWord_6829708, baseEnd_6829708] using wordTrace_append hprefix tailTrace_6829708
  have hstable : (prefixWord ++ tailWord_6829708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829708).length < 2 ^ (prefixWord ++ tailWord_6829708).sum := by decide
  have hdescent : baseEnd_6829708 < baseStart_6829708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829741 : List Nat := [1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 3]
def baseStart_6829741 : Nat := 118140960795 + 6829741 * 2 ^ 59
def prefixEnd_6829741 : Nat := 4983230072969 + 3 ^ 40 * 6829741 * 2
def baseEnd_6829741 : Nat := 3506939878718868340628099

theorem tailTrace_6829741 : CollatzResearch.WordTrace tailWord_6829741 prefixEnd_6829741 3506939878718868340628099 := by
  unfold tailWord_6829741
  simp only [CollatzResearch.WordTrace]
  refine ⟨249101118750022258743921077, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166067412500014839162614051 249101118750022258743921077)
  ·
    refine ⟨23353229882814586757242601, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249101118750022258743921077 23353229882814586757242601)
    ·
      refine ⟨17514922412110940067931951, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23353229882814586757242601 17514922412110940067931951)
      ·
        refine ⟨26272383618166410101897927, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17514922412110940067931951 26272383618166410101897927)
        ·
          refine ⟨39408575427249615152846891, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26272383618166410101897927 39408575427249615152846891)
          ·
            refine ⟨59112863140874422729270337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39408575427249615152846891 59112863140874422729270337)
            ·
              refine ⟨44334647355655817046952753, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59112863140874422729270337 44334647355655817046952753)
              ·
                refine ⟨33250985516741862785214565, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44334647355655817046952753 33250985516741862785214565)
                ·
                  refine ⟨6234559784389099272227731, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33250985516741862785214565 6234559784389099272227731)
                  ·
                    refine ⟨9351839676583648908341597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6234559784389099272227731 9351839676583648908341597)
                    ·
                      refine ⟨3506939878718868340628099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9351839676583648908341597 3506939878718868340628099)
                      ·
                        rfl

theorem cell23_6829741_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 1, 1, 1, 2, 2, 4, 1, 3].length) (baseStart_6829741 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829741 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829741 prefixEnd_6829741 := by exact prefixLift 6829741
  have htrace : WordTrace (prefixWord ++ tailWord_6829741) baseStart_6829741 baseEnd_6829741 := by
    simpa [prefixWord, tailWord_6829741, baseEnd_6829741] using wordTrace_append hprefix tailTrace_6829741
  have hstable : (prefixWord ++ tailWord_6829741).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829741).length < 2 ^ (prefixWord ++ tailWord_6829741).sum := by decide
  have hdescent : baseEnd_6829741 < baseStart_6829741 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829741) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829742 : List Nat := [4, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4]
def baseStart_6829742 : Nat := 118140960795 + 6829742 * 2 ^ 59
def prefixEnd_6829742 : Nat := 4983230072969 + 3 ^ 40 * 6829742 * 2
def baseEnd_6829742 : Nat := 3506940392199522836715595

theorem tailTrace_6829742 : CollatzResearch.WordTrace tailWord_6829742 prefixEnd_6829742 3506940392199522836715595 := by
  unfold tailWord_6829742
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137644402877329489338435, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166067436815345757276471653 31137644402877329489338435)
  ·
    refine ⟨46706466604315994234007653, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31137644402877329489338435 46706466604315994234007653)
    ·
      refine ⟨8757462488309248918876435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 46706466604315994234007653 8757462488309248918876435)
      ·
        refine ⟨13136193732463873378314653, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8757462488309248918876435 13136193732463873378314653)
        ·
          refine ⟨4926072649673952516867995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13136193732463873378314653 4926072649673952516867995)
          ·
            refine ⟨7389108974510928775301993, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926072649673952516867995 7389108974510928775301993)
            ·
              refine ⟨5541831730883196581476495, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389108974510928775301993 5541831730883196581476495)
              ·
                refine ⟨8312747596324794872214743, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5541831730883196581476495 8312747596324794872214743)
                ·
                  refine ⟨12469121394487192308322115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8312747596324794872214743 12469121394487192308322115)
                  ·
                    refine ⟨18703682091730788462483173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12469121394487192308322115 18703682091730788462483173)
                    ·
                      refine ⟨3506940392199522836715595, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18703682091730788462483173 3506940392199522836715595)
                      ·
                        rfl

theorem cell23_6829742_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 4, 1, 3, 1, 2, 1, 1, 1, 4].length) (baseStart_6829742 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829742 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829742 prefixEnd_6829742 := by exact prefixLift 6829742
  have htrace : WordTrace (prefixWord ++ tailWord_6829742) baseStart_6829742 baseEnd_6829742 := by
    simpa [prefixWord, tailWord_6829742, baseEnd_6829742] using wordTrace_append hprefix tailTrace_6829742
  have hstable : (prefixWord ++ tailWord_6829742).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829742).length < 2 ^ (prefixWord ++ tailWord_6829742).sum := by decide
  have hdescent : baseEnd_6829742 < baseStart_6829742 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829742) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829757 : List Nat := [1, 4, 1, 2, 1, 2, 1, 1, 4, 6]
def baseStart_6829757 : Nat := 118140960795 + 6829757 * 2 ^ 59
def prefixEnd_6829757 : Nat := 4983230072969 + 3 ^ 40 * 6829757 * 2
def baseEnd_6829757 : Nat := 1168982698136446759342675

theorem tailTrace_6829757 : CollatzResearch.WordTrace tailWord_6829757 prefixEnd_6829757 1168982698136446759342675 := by
  unfold tailWord_6829757
  simp only [CollatzResearch.WordTrace]
  refine ⟨249101702317964293476503525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166067801545309528984335683 249101702317964293476503525)
  ·
    refine ⟨46706569184618305026844411, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249101702317964293476503525 46706569184618305026844411)
    ·
      refine ⟨70059853776927457540266617, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46706569184618305026844411 70059853776927457540266617)
      ·
        refine ⟨52544890332695593155199963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70059853776927457540266617 52544890332695593155199963)
        ·
          refine ⟨78817335499043389732799945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52544890332695593155199963 78817335499043389732799945)
          ·
            refine ⟨59113001624282542299599959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78817335499043389732799945 59113001624282542299599959)
            ·
              refine ⟨88669502436423813449399939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59113001624282542299599959 88669502436423813449399939)
              ·
                refine ⟨133004253654635720174099909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88669502436423813449399939 133004253654635720174099909)
                ·
                  refine ⟨24938297560244197532643733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133004253654635720174099909 24938297560244197532643733)
                  ·
                    refine ⟨1168982698136446759342675, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24938297560244197532643733 1168982698136446759342675)
                    ·
                      rfl

theorem cell23_6829757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 1, 2, 1, 1, 4, 6].length) (baseStart_6829757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829757 prefixEnd_6829757 := by exact prefixLift 6829757
  have htrace : WordTrace (prefixWord ++ tailWord_6829757) baseStart_6829757 baseEnd_6829757 := by
    simpa [prefixWord, tailWord_6829757, baseEnd_6829757] using wordTrace_append hprefix tailTrace_6829757
  have hstable : (prefixWord ++ tailWord_6829757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829757).length < 2 ^ (prefixWord ++ tailWord_6829757).sum := by decide
  have hdescent : baseEnd_6829757 < baseStart_6829757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829758 : List Nat := [4, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3]
def baseStart_6829758 : Nat := 118140960795 + 6829758 * 2 ^ 59
def prefixEnd_6829758 : Nat := 4983230072969 + 3 ^ 40 * 6829758 * 2
def baseEnd_6829758 : Nat := 3506948607889994774115521

theorem tailTrace_6829758 : CollatzResearch.WordTrace tailWord_6829758 prefixEnd_6829758 3506948607889994774115521 := by
  unfold tailWord_6829758
  simp only [CollatzResearch.WordTrace]
  refine ⟨31137717348870083830911241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166067825860640447098193285 31137717348870083830911241)
  ·
    refine ⟨23353288011652562873183431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31137717348870083830911241 23353288011652562873183431)
    ·
      refine ⟨35029932017478844309775147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23353288011652562873183431 35029932017478844309775147)
      ·
        refine ⟨52544898026218266464662721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35029932017478844309775147 52544898026218266464662721)
        ·
          refine ⟨39408673519663699848497041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52544898026218266464662721 39408673519663699848497041)
          ·
            refine ⟨29556505139747774886372781, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39408673519663699848497041 29556505139747774886372781)
            ·
              refine ⟨11083689427405415582389793, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29556505139747774886372781 11083689427405415582389793)
              ·
                refine ⟨8312767070554061686792345, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11083689427405415582389793 8312767070554061686792345)
                ·
                  refine ⟨6234575302915546265094259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8312767070554061686792345 6234575302915546265094259)
                  ·
                    refine ⟨9351862954373319397641389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6234575302915546265094259 9351862954373319397641389)
                    ·
                      refine ⟨3506948607889994774115521, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9351862954373319397641389 3506948607889994774115521)
                      ·
                        rfl

theorem cell23_6829758_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 2, 2, 3, 2, 2, 1, 3].length) (baseStart_6829758 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829758 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829758 prefixEnd_6829758 := by exact prefixLift 6829758
  have htrace : WordTrace (prefixWord ++ tailWord_6829758) baseStart_6829758 baseEnd_6829758 := by
    simpa [prefixWord, tailWord_6829758, baseEnd_6829758] using wordTrace_append hprefix tailTrace_6829758
  have hstable : (prefixWord ++ tailWord_6829758).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829758).length < 2 ^ (prefixWord ++ tailWord_6829758).sum := by decide
  have hdescent : baseEnd_6829758 < baseStart_6829758 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829758) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829824 : List Nat := [2, 1, 1, 2, 1, 1, 2, 3, 1, 7, 2]
def baseStart_6829824 : Nat := 118140960795 + 6829824 * 2 ^ 59
def prefixEnd_6829824 : Nat := 4983230072969 + 3 ^ 40 * 6829824 * 2
def baseEnd_6829824 : Nat := 3506982497613191515890217

theorem tailTrace_6829824 : CollatzResearch.WordTrace tailWord_6829824 prefixEnd_6829824 3506982497613191515890217 := by
  unfold tailWord_6829824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124552073004360781959596263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166069430672481042612795017 124552073004360781959596263)
  ·
    refine ⟨186828109506541172939394395, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124552073004360781959596263 186828109506541172939394395)
    ·
      refine ⟨280242164259811759409091593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186828109506541172939394395 280242164259811759409091593)
      ·
        refine ⟨210181623194858819556818695, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280242164259811759409091593 210181623194858819556818695)
        ·
          refine ⟨315272434792288229335228043, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210181623194858819556818695 315272434792288229335228043)
          ·
            refine ⟨472908652188432344002842065, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315272434792288229335228043 472908652188432344002842065)
            ·
              refine ⟨354681489141324258002131549, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472908652188432344002842065 354681489141324258002131549)
              ·
                refine ⟨133005558427996596750799331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354681489141324258002131549 133005558427996596750799331)
                ·
                  refine ⟨199508337641994895126198997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133005558427996596750799331 199508337641994895126198997)
                  ·
                    refine ⟨4675976663484255354520289, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 199508337641994895126198997 4675976663484255354520289)
                    ·
                      refine ⟨3506982497613191515890217, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4675976663484255354520289 3506982497613191515890217)
                      ·
                        rfl

theorem cell23_6829824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 1, 2, 3, 1, 7, 2].length) (baseStart_6829824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829824 prefixEnd_6829824 := by exact prefixLift 6829824
  have htrace : WordTrace (prefixWord ++ tailWord_6829824) baseStart_6829824 baseEnd_6829824 := by
    simpa [prefixWord, tailWord_6829824, baseEnd_6829824] using wordTrace_append hprefix tailTrace_6829824
  have hstable : (prefixWord ++ tailWord_6829824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829824).length < 2 ^ (prefixWord ++ tailWord_6829824).sum := by decide
  have hdescent : baseEnd_6829824 < baseStart_6829824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829827 : List Nat := [1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7]
def baseStart_6829827 : Nat := 118140960795 + 6829827 * 2 ^ 59
def prefixEnd_6829827 : Nat := 4983230072969 + 3 ^ 40 * 6829827 * 2
def baseEnd_6829827 : Nat := 3506984038055155004152703

theorem tailTrace_6829827 : CollatzResearch.WordTrace tailWord_6829827 prefixEnd_6829827 3506984038055155004152703 := by
  unfold tailWord_6829827
  simp only [CollatzResearch.WordTrace]
  refine ⟨249104255427710695431551735, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166069503618473796954367823 249104255427710695431551735)
  ·
    refine ⟨373656383141566043147327603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249104255427710695431551735 373656383141566043147327603)
    ·
      refine ⟨560484574712349064720991405, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373656383141566043147327603 560484574712349064720991405)
      ·
        refine ⟨210181715517130899270371777, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560484574712349064720991405 210181715517130899270371777)
        ·
          refine ⟨157636286637848174452778833, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210181715517130899270371777 157636286637848174452778833)
          ·
            refine ⟨118227214978386130839584125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157636286637848174452778833 118227214978386130839584125)
            ·
              refine ⟨44335205616894799064844047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118227214978386130839584125 44335205616894799064844047)
              ·
                refine ⟨66502808425342198597266071, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44335205616894799064844047 66502808425342198597266071)
                ·
                  refine ⟨99754212638013297895899107, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66502808425342198597266071 99754212638013297895899107)
                  ·
                    refine ⟨149631318957019946843848661, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99754212638013297895899107 149631318957019946843848661)
                    ·
                      refine ⟨3506984038055155004152703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149631318957019946843848661 3506984038055155004152703)
                      ·
                        rfl

theorem cell23_6829827_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 2, 2, 3, 1, 1, 1, 7].length) (baseStart_6829827 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829827 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829827 prefixEnd_6829827 := by exact prefixLift 6829827
  have htrace : WordTrace (prefixWord ++ tailWord_6829827) baseStart_6829827 baseEnd_6829827 := by
    simpa [prefixWord, tailWord_6829827, baseEnd_6829827] using wordTrace_append hprefix tailTrace_6829827
  have hstable : (prefixWord ++ tailWord_6829827).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829827).length < 2 ^ (prefixWord ++ tailWord_6829827).sum := by decide
  have hdescent : baseEnd_6829827 < baseStart_6829827 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829827) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829908 : List Nat := [2, 4, 1, 1, 3, 1, 3, 1, 2, 2, 3]
def baseStart_6829908 : Nat := 118140960795 + 6829908 * 2 ^ 59
def prefixEnd_6829908 : Nat := 4983230072969 + 3 ^ 40 * 6829908 * 2
def baseEnd_6829908 : Nat := 3507025629988169187239831

theorem tailTrace_6829908 : CollatzResearch.WordTrace tailWord_6829908 prefixEnd_6829908 3507025629988169187239831 := by
  unfold tailWord_6829908
  simp only [CollatzResearch.WordTrace]
  refine ⟨124553604870208623132625189, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166071473160278164176833585 124553604870208623132625189)
  ·
    refine ⟨23353800913164116837367223, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124553604870208623132625189 23353800913164116837367223)
    ·
      refine ⟨35030701369746175256050835, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23353800913164116837367223 35030701369746175256050835)
      ·
        refine ⟨52546052054619262884076253, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35030701369746175256050835 52546052054619262884076253)
        ·
          refine ⟨19704769520482223581528595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52546052054619262884076253 19704769520482223581528595)
          ·
            refine ⟨29557154280723335372292893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19704769520482223581528595 29557154280723335372292893)
            ·
              refine ⟨11083932855271250764609835, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29557154280723335372292893 11083932855271250764609835)
              ·
                refine ⟨16625899282906876146914753, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11083932855271250764609835 16625899282906876146914753)
                ·
                  refine ⟨12469424462180157110186065, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16625899282906876146914753 12469424462180157110186065)
                  ·
                    refine ⟨9352068346635117832639549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12469424462180157110186065 9352068346635117832639549)
                    ·
                      refine ⟨3507025629988169187239831, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352068346635117832639549 3507025629988169187239831)
                      ·
                        rfl

theorem cell23_6829908_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 1, 3, 1, 3, 1, 2, 2, 3].length) (baseStart_6829908 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829908 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829908 prefixEnd_6829908 := by exact prefixLift 6829908
  have htrace : WordTrace (prefixWord ++ tailWord_6829908) baseStart_6829908 baseEnd_6829908 := by
    simpa [prefixWord, tailWord_6829908, baseEnd_6829908] using wordTrace_append hprefix tailTrace_6829908
  have hstable : (prefixWord ++ tailWord_6829908).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829908).length < 2 ^ (prefixWord ++ tailWord_6829908).sum := by decide
  have hdescent : baseEnd_6829908 < baseStart_6829908 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829908) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829921 : List Nat := [1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 3]
def baseStart_6829921 : Nat := 118140960795 + 6829921 * 2 ^ 59
def prefixEnd_6829921 : Nat := 4983230072969 + 3 ^ 40 * 6829921 * 2
def baseEnd_6829921 : Nat := 3507032305236677636377271

theorem tailTrace_6829921 : CollatzResearch.WordTrace tailWord_6829921 prefixEnd_6829921 3507032305236677636377271 := by
  unfold tailWord_6829921
  simp only [CollatzResearch.WordTrace]
  refine ⟨249107683889370149485473617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166071789259580099656982411 249107683889370149485473617)
  ·
    refine ⟨186830762917027612114105213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249107683889370149485473617 186830762917027612114105213)
    ·
      refine ⟨70061536093885354542789455, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186830762917027612114105213 70061536093885354542789455)
      ·
        refine ⟨105092304140828031814184183, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70061536093885354542789455 105092304140828031814184183)
        ·
          refine ⟨157638456211242047721276275, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105092304140828031814184183 157638456211242047721276275)
          ·
            refine ⟨236457684316863071581914413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157638456211242047721276275 236457684316863071581914413)
            ·
              refine ⟨88671631618823651843217905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236457684316863071581914413 88671631618823651843217905)
              ·
                refine ⟨66503723714117738882413429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88671631618823651843217905 66503723714117738882413429)
                ·
                  refine ⟨6234724098198538020226259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66503723714117738882413429 6234724098198538020226259)
                  ·
                    refine ⟨9352086147297807030339389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6234724098198538020226259 9352086147297807030339389)
                    ·
                      refine ⟨3507032305236677636377271, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352086147297807030339389 3507032305236677636377271)
                      ·
                        rfl

theorem cell23_6829921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 1, 3, 2, 5, 1, 3].length) (baseStart_6829921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829921 prefixEnd_6829921 := by exact prefixLift 6829921
  have htrace : WordTrace (prefixWord ++ tailWord_6829921) baseStart_6829921 baseEnd_6829921 := by
    simpa [prefixWord, tailWord_6829921, baseEnd_6829921] using wordTrace_append hprefix tailTrace_6829921
  have hstable : (prefixWord ++ tailWord_6829921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829921).length < 2 ^ (prefixWord ++ tailWord_6829921).sum := by decide
  have hdescent : baseEnd_6829921 < baseStart_6829921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829931 : List Nat := [1, 1, 1, 1, 2, 2, 3, 3, 4, 3, 2]
def baseStart_6829931 : Nat := 118140960795 + 6829931 * 2 ^ 59
def prefixEnd_6829931 : Nat := 4983230072969 + 3 ^ 40 * 6829931 * 2
def baseEnd_6829931 : Nat := 3507037440043222597252225

theorem tailTrace_6829931 : CollatzResearch.WordTrace tailWord_6829931 prefixEnd_6829931 3507037440043222597252225 := by
  unfold tailWord_6829931
  simp only [CollatzResearch.WordTrace]
  refine ⟨249108048619333921193337647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166072032412889280795558431 249108048619333921193337647)
  ·
    refine ⟨373662072929000881790006471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249108048619333921193337647 373662072929000881790006471)
    ·
      refine ⟨560493109393501322685009707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373662072929000881790006471 560493109393501322685009707)
      ·
        refine ⟨840739664090251984027514561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560493109393501322685009707 840739664090251984027514561)
        ·
          refine ⟨630554748067688988020635921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840739664090251984027514561 630554748067688988020635921)
          ·
            refine ⟨472916061050766741015476941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630554748067688988020635921 472916061050766741015476941)
            ·
              refine ⟨177343522894037527880803853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472916061050766741015476941 177343522894037527880803853)
              ·
                refine ⟨66503821085264072955301445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177343522894037527880803853 66503821085264072955301445)
                ·
                  refine ⟨12469466453487013679119021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66503821085264072955301445 12469466453487013679119021)
                  ·
                    refine ⟨4676049920057630129669633, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12469466453487013679119021 4676049920057630129669633)
                    ·
                      refine ⟨3507037440043222597252225, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676049920057630129669633 3507037440043222597252225)
                      ·
                        rfl

theorem cell23_6829931_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 2, 3, 3, 4, 3, 2].length) (baseStart_6829931 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829931 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829931 prefixEnd_6829931 := by exact prefixLift 6829931
  have htrace : WordTrace (prefixWord ++ tailWord_6829931) baseStart_6829931 baseEnd_6829931 := by
    simpa [prefixWord, tailWord_6829931, baseEnd_6829931] using wordTrace_append hprefix tailTrace_6829931
  have hstable : (prefixWord ++ tailWord_6829931).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829931).length < 2 ^ (prefixWord ++ tailWord_6829931).sum := by decide
  have hdescent : baseEnd_6829931 < baseStart_6829931 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829931) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829961 : List Nat := [1, 2, 1, 1, 5, 1, 1, 1, 2, 6, 2]
def baseStart_6829961 : Nat := 118140960795 + 6829961 * 2 ^ 59
def prefixEnd_6829961 : Nat := 4983230072969 + 3 ^ 40 * 6829961 * 2
def baseEnd_6829961 : Nat := 3507052844462857479877087

theorem tailTrace_6829961 : CollatzResearch.WordTrace tailWord_6829961 prefixEnd_6829961 3507052844462857479877087 := by
  unfold tailWord_6829961
  simp only [CollatzResearch.WordTrace]
  refine ⟨249109142809225236316929737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166072761872816824211286491 249109142809225236316929737)
  ·
    refine ⟨186831857106918927237697303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249109142809225236316929737 186831857106918927237697303)
    ·
      refine ⟨280247785660378390856545955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186831857106918927237697303 280247785660378390856545955)
      ·
        refine ⟨420371678490567586284818933, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280247785660378390856545955 420371678490567586284818933)
        ·
          refine ⟨39409844858490711214201775, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 420371678490567586284818933 39409844858490711214201775)
          ·
            refine ⟨59114767287736066821302663, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39409844858490711214201775 59114767287736066821302663)
            ·
              refine ⟨88672150931604100231953995, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59114767287736066821302663 88672150931604100231953995)
              ·
                refine ⟨133008226397406150347930993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88672150931604100231953995 133008226397406150347930993)
                ·
                  refine ⟨99756169798054612760948245, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133008226397406150347930993 99756169798054612760948245)
                  ·
                    refine ⟨4676070459283809973169449, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99756169798054612760948245 4676070459283809973169449)
                    ·
                      refine ⟨3507052844462857479877087, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676070459283809973169449 3507052844462857479877087)
                      ·
                        rfl

theorem cell23_6829961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 1, 1, 1, 2, 6, 2].length) (baseStart_6829961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829961 prefixEnd_6829961 := by exact prefixLift 6829961
  have htrace : WordTrace (prefixWord ++ tailWord_6829961) baseStart_6829961 baseEnd_6829961 := by
    simpa [prefixWord, tailWord_6829961, baseEnd_6829961] using wordTrace_append hprefix tailTrace_6829961
  have hstable : (prefixWord ++ tailWord_6829961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829961).length < 2 ^ (prefixWord ++ tailWord_6829961).sum := by decide
  have hdescent : baseEnd_6829961 < baseStart_6829961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829964 : List Nat := [2, 2, 1, 2, 1, 2, 1, 1, 5, 1, 5]
def baseStart_6829964 : Nat := 118140960795 + 6829964 * 2 ^ 59
def prefixEnd_6829964 : Nat := 4983230072969 + 3 ^ 40 * 6829964 * 2
def baseEnd_6829964 : Nat := 3507054384904820968139573

theorem tailTrace_6829964 : CollatzResearch.WordTrace tailWord_6829964 prefixEnd_6829964 3507054384904820968139573 := by
  unfold tailWord_6829964
  simp only [CollatzResearch.WordTrace]
  refine ⟨124554626114107183914644473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166072834818809578552859297 124554626114107183914644473)
  ·
    refine ⟨93415969585580387935983355, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124554626114107183914644473 93415969585580387935983355)
    ·
      refine ⟨140123954378370581903975033, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93415969585580387935983355 140123954378370581903975033)
      ·
        refine ⟨105092965783777936427981275, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140123954378370581903975033 105092965783777936427981275)
        ·
          refine ⟨157639448675666904641971913, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105092965783777936427981275 157639448675666904641971913)
          ·
            refine ⟨118229586506750178481478935, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157639448675666904641971913 118229586506750178481478935)
            ·
              refine ⟨177344379760125267722218403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118229586506750178481478935 177344379760125267722218403)
              ·
                refine ⟨266016569640187901583327605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177344379760125267722218403 266016569640187901583327605)
                ·
                  refine ⟨24939053403767615773436963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266016569640187901583327605 24939053403767615773436963)
                  ·
                    refine ⟨37408580105651423660155445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24939053403767615773436963 37408580105651423660155445)
                    ·
                      refine ⟨3507054384904820968139573, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37408580105651423660155445 3507054384904820968139573)
                      ·
                        rfl

theorem cell23_6829964_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 1, 2, 1, 1, 5, 1, 5].length) (baseStart_6829964 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829964 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829964 prefixEnd_6829964 := by exact prefixLift 6829964
  have htrace : WordTrace (prefixWord ++ tailWord_6829964) baseStart_6829964 baseEnd_6829964 := by
    simpa [prefixWord, tailWord_6829964, baseEnd_6829964] using wordTrace_append hprefix tailTrace_6829964
  have hstable : (prefixWord ++ tailWord_6829964).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829964).length < 2 ^ (prefixWord ++ tailWord_6829964).sum := by decide
  have hdescent : baseEnd_6829964 < baseStart_6829964 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829964) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829972 : List Nat := [2, 4, 2, 1, 1, 2, 3, 3, 1, 1, 3]
def baseStart_6829972 : Nat := 118140960795 + 6829972 * 2 ^ 59
def prefixEnd_6829972 : Nat := 4983230072969 + 3 ^ 40 * 6829972 * 2
def baseEnd_6829972 : Nat := 3507058492750056936839537

theorem tailTrace_6829972 : CollatzResearch.WordTrace tailWord_6829972 prefixEnd_6829972 3507058492750056936839537 := by
  unfold tailWord_6829972
  simp only [CollatzResearch.WordTrace]
  refine ⟨124554772006092692597790085, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166073029341456923463720113 124554772006092692597790085)
  ·
    refine ⟨23354019751142379862085641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124554772006092692597790085 23354019751142379862085641)
    ·
      refine ⟨17515514813356784896564231, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23354019751142379862085641 17515514813356784896564231)
      ·
        refine ⟨26273272220035177344846347, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17515514813356784896564231 26273272220035177344846347)
        ·
          refine ⟨39409908330052766017269521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26273272220035177344846347 39409908330052766017269521)
          ·
            refine ⟨29557431247539574512952141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39409908330052766017269521 29557431247539574512952141)
            ·
              refine ⟨11084036717827340442357053, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29557431247539574512952141 11084036717827340442357053)
              ·
                refine ⟨4156513769185252665883895, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11084036717827340442357053 4156513769185252665883895)
                ·
                  refine ⟨6234770653777878998825843, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156513769185252665883895 6234770653777878998825843)
                  ·
                    refine ⟨9352155980666818498238765, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6234770653777878998825843 9352155980666818498238765)
                    ·
                      refine ⟨3507058492750056936839537, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352155980666818498238765 3507058492750056936839537)
                      ·
                        rfl

theorem cell23_6829972_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 2, 3, 3, 1, 1, 3].length) (baseStart_6829972 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829972 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829972 prefixEnd_6829972 := by exact prefixLift 6829972
  have htrace : WordTrace (prefixWord ++ tailWord_6829972) baseStart_6829972 baseEnd_6829972 := by
    simpa [prefixWord, tailWord_6829972, baseEnd_6829972] using wordTrace_append hprefix tailTrace_6829972
  have hstable : (prefixWord ++ tailWord_6829972).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829972).length < 2 ^ (prefixWord ++ tailWord_6829972).sum := by decide
  have hdescent : baseEnd_6829972 < baseStart_6829972 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829972) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829978 : List Nat := [3, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4]
def baseStart_6829978 : Nat := 118140960795 + 6829978 * 2 ^ 59
def prefixEnd_6829978 : Nat := 4983230072969 + 3 ^ 40 * 6829978 * 2
def baseEnd_6829978 : Nat := 3507061573633983913364509

theorem tailTrace_6829978 : CollatzResearch.WordTrace tailWord_6829978 prefixEnd_6829978 3507061573633983913364509 := by
  unfold tailWord_6829978
  simp only [CollatzResearch.WordTrace]
  refine ⟨62277440712540912055074647, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166073175233442432146865725 62277440712540912055074647)
  ·
    refine ⟨93416161068811368082611971, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62277440712540912055074647 93416161068811368082611971)
    ·
      refine ⟨140124241603217052123917957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93416161068811368082611971 140124241603217052123917957)
      ·
        refine ⟨26273295300603197273234617, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140124241603217052123917957 26273295300603197273234617)
        ·
          refine ⟨19704971475452397954925963, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26273295300603197273234617 19704971475452397954925963)
          ·
            refine ⟨29557457213178596932388945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19704971475452397954925963 29557457213178596932388945)
            ·
              refine ⟨22168092909883947699291709, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29557457213178596932388945 22168092909883947699291709)
              ·
                refine ⟨8313034841206480387234391, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22168092909883947699291709 8313034841206480387234391)
                ·
                  refine ⟨12469552261809720580851587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313034841206480387234391 12469552261809720580851587)
                  ·
                    refine ⟨18704328392714580871277381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12469552261809720580851587 18704328392714580871277381)
                    ·
                      refine ⟨3507061573633983913364509, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18704328392714580871277381 3507061573633983913364509)
                      ·
                        rfl

theorem cell23_6829978_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 2, 1, 2, 3, 1, 1, 4].length) (baseStart_6829978 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829978 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829978 prefixEnd_6829978 := by exact prefixLift 6829978
  have htrace : WordTrace (prefixWord ++ tailWord_6829978) baseStart_6829978 baseEnd_6829978 := by
    simpa [prefixWord, tailWord_6829978, baseEnd_6829978] using wordTrace_append hprefix tailTrace_6829978
  have hstable : (prefixWord ++ tailWord_6829978).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829978).length < 2 ^ (prefixWord ++ tailWord_6829978).sum := by decide
  have hdescent : baseEnd_6829978 < baseStart_6829978 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829978) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829981 : List Nat := [1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 5]
def baseStart_6829981 : Nat := 118140960795 + 6829981 * 2 ^ 59
def prefixEnd_6829981 : Nat := 4983230072969 + 3 ^ 40 * 6829981 * 2
def baseEnd_6829981 : Nat := 3507063114075947401626995

theorem tailTrace_6829981 : CollatzResearch.WordTrace tailWord_6829981 prefixEnd_6829981 3507063114075947401626995 := by
  unfold tailWord_6829981
  simp only [CollatzResearch.WordTrace]
  refine ⟨249109872269152779732657797, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166073248179435186488438531 249109872269152779732657797)
  ·
    refine ⟨46708101050466146199873337, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249109872269152779732657797 46708101050466146199873337)
    ·
      refine ⟨35031075787849609649905003, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46708101050466146199873337 35031075787849609649905003)
      ·
        refine ⟨52546613681774414474857505, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35031075787849609649905003 52546613681774414474857505)
        ·
          refine ⟨39409960261330810856143129, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52546613681774414474857505 39409960261330810856143129)
          ·
            refine ⟨29557470195998108142107347, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39409960261330810856143129 29557470195998108142107347)
            ·
              refine ⟨44336205293997162213161021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29557470195998108142107347 44336205293997162213161021)
              ·
                refine ⟨16626076985248935829935383, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44336205293997162213161021 16626076985248935829935383)
                ·
                  refine ⟨24939115477873403744903075, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16626076985248935829935383 24939115477873403744903075)
                  ·
                    refine ⟨37408673216810105617354613, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24939115477873403744903075 37408673216810105617354613)
                    ·
                      refine ⟨3507063114075947401626995, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37408673216810105617354613 3507063114075947401626995)
                      ·
                        rfl

theorem cell23_6829981_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 2, 2, 1, 3, 1, 1, 5].length) (baseStart_6829981 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829981 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829981 prefixEnd_6829981 := by exact prefixLift 6829981
  have htrace : WordTrace (prefixWord ++ tailWord_6829981) baseStart_6829981 baseEnd_6829981 := by
    simpa [prefixWord, tailWord_6829981, baseEnd_6829981] using wordTrace_append hprefix tailTrace_6829981
  have hstable : (prefixWord ++ tailWord_6829981).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829981).length < 2 ^ (prefixWord ++ tailWord_6829981).sum := by decide
  have hdescent : baseEnd_6829981 < baseStart_6829981 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829981) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6829991 : List Nat := [1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 6]
def baseStart_6829991 : Nat := 118140960795 + 6829991 * 2 ^ 59
def prefixEnd_6829991 : Nat := 4983230072969 + 3 ^ 40 * 6829991 * 2
def baseEnd_6829991 : Nat := 3507068248882492362501949

theorem tailTrace_6829991 : CollatzResearch.WordTrace tailWord_6829991 prefixEnd_6829991 3507068248882492362501949 := by
  unfold tailWord_6829991
  simp only [CollatzResearch.WordTrace]
  refine ⟨249110236999116551440521827, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166073491332744367627014551 249110236999116551440521827)
  ·
    refine ⟨373665355498674827160782741, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249110236999116551440521827 373665355498674827160782741)
    ·
      refine ⟨17515563539000382523161691, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 373665355498674827160782741 17515563539000382523161691)
      ·
        refine ⟨26273345308500573784742537, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17515563539000382523161691 26273345308500573784742537)
        ·
          refine ⟨19705008981375430338556903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26273345308500573784742537 19705008981375430338556903)
          ·
            refine ⟨29557513472063145507835355, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19705008981375430338556903 29557513472063145507835355)
            ·
              refine ⟨44336270208094718261753033, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29557513472063145507835355 44336270208094718261753033)
              ·
                refine ⟨33252202656071038696314775, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44336270208094718261753033 33252202656071038696314775)
                ·
                  refine ⟨49878303984106558044472163, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33252202656071038696314775 49878303984106558044472163)
                  ·
                    refine ⟨74817455976159837066708245, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49878303984106558044472163 74817455976159837066708245)
                    ·
                      refine ⟨3507068248882492362501949, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74817455976159837066708245 3507068248882492362501949)
                      ·
                        rfl

theorem cell23_6829991_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 1, 1, 6].length) (baseStart_6829991 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6829991 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6829991 prefixEnd_6829991 := by exact prefixLift 6829991
  have htrace : WordTrace (prefixWord ++ tailWord_6829991) baseStart_6829991 baseEnd_6829991 := by
    simpa [prefixWord, tailWord_6829991, baseEnd_6829991] using wordTrace_append hprefix tailTrace_6829991
  have hstable : (prefixWord ++ tailWord_6829991).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6829991).length < 2 ^ (prefixWord ++ tailWord_6829991).sum := by decide
  have hdescent : baseEnd_6829991 < baseStart_6829991 := by decide
  rcases family_descends (prefixWord ++ tailWord_6829991) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830001 : List Nat := [1, 2, 2, 4, 2, 2, 2, 8]
def baseStart_6830001 : Nat := 118140960795 + 6830001 * 2 ^ 59
def prefixEnd_6830001 : Nat := 4983230072969 + 3 ^ 40 * 6830001 * 2
def baseEnd_6830001 : Nat := 129891606803297678643589

theorem tailTrace_6830001 : CollatzResearch.WordTrace tailWord_6830001 prefixEnd_6830001 129891606803297678643589 := by
  unfold tailWord_6830001
  simp only [CollatzResearch.WordTrace]
  refine ⟨249110601729080323148385857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166073734486053548765590571 249110601729080323148385857)
  ·
    refine ⟨186832951296810242361289393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249110601729080323148385857 186832951296810242361289393)
    ·
      refine ⟨140124713472607681770967045, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186832951296810242361289393 140124713472607681770967045)
      ·
        refine ⟨26273383776113940332056321, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140124713472607681770967045 26273383776113940332056321)
        ·
          refine ⟨19705037832085455249042241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26273383776113940332056321 19705037832085455249042241)
          ·
            refine ⟨14778778374064091436781681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19705037832085455249042241 14778778374064091436781681)
            ·
              refine ⟨11084083780548068577586261, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14778778374064091436781681 11084083780548068577586261)
              ·
                refine ⟨129891606803297678643589, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11084083780548068577586261 129891606803297678643589)
                ·
                  rfl

theorem cell23_6830001_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 2, 2, 2, 8].length) (baseStart_6830001 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830001 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830001 prefixEnd_6830001 := by exact prefixLift 6830001
  have htrace : WordTrace (prefixWord ++ tailWord_6830001) baseStart_6830001 baseEnd_6830001 := by
    simpa [prefixWord, tailWord_6830001, baseEnd_6830001] using wordTrace_append hprefix tailTrace_6830001
  have hstable : (prefixWord ++ tailWord_6830001).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830001).length < 2 ^ (prefixWord ++ tailWord_6830001).sum := by decide
  have hdescent : baseEnd_6830001 < baseStart_6830001 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830001) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830005 : List Nat := [1, 3, 3, 2, 1, 2, 4, 1, 2, 4]
def baseStart_6830005 : Nat := 118140960795 + 6830005 * 2 ^ 59
def prefixEnd_6830005 : Nat := 4983230072969 + 3 ^ 40 * 6830005 * 2
def baseEnd_6830005 : Nat := 1169025145870551769242295

theorem tailTrace_6830005 : CollatzResearch.WordTrace tailWord_6830005 prefixEnd_6830005 1169025145870551769242295 := by
  unfold tailWord_6830005
  simp only [CollatzResearch.WordTrace]
  refine ⟨249110747621065831831531469, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166073831747377221221020979 249110747621065831831531469)
  ·
    refine ⟨93416530357899686936824301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249110747621065831831531469 93416530357899686936824301)
    ·
      refine ⟨35031198884212382601309113, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93416530357899686936824301 35031198884212382601309113)
      ·
        refine ⟨26273399163159286950981835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35031198884212382601309113 26273399163159286950981835)
        ·
          refine ⟨39410098744738930426472753, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26273399163159286950981835 39410098744738930426472753)
          ·
            refine ⟨29557574058554197819854565, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39410098744738930426472753 29557574058554197819854565)
            ·
              refine ⟨5542045135978912091222731, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29557574058554197819854565 5542045135978912091222731)
              ·
                refine ⟨8313067703968368136834097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542045135978912091222731 8313067703968368136834097)
                ·
                  refine ⟨6234800777976276102625573, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8313067703968368136834097 6234800777976276102625573)
                  ·
                    refine ⟨1169025145870551769242295, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6234800777976276102625573 1169025145870551769242295)
                    ·
                      rfl

theorem cell23_6830005_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 1, 2, 4, 1, 2, 4].length) (baseStart_6830005 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830005 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830005 prefixEnd_6830005 := by exact prefixLift 6830005
  have htrace : WordTrace (prefixWord ++ tailWord_6830005) baseStart_6830005 baseEnd_6830005 := by
    simpa [prefixWord, tailWord_6830005, baseEnd_6830005] using wordTrace_append hprefix tailTrace_6830005
  have hstable : (prefixWord ++ tailWord_6830005).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830005).length < 2 ^ (prefixWord ++ tailWord_6830005).sum := by decide
  have hdescent : baseEnd_6830005 < baseStart_6830005 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830005) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830012 : List Nat := [2, 2, 2, 5, 1, 2, 1, 2, 1, 1, 4]
def baseStart_6830012 : Nat := 118140960795 + 6830012 * 2 ^ 59
def prefixEnd_6830012 : Nat := 4983230072969 + 3 ^ 40 * 6830012 * 2
def baseEnd_6830012 : Nat := 3507079031976236780339353

theorem tailTrace_6830012 : CollatzResearch.WordTrace tailWord_6830012 prefixEnd_6830012 3507079031976236780339353 := by
  unfold tailWord_6830012
  simp only [CollatzResearch.WordTrace]
  refine ⟨124555501466020236013518145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166074001954693648018024193 124555501466020236013518145)
  ·
    refine ⟨93416626099515177010138609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124555501466020236013518145 93416626099515177010138609)
    ·
      refine ⟨70062469574636382757603957, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93416626099515177010138609 70062469574636382757603957)
      ·
        refine ⟨6568356522622160883525371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70062469574636382757603957 6568356522622160883525371)
        ·
          refine ⟨9852534783933241325288057, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568356522622160883525371 9852534783933241325288057)
          ·
            refine ⟨7389401087949930993966043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9852534783933241325288057 7389401087949930993966043)
            ·
              refine ⟨11084101631924896490949065, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7389401087949930993966043 11084101631924896490949065)
              ·
                refine ⟨8313076223943672368211799, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11084101631924896490949065 8313076223943672368211799)
                ·
                  refine ⟨12469614335915508552317699, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313076223943672368211799 12469614335915508552317699)
                  ·
                    refine ⟨18704421503873262828476549, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12469614335915508552317699 18704421503873262828476549)
                    ·
                      refine ⟨3507079031976236780339353, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18704421503873262828476549 3507079031976236780339353)
                      ·
                        rfl

theorem cell23_6830012_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 5, 1, 2, 1, 2, 1, 1, 4].length) (baseStart_6830012 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830012 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830012 prefixEnd_6830012 := by exact prefixLift 6830012
  have htrace : WordTrace (prefixWord ++ tailWord_6830012) baseStart_6830012 baseEnd_6830012 := by
    simpa [prefixWord, tailWord_6830012, baseEnd_6830012] using wordTrace_append hprefix tailTrace_6830012
  have hstable : (prefixWord ++ tailWord_6830012).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830012).length < 2 ^ (prefixWord ++ tailWord_6830012).sum := by decide
  have hdescent : baseEnd_6830012 < baseStart_6830012 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830012) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830028 : List Nat := [2, 2, 1, 4, 1, 3, 1, 2, 1, 3, 3]
def baseStart_6830028 : Nat := 118140960795 + 6830028 * 2 ^ 59
def prefixEnd_6830028 : Nat := 4983230072969 + 3 ^ 40 * 6830028 * 2
def baseEnd_6830028 : Nat := 3507087247666708717739279

theorem tailTrace_6830028 : CollatzResearch.WordTrace tailWord_6830028 prefixEnd_6830028 3507087247666708717739279 := by
  unfold tailWord_6830028
  simp only [CollatzResearch.WordTrace]
  refine ⟨124555793249991253379809369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166074390999988337839745825 124555793249991253379809369)
  ·
    refine ⟨93416844937493440034857027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124555793249991253379809369 93416844937493440034857027)
    ·
      refine ⟨140125267406240160052285541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93416844937493440034857027 140125267406240160052285541)
      ·
        refine ⟨26273487638670030009803539, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140125267406240160052285541 26273487638670030009803539)
        ·
          refine ⟨39410231458005045014705309, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26273487638670030009803539 39410231458005045014705309)
          ·
            refine ⟨14778836796751891880514491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39410231458005045014705309 14778836796751891880514491)
            ·
              refine ⟨22168255195127837820771737, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14778836796751891880514491 22168255195127837820771737)
              ·
                refine ⟨16626191396345878365578803, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22168255195127837820771737 16626191396345878365578803)
                ·
                  refine ⟨24939287094518817548368205, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16626191396345878365578803 24939287094518817548368205)
                  ·
                    refine ⟨9352232660444556580638077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24939287094518817548368205 9352232660444556580638077)
                    ·
                      refine ⟨3507087247666708717739279, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352232660444556580638077 3507087247666708717739279)
                      ·
                        rfl

theorem cell23_6830028_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 4, 1, 3, 1, 2, 1, 3, 3].length) (baseStart_6830028 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830028 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830028 prefixEnd_6830028 := by exact prefixLift 6830028
  have htrace : WordTrace (prefixWord ++ tailWord_6830028) baseStart_6830028 baseEnd_6830028 := by
    simpa [prefixWord, tailWord_6830028, baseEnd_6830028] using wordTrace_append hprefix tailTrace_6830028
  have hstable : (prefixWord ++ tailWord_6830028).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830028).length < 2 ^ (prefixWord ++ tailWord_6830028).sum := by decide
  have hdescent : baseEnd_6830028 < baseStart_6830028 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830028) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830051 : List Nat := [1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6830051 : Nat := 118140960795 + 6830051 * 2 ^ 59
def prefixEnd_6830051 : Nat := 4983230072969 + 3 ^ 40 * 6830051 * 2
def baseEnd_6830051 : Nat := 3507099057721762127751673

theorem tailTrace_6830051 : CollatzResearch.WordTrace tailWord_6830051 prefixEnd_6830051 3507099057721762127751673 := by
  unfold tailWord_6830051
  simp only [CollatzResearch.WordTrace]
  refine ⟨249112425378899181687706007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166074950252599454458470671 249112425378899181687706007)
  ·
    refine ⟨373668638068348772531559011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249112425378899181687706007 373668638068348772531559011)
    ·
      refine ⟨560502957102523158797338517, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373668638068348772531559011 560502957102523158797338517)
      ·
        refine ⟨26273576114180773068625243, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 560502957102523158797338517 26273576114180773068625243)
        ·
          refine ⟨39410364171271159602937865, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26273576114180773068625243 39410364171271159602937865)
          ·
            refine ⟨29557773128453369702203399, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39410364171271159602937865 29557773128453369702203399)
            ·
              refine ⟨44336659692680054553305099, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29557773128453369702203399 44336659692680054553305099)
              ·
                refine ⟨66504989539020081829957649, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44336659692680054553305099 66504989539020081829957649)
                ·
                  refine ⟨49878742154265061372468237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66504989539020081829957649 49878742154265061372468237)
                  ·
                    refine ⟨18704528307849398014675589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49878742154265061372468237 18704528307849398014675589)
                    ·
                      refine ⟨3507099057721762127751673, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18704528307849398014675589 3507099057721762127751673)
                      ·
                        rfl

theorem cell23_6830051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6830051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830051 prefixEnd_6830051 := by exact prefixLift 6830051
  have htrace : WordTrace (prefixWord ++ tailWord_6830051) baseStart_6830051 baseEnd_6830051 := by
    simpa [prefixWord, tailWord_6830051, baseEnd_6830051] using wordTrace_append hprefix tailTrace_6830051
  have hstable : (prefixWord ++ tailWord_6830051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830051).length < 2 ^ (prefixWord ++ tailWord_6830051).sum := by decide
  have hdescent : baseEnd_6830051 < baseStart_6830051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830081 : List Nat := [1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 4]
def baseStart_6830081 : Nat := 118140960795 + 6830081 * 2 ^ 59
def prefixEnd_6830081 : Nat := 4983230072969 + 3 ^ 40 * 6830081 * 2
def baseEnd_6830081 : Nat := 3507114462141397010376535

theorem tailTrace_6830081 : CollatzResearch.WordTrace tailWord_6830081 prefixEnd_6830081 3507114462141397010376535 := by
  unfold tailWord_6830081
  simp only [CollatzResearch.WordTrace]
  refine ⟨249113519568790496811298097, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166075679712526997874198731 249113519568790496811298097)
  ·
    refine ⟨186835139676592872608473573, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249113519568790496811298097 186835139676592872608473573)
    ·
      refine ⟨35031588689361163614088795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186835139676592872608473573 35031588689361163614088795)
      ·
        refine ⟨52547383034041745421133193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35031588689361163614088795 52547383034041745421133193)
        ·
          refine ⟨39410537275531309065849895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52547383034041745421133193 39410537275531309065849895)
          ·
            refine ⟨59115805913296963598774843, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39410537275531309065849895 59115805913296963598774843)
            ·
              refine ⟨88673708869945445398162265, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59115805913296963598774843 88673708869945445398162265)
              ·
                refine ⟨66505281652459084048621699, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88673708869945445398162265 66505281652459084048621699)
                ·
                  refine ⟨99757922478688626072932549, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66505281652459084048621699 99757922478688626072932549)
                  ·
                    refine ⟨18704610464754117388674853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99757922478688626072932549 18704610464754117388674853)
                    ·
                      refine ⟨3507114462141397010376535, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18704610464754117388674853 3507114462141397010376535)
                      ·
                        rfl

theorem cell23_6830081_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 2, 1, 1, 2, 1, 4, 4].length) (baseStart_6830081 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830081 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830081 prefixEnd_6830081 := by exact prefixLift 6830081
  have htrace : WordTrace (prefixWord ++ tailWord_6830081) baseStart_6830081 baseEnd_6830081 := by
    simpa [prefixWord, tailWord_6830081, baseEnd_6830081] using wordTrace_append hprefix tailTrace_6830081
  have hstable : (prefixWord ++ tailWord_6830081).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830081).length < 2 ^ (prefixWord ++ tailWord_6830081).sum := by decide
  have hdescent : baseEnd_6830081 < baseStart_6830081 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830081) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830108 : List Nat := [2, 2, 3, 1, 3, 2, 2, 1, 7]
def baseStart_6830108 : Nat := 118140960795 + 6830108 * 2 ^ 59
def prefixEnd_6830108 : Nat := 4983230072969 + 3 ^ 40 * 6830108 * 2
def baseEnd_6830108 : Nat := 389680925124340933859879

theorem tailTrace_6830108 : CollatzResearch.WordTrace tailWord_6830108 prefixEnd_6830108 389680925124340933859879 := by
  unfold tailWord_6830108
  simp only [CollatzResearch.WordTrace]
  refine ⟨124557252169846340211265489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166076336226461786948353985 124557252169846340211265489)
  ·
    refine ⟨93417939127384755158449117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124557252169846340211265489 93417939127384755158449117)
    ·
      refine ⟨35031727172769283184418419, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93417939127384755158449117 35031727172769283184418419)
      ·
        refine ⟨52547590759153924776627629, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35031727172769283184418419 52547590759153924776627629)
        ·
          refine ⟨19705346534682721791235361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52547590759153924776627629 19705346534682721791235361)
          ·
            refine ⟨14779009901012041343426521, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19705346534682721791235361 14779009901012041343426521)
            ·
              refine ⟨11084257425759031007569891, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14779009901012041343426521 11084257425759031007569891)
              ·
                refine ⟨16626386138638546511354837, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11084257425759031007569891 16626386138638546511354837)
                ·
                  refine ⟨389680925124340933859879, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16626386138638546511354837 389680925124340933859879)
                  ·
                    rfl

theorem cell23_6830108_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 3, 2, 2, 1, 7].length) (baseStart_6830108 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830108 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830108 prefixEnd_6830108 := by exact prefixLift 6830108
  have htrace : WordTrace (prefixWord ++ tailWord_6830108) baseStart_6830108 baseEnd_6830108 := by
    simpa [prefixWord, tailWord_6830108, baseEnd_6830108] using wordTrace_append hprefix tailTrace_6830108
  have hstable : (prefixWord ++ tailWord_6830108).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830108).length < 2 ^ (prefixWord ++ tailWord_6830108).sum := by decide
  have hdescent : baseEnd_6830108 < baseStart_6830108 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830108) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830119 : List Nat := [1, 1, 7, 1, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6830119 : Nat := 118140960795 + 6830119 * 2 ^ 59
def prefixEnd_6830119 : Nat := 4983230072969 + 3 ^ 40 * 6830119 * 2
def baseEnd_6830119 : Nat := 3507133974406267861701361

theorem tailTrace_6830119 : CollatzResearch.WordTrace tailWord_6830119 prefixEnd_6830119 3507133974406267861701361 := by
  unfold tailWord_6830119
  simp only [CollatzResearch.WordTrace]
  refine ⟨249114905542652829301181411, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166076603695101886200787607 249114905542652829301181411)
  ·
    refine ⟨373672358313979243951772117, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249114905542652829301181411 373672358313979243951772117)
    ·
      refine ⟨8757945897983888530119659, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 373672358313979243951772117 8757945897983888530119659)
      ·
        refine ⟨13136918846975832795179489, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8757945897983888530119659 13136918846975832795179489)
        ·
          refine ⟨9852689135231874596384617, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13136918846975832795179489 9852689135231874596384617)
          ·
            refine ⟨7389516851423905947288463, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9852689135231874596384617 7389516851423905947288463)
            ·
              refine ⟨11084275277135858920932695, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7389516851423905947288463 11084275277135858920932695)
              ·
                refine ⟨16626412915703788381399043, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11084275277135858920932695 16626412915703788381399043)
                ·
                  refine ⟨24939619373555682572098565, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16626412915703788381399043 24939619373555682572098565)
                  ·
                    refine ⟨4676178632541690482268481, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24939619373555682572098565 4676178632541690482268481)
                    ·
                      refine ⟨3507133974406267861701361, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676178632541690482268481 3507133974406267861701361)
                      ·
                        rfl

theorem cell23_6830119_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6830119 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830119 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830119 prefixEnd_6830119 := by exact prefixLift 6830119
  have htrace : WordTrace (prefixWord ++ tailWord_6830119) baseStart_6830119 baseEnd_6830119 := by
    simpa [prefixWord, tailWord_6830119, baseEnd_6830119] using wordTrace_append hprefix tailTrace_6830119
  have hstable : (prefixWord ++ tailWord_6830119).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830119).length < 2 ^ (prefixWord ++ tailWord_6830119).sum := by decide
  have hdescent : baseEnd_6830119 < baseStart_6830119 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830119) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830158 : List Nat := [4, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4]
def baseStart_6830158 : Nat := 118140960795 + 6830158 * 2 ^ 59
def prefixEnd_6830158 : Nat := 4983230072969 + 3 ^ 40 * 6830158 * 2
def baseEnd_6830158 : Nat := 3507154000151793209113681

theorem tailTrace_6830158 : CollatzResearch.WordTrace tailWord_6830158 prefixEnd_6830158 3507154000151793209113681 := by
  unfold tailWord_6830158
  simp only [CollatzResearch.WordTrace]
  refine ⟨31139540998688942370231391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166077551993007692641234085 31139540998688942370231391)
  ·
    refine ⟨46709311498033413555347087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31139540998688942370231391 46709311498033413555347087)
    ·
      refine ⟨70063967247050120333020631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46709311498033413555347087 70063967247050120333020631)
      ·
        refine ⟨105095950870575180499530947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70063967247050120333020631 105095950870575180499530947)
        ·
          refine ⟨157643926305862770749296421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105095950870575180499530947 157643926305862770749296421)
          ·
            refine ⟨29558236182349269515493079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157643926305862770749296421 29558236182349269515493079)
            ·
              refine ⟨44337354273523904273239619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29558236182349269515493079 44337354273523904273239619)
              ·
                refine ⟨66506031410285856409859429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44337354273523904273239619 66506031410285856409859429)
                ·
                  refine ⟨12469880889428598076848643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66506031410285856409859429 12469880889428598076848643)
                  ·
                    refine ⟨18704821334142897115272965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12469880889428598076848643 18704821334142897115272965)
                    ·
                      refine ⟨3507154000151793209113681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18704821334142897115272965 3507154000151793209113681)
                      ·
                        rfl

theorem cell23_6830158_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 4, 1, 1, 4, 1, 4].length) (baseStart_6830158 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830158 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830158 prefixEnd_6830158 := by exact prefixLift 6830158
  have htrace : WordTrace (prefixWord ++ tailWord_6830158) baseStart_6830158 baseEnd_6830158 := by
    simpa [prefixWord, tailWord_6830158, baseEnd_6830158] using wordTrace_append hprefix tailTrace_6830158
  have hstable : (prefixWord ++ tailWord_6830158).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830158).length < 2 ^ (prefixWord ++ tailWord_6830158).sum := by decide
  have hdescent : baseEnd_6830158 < baseStart_6830158 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830158) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830242 : List Nat := [3, 3, 1, 3, 1, 1, 1, 1, 5, 1, 3]
def baseStart_6830242 : Nat := 118140960795 + 6830242 * 2 ^ 59
def prefixEnd_6830242 : Nat := 4983230072969 + 3 ^ 40 * 6830242 * 2
def baseEnd_6830242 : Nat := 3507197132526770880463295

theorem tailTrace_6830242 : CollatzResearch.WordTrace tailWord_6830242 prefixEnd_6830242 3507197132526770880463295 := by
  unfold tailWord_6830242
  simp only [CollatzResearch.WordTrace]
  refine ⟨62279847930301805326977245, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166079594480804814205272653 62279847930301805326977245)
  ·
    refine ⟨23354942973863176997616467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62279847930301805326977245 23354942973863176997616467)
    ·
      refine ⟨35032414460794765496424701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23354942973863176997616467 35032414460794765496424701)
      ·
        refine ⟨13137155422798037061159263, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35032414460794765496424701 13137155422798037061159263)
        ·
          refine ⟨19705733134197055591738895, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13137155422798037061159263 19705733134197055591738895)
          ·
            refine ⟨29558599701295583387608343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19705733134197055591738895 29558599701295583387608343)
            ·
              refine ⟨44337899551943375081412515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29558599701295583387608343 44337899551943375081412515)
              ·
                refine ⟨66506849327915062622118773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44337899551943375081412515 66506849327915062622118773)
                ·
                  refine ⟨6235017124492037120823635, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66506849327915062622118773 6235017124492037120823635)
                  ·
                    refine ⟨9352525686738055681235453, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6235017124492037120823635 9352525686738055681235453)
                    ·
                      refine ⟨3507197132526770880463295, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352525686738055681235453 3507197132526770880463295)
                      ·
                        rfl

theorem cell23_6830242_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 3, 1, 1, 1, 1, 5, 1, 3].length) (baseStart_6830242 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830242 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830242 prefixEnd_6830242 := by exact prefixLift 6830242
  have htrace : WordTrace (prefixWord ++ tailWord_6830242) baseStart_6830242 baseEnd_6830242 := by
    simpa [prefixWord, tailWord_6830242, baseEnd_6830242] using wordTrace_append hprefix tailTrace_6830242
  have hstable : (prefixWord ++ tailWord_6830242).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830242).length < 2 ^ (prefixWord ++ tailWord_6830242).sum := by decide
  have hdescent : baseEnd_6830242 < baseStart_6830242 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830242) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830258 : List Nat := [3, 2, 1, 1, 1, 3, 1, 4, 1, 6]
def baseStart_6830258 : Nat := 118140960795 + 6830258 * 2 ^ 59
def prefixEnd_6830258 : Nat := 4983230072969 + 3 ^ 40 * 6830258 * 2
def baseEnd_6830258 : Nat := 1169068449405747605954407

theorem tailTrace_6830258 : CollatzResearch.WordTrace tailWord_6830258 prefixEnd_6830258 1169068449405747605954407 := by
  unfold tailWord_6830258
  simp only [CollatzResearch.WordTrace]
  refine ⟨62279993822287314010122857, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166079983526099504026994285 62279993822287314010122857)
  ·
    refine ⟨46709995366715485507592143, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62279993822287314010122857 46709995366715485507592143)
    ·
      refine ⟨70064993050073228261388215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46709995366715485507592143 70064993050073228261388215)
      ·
        refine ⟨105097489575109842392082323, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70064993050073228261388215 105097489575109842392082323)
        ·
          refine ⟨157646234362664763588123485, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105097489575109842392082323 157646234362664763588123485)
          ·
            refine ⟨59117337885999286345546307, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157646234362664763588123485 59117337885999286345546307)
            ·
              refine ⟨88676006828998929518319461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59117337885999286345546307 88676006828998929518319461)
              ·
                refine ⟨16626751280437299284684899, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88676006828998929518319461 16626751280437299284684899)
                ·
                  refine ⟨24940126920655948927027349, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16626751280437299284684899 24940126920655948927027349)
                  ·
                    refine ⟨1169068449405747605954407, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24940126920655948927027349 1169068449405747605954407)
                    ·
                      rfl

theorem cell23_6830258_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 3, 1, 4, 1, 6].length) (baseStart_6830258 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830258 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830258 prefixEnd_6830258 := by exact prefixLift 6830258
  have htrace : WordTrace (prefixWord ++ tailWord_6830258) baseStart_6830258 baseEnd_6830258 := by
    simpa [prefixWord, tailWord_6830258, baseEnd_6830258] using wordTrace_append hprefix tailTrace_6830258
  have hstable : (prefixWord ++ tailWord_6830258).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830258).length < 2 ^ (prefixWord ++ tailWord_6830258).sum := by decide
  have hdescent : baseEnd_6830258 < baseStart_6830258 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830258) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830265 : List Nat := [1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 4]
def baseStart_6830265 : Nat := 118140960795 + 6830265 * 2 ^ 59
def prefixEnd_6830265 : Nat := 4983230072969 + 3 ^ 40 * 6830265 * 2
def baseEnd_6830265 : Nat := 3507208942581824290475689

theorem tailTrace_6830265 : CollatzResearch.WordTrace tailWord_6830265 prefixEnd_6830265 3507208942581824290475689 := by
  unfold tailWord_6830265
  simp only [CollatzResearch.WordTrace]
  refine ⟨249120230600123896235996249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166080153733415930823997499 249120230600123896235996249)
  ·
    refine ⟨186840172950092922176997187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249120230600123896235996249 186840172950092922176997187)
    ·
      refine ⟨280260259425139383265495781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186840172950092922176997187 280260259425139383265495781)
      ·
        refine ⟨52548798642213634362280459, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280260259425139383265495781 52548798642213634362280459)
        ·
          refine ⟨78823197963320451543420689, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52548798642213634362280459 78823197963320451543420689)
          ·
            refine ⟨59117398472490338657565517, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78823197963320451543420689 59117398472490338657565517)
            ·
              refine ⟨22169024427183876996587069, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59117398472490338657565517 22169024427183876996587069)
              ·
                refine ⟨8313384160193953873720151, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22169024427183876996587069 8313384160193953873720151)
                ·
                  refine ⟨12470076240290930810580227, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313384160193953873720151 12470076240290930810580227)
                  ·
                    refine ⟨18705114360436396215870341, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12470076240290930810580227 18705114360436396215870341)
                    ·
                      refine ⟨3507208942581824290475689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18705114360436396215870341 3507208942581824290475689)
                      ·
                        rfl

theorem cell23_6830265_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 2, 3, 3, 1, 1, 4].length) (baseStart_6830265 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830265 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830265 prefixEnd_6830265 := by exact prefixLift 6830265
  have htrace : WordTrace (prefixWord ++ tailWord_6830265) baseStart_6830265 baseEnd_6830265 := by
    simpa [prefixWord, tailWord_6830265, baseEnd_6830265] using wordTrace_append hprefix tailTrace_6830265
  have hstable : (prefixWord ++ tailWord_6830265).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830265).length < 2 ^ (prefixWord ++ tailWord_6830265).sum := by decide
  have hdescent : baseEnd_6830265 < baseStart_6830265 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830265) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830315 : List Nat := [1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 3]
def baseStart_6830315 : Nat := 118140960795 + 6830315 * 2 ^ 59
def prefixEnd_6830315 : Nat := 4983230072969 + 3 ^ 40 * 6830315 * 2
def baseEnd_6830315 : Nat := 3507234616614549094850459

theorem tailTrace_6830315 : CollatzResearch.WordTrace tailWord_6830315 prefixEnd_6830315 3507234616614549094850459 := by
  unfold tailWord_6830315
  simp only [CollatzResearch.WordTrace]
  refine ⟨249122054249942754775316399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166081369499961836516877599 249122054249942754775316399)
  ·
    refine ⟨373683081374914132162974599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249122054249942754775316399 373683081374914132162974599)
    ·
      refine ⟨560524622062371198244461899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373683081374914132162974599 560524622062371198244461899)
      ·
        refine ⟨840786933093556797366692849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560524622062371198244461899 840786933093556797366692849)
        ·
          refine ⟨630590199820167598025019637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 840786933093556797366692849 630590199820167598025019637)
          ·
            refine ⟨59117831233140712314845591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 630590199820167598025019637 59117831233140712314845591)
            ·
              refine ⟨88676746849711068472268387, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59117831233140712314845591 88676746849711068472268387)
              ·
                refine ⟨133015120274566602708402581, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88676746849711068472268387 133015120274566602708402581)
                ·
                  refine ⟨6235083762870309501956371, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133015120274566602708402581 6235083762870309501956371)
                  ·
                    refine ⟨9352625644305464252934557, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6235083762870309501956371 9352625644305464252934557)
                    ·
                      refine ⟨3507234616614549094850459, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352625644305464252934557 3507234616614549094850459)
                      ·
                        rfl

theorem cell23_6830315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 2, 5, 1, 1, 6, 1, 3].length) (baseStart_6830315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830315 prefixEnd_6830315 := by exact prefixLift 6830315
  have htrace : WordTrace (prefixWord ++ tailWord_6830315) baseStart_6830315 baseEnd_6830315 := by
    simpa [prefixWord, tailWord_6830315, baseEnd_6830315] using wordTrace_append hprefix tailTrace_6830315
  have hstable : (prefixWord ++ tailWord_6830315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830315).length < 2 ^ (prefixWord ++ tailWord_6830315).sum := by decide
  have hdescent : baseEnd_6830315 < baseStart_6830315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830318 : List Nat := [4, 1, 2, 1, 1, 1, 1, 2, 1, 9]
def baseStart_6830318 : Nat := 118140960795 + 6830318 * 2 ^ 59
def prefixEnd_6830318 : Nat := 4983230072969 + 3 ^ 40 * 6830318 * 2
def baseEnd_6830318 : Nat := 1169078719018837527704315

theorem tailTrace_6830318 : CollatzResearch.WordTrace tailWord_6830318 prefixEnd_6830318 1169078719018837527704315 := by
  unfold tailWord_6830318
  simp only [CollatzResearch.WordTrace]
  refine ⟨31140270458616485785959451, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166081442445954590858450405 31140270458616485785959451)
  ·
    refine ⟨46710405687924728678939177, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31140270458616485785959451 46710405687924728678939177)
    ·
      refine ⟨35032804265943546509204383, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46710405687924728678939177 35032804265943546509204383)
      ·
        refine ⟨52549206398915319763806575, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35032804265943546509204383 52549206398915319763806575)
        ·
          refine ⟨78823809598372979645709863, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52549206398915319763806575 78823809598372979645709863)
          ·
            refine ⟨118235714397559469468564795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78823809598372979645709863 118235714397559469468564795)
            ·
              refine ⟨177353571596339204202847193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118235714397559469468564795 177353571596339204202847193)
              ·
                refine ⟨133015178697254403152135395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177353571596339204202847193 133015178697254403152135395)
                ·
                  refine ⟨199522768045881604728203093, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133015178697254403152135395 199522768045881604728203093)
                  ·
                    refine ⟨1169078719018837527704315, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199522768045881604728203093 1169078719018837527704315)
                    ·
                      rfl

theorem cell23_6830318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 1, 2, 1, 9].length) (baseStart_6830318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830318 prefixEnd_6830318 := by exact prefixLift 6830318
  have htrace : WordTrace (prefixWord ++ tailWord_6830318) baseStart_6830318 baseEnd_6830318 := by
    simpa [prefixWord, tailWord_6830318, baseEnd_6830318] using wordTrace_append hprefix tailTrace_6830318
  have hstable : (prefixWord ++ tailWord_6830318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830318).length < 2 ^ (prefixWord ++ tailWord_6830318).sum := by decide
  have hdescent : baseEnd_6830318 < baseStart_6830318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830332 : List Nat := [2, 2, 2, 1, 4, 1, 2, 1, 4, 1, 3]
def baseStart_6830332 : Nat := 118140960795 + 6830332 * 2 ^ 59
def prefixEnd_6830332 : Nat := 4983230072969 + 3 ^ 40 * 6830332 * 2
def baseEnd_6830332 : Nat := 3507243345785675528337881

theorem tailTrace_6830332 : CollatzResearch.WordTrace tailWord_6830332 prefixEnd_6830332 3507243345785675528337881 := by
  unfold tailWord_6830332
  simp only [CollatzResearch.WordTrace]
  refine ⟨124561337145440583339342625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166081782860587444452456833 124561337145440583339342625)
  ·
    refine ⟨93421002859080437504506969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124561337145440583339342625 93421002859080437504506969)
    ·
      refine ⟨70065752144310328128380227, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93421002859080437504506969 70065752144310328128380227)
      ·
        refine ⟨105098628216465492192570341, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70065752144310328128380227 105098628216465492192570341)
        ·
          refine ⟨19705992790587279786106939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105098628216465492192570341 19705992790587279786106939)
          ·
            refine ⟨29558989185880919679160409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19705992790587279786106939 29558989185880919679160409)
            ·
              refine ⟨22169241889410689759370307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29558989185880919679160409 22169241889410689759370307)
              ·
                refine ⟨33253862834116034639055461, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22169241889410689759370307 33253862834116034639055461)
                ·
                  refine ⟨6235099281396756494822899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33253862834116034639055461 6235099281396756494822899)
                  ·
                    refine ⟨9352648922095134742234349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6235099281396756494822899 9352648922095134742234349)
                    ·
                      refine ⟨3507243345785675528337881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352648922095134742234349 3507243345785675528337881)
                      ·
                        rfl

theorem cell23_6830332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 4, 1, 2, 1, 4, 1, 3].length) (baseStart_6830332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830332 prefixEnd_6830332 := by exact prefixLift 6830332
  have htrace : WordTrace (prefixWord ++ tailWord_6830332) baseStart_6830332 baseEnd_6830332 := by
    simpa [prefixWord, tailWord_6830332, baseEnd_6830332] using wordTrace_append hprefix tailTrace_6830332
  have hstable : (prefixWord ++ tailWord_6830332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830332).length < 2 ^ (prefixWord ++ tailWord_6830332).sum := by decide
  have hdescent : baseEnd_6830332 < baseStart_6830332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830343 : List Nat := [1, 1, 4, 5, 2, 1, 2, 1, 2, 4]
def baseStart_6830343 : Nat := 118140960795 + 6830343 * 2 ^ 59
def prefixEnd_6830343 : Nat := 4983230072969 + 3 ^ 40 * 6830343 * 2
def baseEnd_6830343 : Nat := 1169082998024291661766777

theorem tailTrace_6830343 : CollatzResearch.WordTrace tailWord_6830343 prefixEnd_6830343 1169082998024291661766777 := by
  unfold tailWord_6830343
  simp only [CollatzResearch.WordTrace]
  refine ⟨249123075493841315557335683, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166082050329227543704890455 249123075493841315557335683)
  ·
    refine ⟨373684613240761973336003525, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249123075493841315557335683 373684613240761973336003525)
    ·
      refine ⟨70065864982642870000500661, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373684613240761973336003525 70065864982642870000500661)
      ·
        refine ⟨6568674842122769062546937, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 70065864982642870000500661 6568674842122769062546937)
        ·
          refine ⟨4926506131592076796910203, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6568674842122769062546937 4926506131592076796910203)
          ·
            refine ⟨7389759197388115195365305, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926506131592076796910203 7389759197388115195365305)
            ·
              refine ⟨5542319398041086396523979, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389759197388115195365305 5542319398041086396523979)
              ·
                refine ⟨8313479097061629594785969, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542319398041086396523979 8313479097061629594785969)
                ·
                  refine ⟨6235109322796222196089477, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8313479097061629594785969 6235109322796222196089477)
                  ·
                    refine ⟨1169082998024291661766777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6235109322796222196089477 1169082998024291661766777)
                    ·
                      rfl

theorem cell23_6830343_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 5, 2, 1, 2, 1, 2, 4].length) (baseStart_6830343 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830343 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830343 prefixEnd_6830343 := by exact prefixLift 6830343
  have htrace : WordTrace (prefixWord ++ tailWord_6830343) baseStart_6830343 baseEnd_6830343 := by
    simpa [prefixWord, tailWord_6830343, baseEnd_6830343] using wordTrace_append hprefix tailTrace_6830343
  have hstable : (prefixWord ++ tailWord_6830343).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830343).length < 2 ^ (prefixWord ++ tailWord_6830343).sum := by decide
  have hdescent : baseEnd_6830343 < baseStart_6830343 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830343) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830348 : List Nat := [2, 2, 1, 2, 2, 2, 2, 1, 1, 8]
def baseStart_6830348 : Nat := 118140960795 + 6830348 * 2 ^ 59
def prefixEnd_6830348 : Nat := 4983230072969 + 3 ^ 40 * 6830348 * 2
def baseEnd_6830348 : Nat := 1169083853825382488579269

theorem tailTrace_6830348 : CollatzResearch.WordTrace tailWord_6830348 prefixEnd_6830348 1169083853825382488579269 := by
  unfold tailWord_6830348
  simp only [CollatzResearch.WordTrace]
  refine ⟨124561628929411600705633849, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166082171905882134274178465 124561628929411600705633849)
  ·
    refine ⟨93421221697058700529225387, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124561628929411600705633849 93421221697058700529225387)
    ·
      refine ⟨140131832545588050793838081, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93421221697058700529225387 140131832545588050793838081)
      ·
        refine ⟨105098874409191038095378561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140131832545588050793838081 105098874409191038095378561)
        ·
          refine ⟨78824155806893278571533921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105098874409191038095378561 78824155806893278571533921)
          ·
            refine ⟨59118116855169958928650441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78824155806893278571533921 59118116855169958928650441)
            ·
              refine ⟨44338587641377469196487831, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59118116855169958928650441 44338587641377469196487831)
              ·
                refine ⟨66507881462066203794731747, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44338587641377469196487831 66507881462066203794731747)
                ·
                  refine ⟨99761822193099305692097621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66507881462066203794731747 99761822193099305692097621)
                  ·
                    refine ⟨1169083853825382488579269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99761822193099305692097621 1169083853825382488579269)
                    ·
                      rfl

theorem cell23_6830348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 2, 2, 2, 1, 1, 8].length) (baseStart_6830348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830348 prefixEnd_6830348 := by exact prefixLift 6830348
  have htrace : WordTrace (prefixWord ++ tailWord_6830348) baseStart_6830348 baseEnd_6830348 := by
    simpa [prefixWord, tailWord_6830348, baseEnd_6830348] using wordTrace_append hprefix tailTrace_6830348
  have hstable : (prefixWord ++ tailWord_6830348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830348).length < 2 ^ (prefixWord ++ tailWord_6830348).sum := by decide
  have hdescent : baseEnd_6830348 < baseStart_6830348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830355 : List Nat := [1, 1, 1, 2, 1, 3, 1, 2, 5, 4, 2]
def baseStart_6830355 : Nat := 118140960795 + 6830355 * 2 ^ 59
def prefixEnd_6830355 : Nat := 4983230072969 + 3 ^ 40 * 6830355 * 2
def baseEnd_6830355 : Nat := 3507255155840728938350275

theorem tailTrace_6830355 : CollatzResearch.WordTrace tailWord_6830355 prefixEnd_6830355 3507255155840728938350275 := by
  unfold tailWord_6830355
  simp only [CollatzResearch.WordTrace]
  refine ⟨249123513169797841606772519, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166082342113198561071181679 249123513169797841606772519)
  ·
    refine ⟨373685269754696762410158779, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249123513169797841606772519 373685269754696762410158779)
    ·
      refine ⟨560527904632045143615238169, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373685269754696762410158779 560527904632045143615238169)
      ·
        refine ⟨420395928474033857711428627, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560527904632045143615238169 420395928474033857711428627)
        ·
          refine ⟨630593892711050786567142941, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420395928474033857711428627 630593892711050786567142941)
          ·
            refine ⟨236472709766644044962678603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630593892711050786567142941 236472709766644044962678603)
            ·
              refine ⟨354709064649966067444017905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236472709766644044962678603 354709064649966067444017905)
              ·
                refine ⟨266031798487474550583013429, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354709064649966067444017905 266031798487474550583013429)
                ·
                  refine ⟨24940481108200739117157509, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266031798487474550583013429 24940481108200739117157509)
                  ·
                    refine ⟨4676340207787638584467033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24940481108200739117157509 4676340207787638584467033)
                    ·
                      refine ⟨3507255155840728938350275, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676340207787638584467033 3507255155840728938350275)
                      ·
                        rfl

theorem cell23_6830355_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 3, 1, 2, 5, 4, 2].length) (baseStart_6830355 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830355 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830355 prefixEnd_6830355 := by exact prefixLift 6830355
  have htrace : WordTrace (prefixWord ++ tailWord_6830355) baseStart_6830355 baseEnd_6830355 := by
    simpa [prefixWord, tailWord_6830355, baseEnd_6830355] using wordTrace_append hprefix tailTrace_6830355
  have hstable : (prefixWord ++ tailWord_6830355).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830355).length < 2 ^ (prefixWord ++ tailWord_6830355).sum := by decide
  have hdescent : baseEnd_6830355 < baseStart_6830355 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830355) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830359 : List Nat := [1, 1, 3, 4, 1, 2, 3, 2, 1, 3, 2]
def baseStart_6830359 : Nat := 118140960795 + 6830359 * 2 ^ 59
def prefixEnd_6830359 : Nat := 4983230072969 + 3 ^ 40 * 6830359 * 2
def baseEnd_6830359 : Nat := 3507257209763346922700257

theorem tailTrace_6830359 : CollatzResearch.WordTrace tailWord_6830359 prefixEnd_6830359 3507257209763346922700257 := by
  unfold tailWord_6830359
  simp only [CollatzResearch.WordTrace]
  refine ⟨249123659061783350289918131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166082439374522233526612087 249123659061783350289918131)
  ·
    refine ⟨373685488592675025434877197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249123659061783350289918131 373685488592675025434877197)
    ·
      refine ⟨140132058222253134538078949, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373685488592675025434877197 140132058222253134538078949)
      ·
        refine ⟨26274760916672462725889803, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140132058222253134538078949 26274760916672462725889803)
        ·
          refine ⟨39412141375008694088834705, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26274760916672462725889803 39412141375008694088834705)
          ·
            refine ⟨29559106031256520566626029, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39412141375008694088834705 29559106031256520566626029)
            ·
              refine ⟨11084664761721195212484761, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29559106031256520566626029 11084664761721195212484761)
              ·
                refine ⟨8313498571290896409363571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11084664761721195212484761 8313498571290896409363571)
                ·
                  refine ⟨12470247856936344614045357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313498571290896409363571 12470247856936344614045357)
                  ·
                    refine ⟨4676342946351129230267009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12470247856936344614045357 4676342946351129230267009)
                    ·
                      refine ⟨3507257209763346922700257, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676342946351129230267009 3507257209763346922700257)
                      ·
                        rfl

theorem cell23_6830359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 4, 1, 2, 3, 2, 1, 3, 2].length) (baseStart_6830359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830359 prefixEnd_6830359 := by exact prefixLift 6830359
  have htrace : WordTrace (prefixWord ++ tailWord_6830359) baseStart_6830359 baseEnd_6830359 := by
    simpa [prefixWord, tailWord_6830359, baseEnd_6830359] using wordTrace_append hprefix tailTrace_6830359
  have hstable : (prefixWord ++ tailWord_6830359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830359).length < 2 ^ (prefixWord ++ tailWord_6830359).sum := by decide
  have hdescent : baseEnd_6830359 < baseStart_6830359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830372 : List Nat := [2, 3, 1, 3, 1, 2, 1, 1, 3, 4, 2]
def baseStart_6830372 : Nat := 118140960795 + 6830372 * 2 ^ 59
def prefixEnd_6830372 : Nat := 4983230072969 + 3 ^ 40 * 6830372 * 2
def baseEnd_6830372 : Nat := 3507263885011855371837697

theorem tailTrace_6830372 : CollatzResearch.WordTrace tailWord_6830372 prefixEnd_6830372 3507263885011855371837697 := by
  unfold tailWord_6830372
  simp only [CollatzResearch.WordTrace]
  refine ⟨124562066605368126755070685, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166082755473824169006760913 124562066605368126755070685)
  ·
    refine ⟨46710774977013047533151507, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124562066605368126755070685 46710774977013047533151507)
    ·
      refine ⟨70066162465519571299727261, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46710774977013047533151507 70066162465519571299727261)
      ·
        refine ⟨26274810924569839237397723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70066162465519571299727261 26274810924569839237397723)
        ·
          refine ⟨39412216386854758856096585, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26274810924569839237397723 39412216386854758856096585)
          ·
            refine ⟨29559162290141069142072439, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39412216386854758856096585 29559162290141069142072439)
            ·
              refine ⟨44338743435211603713108659, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29559162290141069142072439 44338743435211603713108659)
              ·
                refine ⟨66508115152817405569662989, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44338743435211603713108659 66508115152817405569662989)
                ·
                  refine ⟨24940543182306527088623621, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66508115152817405569662989 24940543182306527088623621)
                  ·
                    refine ⟨4676351846682473829116929, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24940543182306527088623621 4676351846682473829116929)
                    ·
                      refine ⟨3507263885011855371837697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676351846682473829116929 3507263885011855371837697)
                      ·
                        rfl

theorem cell23_6830372_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 2, 1, 1, 3, 4, 2].length) (baseStart_6830372 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830372 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830372 prefixEnd_6830372 := by exact prefixLift 6830372
  have htrace : WordTrace (prefixWord ++ tailWord_6830372) baseStart_6830372 baseEnd_6830372 := by
    simpa [prefixWord, tailWord_6830372, baseEnd_6830372] using wordTrace_append hprefix tailTrace_6830372
  have hstable : (prefixWord ++ tailWord_6830372).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830372).length < 2 ^ (prefixWord ++ tailWord_6830372).sum := by decide
  have hdescent : baseEnd_6830372 < baseStart_6830372 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830372) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830472 : List Nat := [2, 1, 3, 3, 1, 1, 1, 4, 3, 4]
def baseStart_6830472 : Nat := 118140960795 + 6830472 * 2 ^ 59
def prefixEnd_6830472 : Nat := 4983230072969 + 3 ^ 40 * 6830472 * 2
def baseEnd_6830472 : Nat := 1169105077692434993529079

theorem tailTrace_6830472 : CollatzResearch.WordTrace tailWord_6830472 prefixEnd_6830472 1169105077692434993529079 := by
  unfold tailWord_6830472
  simp only [CollatzResearch.WordTrace]
  refine ⟨124563890255186985294390835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166085187006915980392521113 124563890255186985294390835)
  ·
    refine ⟨186845835382780477941586253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124563890255186985294390835 186845835382780477941586253)
    ·
      refine ⟨70067188268542679228094845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186845835382780477941586253 70067188268542679228094845)
      ·
        refine ⟨26275195600703504710535567, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70067188268542679228094845 26275195600703504710535567)
        ·
          refine ⟨39412793401055257065803351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26275195600703504710535567 39412793401055257065803351)
          ·
            refine ⟨59119190101582885598705027, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39412793401055257065803351 59119190101582885598705027)
            ·
              refine ⟨88678785152374328398057541, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59119190101582885598705027 88678785152374328398057541)
              ·
                refine ⟨16627272216070186574635789, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88678785152374328398057541 16627272216070186574635789)
                ·
                  refine ⟨6235227081026319965488421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16627272216070186574635789 6235227081026319965488421)
                  ·
                    refine ⟨1169105077692434993529079, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6235227081026319965488421 1169105077692434993529079)
                    ·
                      rfl

theorem cell23_6830472_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 1, 1, 4, 3, 4].length) (baseStart_6830472 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830472 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830472 prefixEnd_6830472 := by exact prefixLift 6830472
  have htrace : WordTrace (prefixWord ++ tailWord_6830472) baseStart_6830472 baseEnd_6830472 := by
    simpa [prefixWord, tailWord_6830472, baseEnd_6830472] using wordTrace_append hprefix tailTrace_6830472
  have hstable : (prefixWord ++ tailWord_6830472).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830472).length < 2 ^ (prefixWord ++ tailWord_6830472).sum := by decide
  have hdescent : baseEnd_6830472 < baseStart_6830472 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830472) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830519 : List Nat := [1, 1, 3, 1, 3, 5, 2, 1, 6]
def baseStart_6830519 : Nat := 118140960795 + 6830519 * 2 ^ 59
def prefixEnd_6830519 : Nat := 4983230072969 + 3 ^ 40 * 6830519 * 2
def baseEnd_6830519 : Nat := 389704374074229588522169

theorem tailTrace_6830519 : CollatzResearch.WordTrace tailWord_6830519 prefixEnd_6830519 389704374074229588522169 := by
  unfold tailWord_6830519
  simp only [CollatzResearch.WordTrace]
  refine ⟨249129494741203697615742611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166086329827469131743828407 249129494741203697615742611)
  ·
    refine ⟨373694242111805546423613917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249129494741203697615742611 373694242111805546423613917)
    ·
      refine ⟨140135340791927079908855219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373694242111805546423613917 140135340791927079908855219)
      ·
        refine ⟨210203011187890619863282829, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140135340791927079908855219 210203011187890619863282829)
        ·
          refine ⟨78826129195458982448731061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210203011187890619863282829 78826129195458982448731061)
          ·
            refine ⟨7389949612074279604568537, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78826129195458982448731061 7389949612074279604568537)
            ·
              refine ⟨5542462209055709703426403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7389949612074279604568537 5542462209055709703426403)
              ·
                refine ⟨8313693313583564555139605, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5542462209055709703426403 8313693313583564555139605)
                ·
                  refine ⟨389704374074229588522169, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8313693313583564555139605 389704374074229588522169)
                  ·
                    rfl

theorem cell23_6830519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 5, 2, 1, 6].length) (baseStart_6830519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830519 prefixEnd_6830519 := by exact prefixLift 6830519
  have htrace : WordTrace (prefixWord ++ tailWord_6830519) baseStart_6830519 baseEnd_6830519 := by
    simpa [prefixWord, tailWord_6830519, baseEnd_6830519] using wordTrace_append hprefix tailTrace_6830519
  have hstable : (prefixWord ++ tailWord_6830519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830519).length < 2 ^ (prefixWord ++ tailWord_6830519).sum := by decide
  have hdescent : baseEnd_6830519 < baseStart_6830519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830522 : List Nat := [3, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2]
def baseStart_6830522 : Nat := 118140960795 + 6830522 * 2 ^ 59
def prefixEnd_6830522 : Nat := 4983230072969 + 3 ^ 40 * 6830522 * 2
def baseEnd_6830522 : Nat := 3507340907110029784962007

theorem tailTrace_6830522 : CollatzResearch.WordTrace tailWord_6830522 prefixEnd_6830522 3507340907110029784962007 := by
  unfold tailWord_6830522
  simp only [CollatzResearch.WordTrace]
  refine ⟨62282401040048207282025455, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166086402773461886085401213 62282401040048207282025455)
  ·
    refine ⟨93423601560072310923038183, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62282401040048207282025455 93423601560072310923038183)
    ·
      refine ⟨140135402340108466384557275, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93423601560072310923038183 140135402340108466384557275)
      ·
        refine ⟨210203103510162699576835913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140135402340108466384557275 210203103510162699576835913)
        ·
          refine ⟨157652327632622024682626935, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210203103510162699576835913 157652327632622024682626935)
          ·
            refine ⟨236478491448933037023940403, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157652327632622024682626935 236478491448933037023940403)
            ·
              refine ⟨354717737173399555535910605, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236478491448933037023940403 354717737173399555535910605)
              ·
                refine ⟨133019151440024833325966477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 354717737173399555535910605 133019151440024833325966477)
                ·
                  refine ⟨49882181790009312497237429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133019151440024833325966477 49882181790009312497237429)
                  ·
                    refine ⟨4676454542813373046616009, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49882181790009312497237429 4676454542813373046616009)
                    ·
                      refine ⟨3507340907110029784962007, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676454542813373046616009 3507340907110029784962007)
                      ·
                        rfl

theorem cell23_6830522_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 1, 1, 3, 3, 5, 2].length) (baseStart_6830522 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830522 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830522 prefixEnd_6830522 := by exact prefixLift 6830522
  have htrace : WordTrace (prefixWord ++ tailWord_6830522) baseStart_6830522 baseEnd_6830522 := by
    simpa [prefixWord, tailWord_6830522, baseEnd_6830522] using wordTrace_append hprefix tailTrace_6830522
  have hstable : (prefixWord ++ tailWord_6830522).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830522).length < 2 ^ (prefixWord ++ tailWord_6830522).sum := by decide
  have hdescent : baseEnd_6830522 < baseStart_6830522 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830522) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830563 : List Nat := [1, 1, 1, 6, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6830563 : Nat := 118140960795 + 6830563 * 2 ^ 59
def prefixEnd_6830563 : Nat := 4983230072969 + 3 ^ 40 * 6830563 * 2
def baseEnd_6830563 : Nat := 3507361959816864124549319

theorem tailTrace_6830563 : CollatzResearch.WordTrace tailWord_6830563 prefixEnd_6830563 3507361959816864124549319 := by
  unfold tailWord_6830563
  simp only [CollatzResearch.WordTrace]
  refine ⟨249131099553044293130344343, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166087399702029528753562895 249131099553044293130344343)
  ·
    refine ⟨373696649329566439695516515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249131099553044293130344343 373696649329566439695516515)
    ·
      refine ⟨560544973994349659543274773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373696649329566439695516515 560544973994349659543274773)
      ·
        refine ⟨26275545655985140291091005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 560544973994349659543274773 26275545655985140291091005)
        ·
          refine ⟨9853329620994427609159127, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26275545655985140291091005 9853329620994427609159127)
          ·
            refine ⟨14779994431491641413738691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9853329620994427609159127 14779994431491641413738691)
            ·
              refine ⟨22169991647237462120608037, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14779994431491641413738691 22169991647237462120608037)
              ·
                refine ⟨4156873433857024147614007, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22169991647237462120608037 4156873433857024147614007)
                ·
                  refine ⟨6235310150785536221421011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156873433857024147614007 6235310150785536221421011)
                  ·
                    refine ⟨9352965226178304332131517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6235310150785536221421011 9352965226178304332131517)
                    ·
                      refine ⟨3507361959816864124549319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352965226178304332131517 3507361959816864124549319)
                      ·
                        rfl

theorem cell23_6830563_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 6, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6830563 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830563 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830563 prefixEnd_6830563 := by exact prefixLift 6830563
  have htrace : WordTrace (prefixWord ++ tailWord_6830563) baseStart_6830563 baseEnd_6830563 := by
    simpa [prefixWord, tailWord_6830563, baseEnd_6830563] using wordTrace_append hprefix tailTrace_6830563
  have hstable : (prefixWord ++ tailWord_6830563).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830563).length < 2 ^ (prefixWord ++ tailWord_6830563).sum := by decide
  have hdescent : baseEnd_6830563 < baseStart_6830563 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830563) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830572 : List Nat := [2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 3]
def baseStart_6830572 : Nat := 118140960795 + 6830572 * 2 ^ 59
def prefixEnd_6830572 : Nat := 4983230072969 + 3 ^ 40 * 6830572 * 2
def baseEnd_6830572 : Nat := 3507366581142754589336777

theorem tailTrace_6830572 : CollatzResearch.WordTrace tailWord_6830572 prefixEnd_6830572 3507366581142754589336777 := by
  unfold tailWord_6830572
  simp only [CollatzResearch.WordTrace]
  refine ⟨124565713905005843833710985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166087618540007791778281313 124565713905005843833710985)
  ·
    refine ⟨93424285428754382875283239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124565713905005843833710985 93424285428754382875283239)
    ·
      refine ⟨140136428143131574312924859, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93424285428754382875283239 140136428143131574312924859)
      ·
        refine ⟨210204642214697361469387289, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140136428143131574312924859 210204642214697361469387289)
        ·
          refine ⟨157653481661023021102040467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210204642214697361469387289 157653481661023021102040467)
          ·
            refine ⟨236480222491534531653060701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157653481661023021102040467 236480222491534531653060701)
            ·
              refine ⟨88680083434325449369897763, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236480222491534531653060701 88680083434325449369897763)
              ·
                refine ⟨133020125151488174054846645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88680083434325449369897763 133020125151488174054846645)
                ·
                  refine ⟨12470636732952016317641873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133020125151488174054846645 12470636732952016317641873)
                  ·
                    refine ⟨9352977549714012238231405, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12470636732952016317641873 9352977549714012238231405)
                    ·
                      refine ⟨3507366581142754589336777, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9352977549714012238231405 3507366581142754589336777)
                      ·
                        rfl

theorem cell23_6830572_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 5, 2, 3].length) (baseStart_6830572 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830572 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830572 prefixEnd_6830572 := by exact prefixLift 6830572
  have htrace : WordTrace (prefixWord ++ tailWord_6830572) baseStart_6830572 baseEnd_6830572 := by
    simpa [prefixWord, tailWord_6830572, baseEnd_6830572] using wordTrace_append hprefix tailTrace_6830572
  have hstable : (prefixWord ++ tailWord_6830572).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830572).length < 2 ^ (prefixWord ++ tailWord_6830572).sum := by decide
  have hdescent : baseEnd_6830572 < baseStart_6830572 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830572) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830589 : List Nat := [1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 3]
def baseStart_6830589 : Nat := 118140960795 + 6830589 * 2 ^ 59
def prefixEnd_6830589 : Nat := 4983230072969 + 3 ^ 40 * 6830589 * 2
def baseEnd_6830589 : Nat := 3507375310313881022824199

theorem tailTrace_6830589 : CollatzResearch.WordTrace tailWord_6830589 prefixEnd_6830589 3507375310313881022824199 := by
  unfold tailWord_6830589
  simp only [CollatzResearch.WordTrace]
  refine ⟨249132047850950099570790821, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166088031900633399713860547 249132047850950099570790821)
  ·
    refine ⟨46712258972053143669523279, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249132047850950099570790821 46712258972053143669523279)
    ·
      refine ⟨70068388458079715504284919, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46712258972053143669523279 70068388458079715504284919)
      ·
        refine ⟨105102582687119573256427379, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70068388458079715504284919 105102582687119573256427379)
        ·
          refine ⟨157653874030679359884641069, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105102582687119573256427379 157653874030679359884641069)
          ·
            refine ⟨59120202761504759956740401, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157653874030679359884641069 59120202761504759956740401)
            ·
              refine ⟨44340152071128569967555301, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59120202761504759956740401 44340152071128569967555301)
              ·
                refine ⟨8313778513336606868916619, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44340152071128569967555301 8313778513336606868916619)
                ·
                  refine ⟨12470667770004910303374929, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313778513336606868916619 12470667770004910303374929)
                  ·
                    refine ⟨9353000827503682727531197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12470667770004910303374929 9353000827503682727531197)
                    ·
                      refine ⟨3507375310313881022824199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353000827503682727531197 3507375310313881022824199)
                      ·
                        rfl

theorem cell23_6830589_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 3, 2, 4, 1, 2, 3].length) (baseStart_6830589 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830589 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830589 prefixEnd_6830589 := by exact prefixLift 6830589
  have htrace : WordTrace (prefixWord ++ tailWord_6830589) baseStart_6830589 baseEnd_6830589 := by
    simpa [prefixWord, tailWord_6830589, baseEnd_6830589] using wordTrace_append hprefix tailTrace_6830589
  have hstable : (prefixWord ++ tailWord_6830589).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830589).length < 2 ^ (prefixWord ++ tailWord_6830589).sum := by decide
  have hdescent : baseEnd_6830589 < baseStart_6830589 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830589) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830603 : List Nat := [1, 1, 1, 1, 7, 1, 1, 5, 1, 2, 2]
def baseStart_6830603 : Nat := 118140960795 + 6830603 * 2 ^ 59
def prefixEnd_6830603 : Nat := 4983230072969 + 3 ^ 40 * 6830603 * 2
def baseEnd_6830603 : Nat := 3507382499043043968049135

theorem tailTrace_6830603 : CollatzResearch.WordTrace tailWord_6830603 prefixEnd_6830603 3507382499043043968049135 := by
  unfold tailWord_6830603
  simp only [CollatzResearch.WordTrace]
  refine ⟨249132558472899379961800463, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166088372315266253307866975 249132558472899379961800463)
  ·
    refine ⟨373698837709349069942700695, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249132558472899379961800463 373698837709349069942700695)
    ·
      refine ⟨560548256564023604914051043, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373698837709349069942700695 560548256564023604914051043)
      ·
        refine ⟨840822384846035407371076565, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560548256564023604914051043 840822384846035407371076565)
        ·
          refine ⟨19706774644828954860259607, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 7 840822384846035407371076565 19706774644828954860259607)
          ·
            refine ⟨29560161967243432290389411, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19706774644828954860259607 29560161967243432290389411)
            ·
              refine ⟨44340242950865148435584117, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29560161967243432290389411 44340242950865148435584117)
              ·
                refine ⟨4156897776643607665836011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44340242950865148435584117 4156897776643607665836011)
                ·
                  refine ⟨6235346664965411498754017, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156897776643607665836011 6235346664965411498754017)
                  ·
                    refine ⟨4676509998724058624065513, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6235346664965411498754017 4676509998724058624065513)
                    ·
                      refine ⟨3507382499043043968049135, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676509998724058624065513 3507382499043043968049135)
                      ·
                        rfl

theorem cell23_6830603_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 7, 1, 1, 5, 1, 2, 2].length) (baseStart_6830603 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830603 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830603 prefixEnd_6830603 := by exact prefixLift 6830603
  have htrace : WordTrace (prefixWord ++ tailWord_6830603) baseStart_6830603 baseEnd_6830603 := by
    simpa [prefixWord, tailWord_6830603, baseEnd_6830603] using wordTrace_append hprefix tailTrace_6830603
  have hstable : (prefixWord ++ tailWord_6830603).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830603).length < 2 ^ (prefixWord ++ tailWord_6830603).sum := by decide
  have hdescent : baseEnd_6830603 < baseStart_6830603 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830603) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830606 : List Nat := [4, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3]
def baseStart_6830606 : Nat := 118140960795 + 6830606 * 2 ^ 59
def prefixEnd_6830606 : Nat := 4983230072969 + 3 ^ 40 * 6830606 * 2
def baseEnd_6830606 : Nat := 3507384039485007456311621

theorem tailTrace_6830606 : CollatzResearch.WordTrace tailWord_6830606 prefixEnd_6830606 3507384039485007456311621 := by
  unfold tailWord_6830606
  simp only [CollatzResearch.WordTrace]
  refine ⟨31141583486486063934269959, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166088445261259007649439781 31141583486486063934269959)
  ·
    refine ⟨46712375229729095901404939, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31141583486486063934269959 46712375229729095901404939)
    ·
      refine ⟨70068562844593643852107409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46712375229729095901404939 70068562844593643852107409)
      ·
        refine ⟨52551422133445232889080557, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70068562844593643852107409 52551422133445232889080557)
        ·
          refine ⟨19706783300041962333405209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52551422133445232889080557 19706783300041962333405209)
          ·
            refine ⟨14780087475031471750053907, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19706783300041962333405209 14780087475031471750053907)
            ·
              refine ⟨22170131212547207625080861, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14780087475031471750053907 22170131212547207625080861)
              ·
                refine ⟨8313799204705202859405323, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22170131212547207625080861 8313799204705202859405323)
                ·
                  refine ⟨12470698807057804289107985, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8313799204705202859405323 12470698807057804289107985)
                  ·
                    refine ⟨9353024105293353216830989, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12470698807057804289107985 9353024105293353216830989)
                    ·
                      refine ⟨3507384039485007456311621, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353024105293353216830989 3507384039485007456311621)
                      ·
                        rfl

theorem cell23_6830606_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 3, 2, 1, 3, 1, 2, 3].length) (baseStart_6830606 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830606 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830606 prefixEnd_6830606 := by exact prefixLift 6830606
  have htrace : WordTrace (prefixWord ++ tailWord_6830606) baseStart_6830606 baseEnd_6830606 := by
    simpa [prefixWord, tailWord_6830606, baseEnd_6830606] using wordTrace_append hprefix tailTrace_6830606
  have hstable : (prefixWord ++ tailWord_6830606).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830606).length < 2 ^ (prefixWord ++ tailWord_6830606).sum := by decide
  have hdescent : baseEnd_6830606 < baseStart_6830606 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830606) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830629 : List Nat := [1, 3, 1, 2, 2, 1, 2, 1, 5, 3, 2]
def baseStart_6830629 : Nat := 118140960795 + 6830629 * 2 ^ 59
def prefixEnd_6830629 : Nat := 4983230072969 + 3 ^ 40 * 6830629 * 2
def baseEnd_6830629 : Nat := 3507395849540060866324015

theorem tailTrace_6830629 : CollatzResearch.WordTrace tailWord_6830629 prefixEnd_6830629 3507395849540060866324015 := by
  unfold tailWord_6830629
  simp only [CollatzResearch.WordTrace]
  refine ⟨249133506770805186402246941, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166089004513870124268164627 249133506770805186402246941)
  ·
    refine ⟨93425065039051944900842603, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249133506770805186402246941 93425065039051944900842603)
    ·
      refine ⟨140137597558577917351263905, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93425065039051944900842603 140137597558577917351263905)
      ·
        refine ⟨105103198168933438013447929, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140137597558577917351263905 105103198168933438013447929)
        ·
          refine ⟨78827398626700078510085947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105103198168933438013447929 78827398626700078510085947)
          ·
            refine ⟨118241097940050117765128921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78827398626700078510085947 118241097940050117765128921)
            ·
              refine ⟨88680823455037588323846691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118241097940050117765128921 88680823455037588323846691)
              ·
                refine ⟨133021235182556382485770037, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88680823455037588323846691 133021235182556382485770037)
                ·
                  refine ⟨12470740798364660858040941, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133021235182556382485770037 12470740798364660858040941)
                  ·
                    refine ⟨4676527799386747821765353, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12470740798364660858040941 4676527799386747821765353)
                    ·
                      refine ⟨3507395849540060866324015, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676527799386747821765353 3507395849540060866324015)
                      ·
                        rfl

theorem cell23_6830629_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 2, 1, 2, 1, 5, 3, 2].length) (baseStart_6830629 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830629 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830629 prefixEnd_6830629 := by exact prefixLift 6830629
  have htrace : WordTrace (prefixWord ++ tailWord_6830629) baseStart_6830629 baseEnd_6830629 := by
    simpa [prefixWord, tailWord_6830629, baseEnd_6830629] using wordTrace_append hprefix tailTrace_6830629
  have hstable : (prefixWord ++ tailWord_6830629).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830629).length < 2 ^ (prefixWord ++ tailWord_6830629).sum := by decide
  have hdescent : baseEnd_6830629 < baseStart_6830629 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830629) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830642 : List Nat := [3, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4]
def baseStart_6830642 : Nat := 118140960795 + 6830642 * 2 ^ 59
def prefixEnd_6830642 : Nat := 4983230072969 + 3 ^ 40 * 6830642 * 2
def baseEnd_6830642 : Nat := 3507402524788569315461455

theorem tailTrace_6830642 : CollatzResearch.WordTrace tailWord_6830642 prefixEnd_6830642 3507402524788569315461455 := by
  unfold tailWord_6830642
  simp only [CollatzResearch.WordTrace]
  refine ⟨62283495229939522405617545, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166089320613172059748313453 62283495229939522405617545)
  ·
    refine ⟨46712621422454641804213159, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62283495229939522405617545 46712621422454641804213159)
    ·
      refine ⟨70068932133681962706319739, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46712621422454641804213159 70068932133681962706319739)
      ·
        refine ⟨105103398200522944059479609, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70068932133681962706319739 105103398200522944059479609)
        ·
          refine ⟨78827548650392208044609707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105103398200522944059479609 78827548650392208044609707)
          ·
            refine ⟨118241322975588312066914561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78827548650392208044609707 118241322975588312066914561)
            ·
              refine ⟨88680992231691234050185921, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118241322975588312066914561 88680992231691234050185921)
              ·
                refine ⟨66510744173768425537639441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88680992231691234050185921 66510744173768425537639441)
                ·
                  refine ⟨49883058130326319153229581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66510744173768425537639441 49883058130326319153229581)
                  ·
                    refine ⟨18706146798872369682461093, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49883058130326319153229581 18706146798872369682461093)
                    ·
                      refine ⟨3507402524788569315461455, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18706146798872369682461093 3507402524788569315461455)
                      ·
                        rfl

theorem cell23_6830642_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 2, 1, 2, 2, 2, 3, 4].length) (baseStart_6830642 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830642 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830642 prefixEnd_6830642 := by exact prefixLift 6830642
  have htrace : WordTrace (prefixWord ++ tailWord_6830642) baseStart_6830642 baseEnd_6830642 := by
    simpa [prefixWord, tailWord_6830642, baseEnd_6830642] using wordTrace_append hprefix tailTrace_6830642
  have hstable : (prefixWord ++ tailWord_6830642).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830642).length < 2 ^ (prefixWord ++ tailWord_6830642).sum := by decide
  have hdescent : baseEnd_6830642 < baseStart_6830642 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830642) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830654 : List Nat := [4, 2, 1, 4, 1, 2, 1, 3, 1, 2, 2]
def baseStart_6830654 : Nat := 118140960795 + 6830654 * 2 ^ 59
def prefixEnd_6830654 : Nat := 4983230072969 + 3 ^ 40 * 6830654 * 2
def baseEnd_6830654 : Nat := 3507408686556423268511401

theorem tailTrace_6830654 : CollatzResearch.WordTrace tailWord_6830654 prefixEnd_6830654 3507408686556423268511401 := by
  unfold tailWord_6830654
  simp only [CollatzResearch.WordTrace]
  refine ⟨31141802324464326958988377, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166089612397143077114604677 31141802324464326958988377)
  ·
    refine ⟨23356351743348245219241283, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31141802324464326958988377 23356351743348245219241283)
    ·
      refine ⟨35034527615022367828861925, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23356351743348245219241283 35034527615022367828861925)
      ·
        refine ⟨6568973927816693967911611, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35034527615022367828861925 6568973927816693967911611)
        ·
          refine ⟨9853460891725040951867417, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6568973927816693967911611 9853460891725040951867417)
          ·
            refine ⟨7390095668793780713900563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9853460891725040951867417 7390095668793780713900563)
            ·
              refine ⟨11085143503190671070850845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390095668793780713900563 11085143503190671070850845)
              ·
                refine ⟨4156928813696501651569067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11085143503190671070850845 4156928813696501651569067)
                ·
                  refine ⟨6235393220544752477353601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4156928813696501651569067 6235393220544752477353601)
                  ·
                    refine ⟨4676544915408564358015201, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6235393220544752477353601 4676544915408564358015201)
                    ·
                      refine ⟨3507408686556423268511401, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676544915408564358015201 3507408686556423268511401)
                      ·
                        rfl

theorem cell23_6830654_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 4, 1, 2, 1, 3, 1, 2, 2].length) (baseStart_6830654 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830654 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830654 prefixEnd_6830654 := by exact prefixLift 6830654
  have htrace : WordTrace (prefixWord ++ tailWord_6830654) baseStart_6830654 baseEnd_6830654 := by
    simpa [prefixWord, tailWord_6830654, baseEnd_6830654] using wordTrace_append hprefix tailTrace_6830654
  have hstable : (prefixWord ++ tailWord_6830654).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830654).length < 2 ^ (prefixWord ++ tailWord_6830654).sum := by decide
  have hdescent : baseEnd_6830654 < baseStart_6830654 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830654) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830659 : List Nat := [1, 1, 1, 3, 1, 2, 1, 6, 1, 4, 2]
def baseStart_6830659 : Nat := 118140960795 + 6830659 * 2 ^ 59
def prefixEnd_6830659 : Nat := 4983230072969 + 3 ^ 40 * 6830659 * 2
def baseEnd_6830659 : Nat := 3507411253959695748948877

theorem tailTrace_6830659 : CollatzResearch.WordTrace tailWord_6830659 prefixEnd_6830659 3507411253959695748948877 := by
  unfold tailWord_6830659
  simp only [CollatzResearch.WordTrace]
  refine ⟨249134600960696501525839031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166089733973797667683892687 249134600960696501525839031)
  ·
    refine ⟨373701901441044752288758547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249134600960696501525839031 373701901441044752288758547)
    ·
      refine ⟨560552852161567128433137821, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373701901441044752288758547 560552852161567128433137821)
      ·
        refine ⟨210207319560587673162426683, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560552852161567128433137821 210207319560587673162426683)
        ·
          refine ⟨315310979340881509743640025, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210207319560587673162426683 315310979340881509743640025)
          ·
            refine ⟨236483234505661132307730019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315310979340881509743640025 236483234505661132307730019)
            ·
              refine ⟨354724851758491698461595029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236483234505661132307730019 354724851758491698461595029)
              ·
                refine ⟨16627727426179298365387267, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 354724851758491698461595029 16627727426179298365387267)
                ·
                  refine ⟨24941591139268947548080901, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16627727426179298365387267 24941591139268947548080901)
                  ·
                    refine ⟨4676548338612927665265169, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24941591139268947548080901 4676548338612927665265169)
                    ·
                      refine ⟨3507411253959695748948877, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676548338612927665265169 3507411253959695748948877)
                      ·
                        rfl

theorem cell23_6830659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 1, 2, 1, 6, 1, 4, 2].length) (baseStart_6830659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830659 prefixEnd_6830659 := by exact prefixLift 6830659
  have htrace : WordTrace (prefixWord ++ tailWord_6830659) baseStart_6830659 baseEnd_6830659 := by
    simpa [prefixWord, tailWord_6830659, baseEnd_6830659] using wordTrace_append hprefix tailTrace_6830659
  have hstable : (prefixWord ++ tailWord_6830659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830659).length < 2 ^ (prefixWord ++ tailWord_6830659).sum := by decide
  have hdescent : baseEnd_6830659 < baseStart_6830659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830672 : List Nat := [2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4]
def baseStart_6830672 : Nat := 118140960795 + 6830672 * 2 ^ 59
def prefixEnd_6830672 : Nat := 4983230072969 + 3 ^ 40 * 6830672 * 2
def baseEnd_6830672 : Nat := 3507417929208204198086317

theorem tailTrace_6830672 : CollatzResearch.WordTrace tailWord_6830672 prefixEnd_6830672 3507417929208204198086317 := by
  unfold tailWord_6830672
  simp only [CollatzResearch.WordTrace]
  refine ⟨124567537554824702373031135, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166090050073099603164041513 124567537554824702373031135)
  ·
    refine ⟨186851306332237053559546703, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124567537554824702373031135 186851306332237053559546703)
    ·
      refine ⟨280276959498355580339320055, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186851306332237053559546703 280276959498355580339320055)
      ·
        refine ⟨420415439247533370508980083, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280276959498355580339320055 420415439247533370508980083)
        ·
          refine ⟨630623158871300055763470125, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420415439247533370508980083 630623158871300055763470125)
          ·
            refine ⟨236483684576737520911301297, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630623158871300055763470125 236483684576737520911301297)
            ·
              refine ⟨177362763432553140683475973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236483684576737520911301297 177362763432553140683475973)
              ·
                refine ⟨33255518143603713878151745, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 177362763432553140683475973 33255518143603713878151745)
                ·
                  refine ⟨24941638607702785408613809, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33255518143603713878151745 24941638607702785408613809)
                  ·
                    refine ⟨18706228955777089056460357, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24941638607702785408613809 18706228955777089056460357)
                    ·
                      refine ⟨3507417929208204198086317, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18706228955777089056460357 3507417929208204198086317)
                      ·
                        rfl

theorem cell23_6830672_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 2, 4, 2, 2, 4].length) (baseStart_6830672 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830672 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830672 prefixEnd_6830672 := by exact prefixLift 6830672
  have htrace : WordTrace (prefixWord ++ tailWord_6830672) baseStart_6830672 baseEnd_6830672 := by
    simpa [prefixWord, tailWord_6830672, baseEnd_6830672] using wordTrace_append hprefix tailTrace_6830672
  have hstable : (prefixWord ++ tailWord_6830672).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830672).length < 2 ^ (prefixWord ++ tailWord_6830672).sum := by decide
  have hdescent : baseEnd_6830672 < baseStart_6830672 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830672) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830712 : List Nat := [2, 1, 2, 1, 1, 1, 2, 2, 6, 5]
def baseStart_6830712 : Nat := 118140960795 + 6830712 * 2 ^ 59
def prefixEnd_6830712 : Nat := 4983230072969 + 3 ^ 40 * 6830712 * 2
def baseEnd_6830712 : Nat := 1169146156144794680528711

theorem tailTrace_6830712 : CollatzResearch.WordTrace tailWord_6830712 prefixEnd_6830712 1169146156144794680528711 := by
  unfold tailWord_6830712
  simp only [CollatzResearch.WordTrace]
  refine ⟨124568267014752245788759195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166091022686336327718345593 124568267014752245788759195)
  ·
    refine ⟨186852400522128368683138793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124568267014752245788759195 186852400522128368683138793)
    ·
      refine ⟨140139300391596276512354095, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186852400522128368683138793 140139300391596276512354095)
      ·
        refine ⟨210208950587394414768531143, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140139300391596276512354095 210208950587394414768531143)
        ·
          refine ⟨315313425881091622152796715, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210208950587394414768531143 315313425881091622152796715)
          ·
            refine ⟨472970138821637433229195073, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315313425881091622152796715 472970138821637433229195073)
            ·
              refine ⟨354727604116228074921896305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 472970138821637433229195073 354727604116228074921896305)
              ·
                refine ⟨266045703087171056191422229, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354727604116228074921896305 266045703087171056191422229)
                ·
                  refine ⟨12470892332211143258972917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 266045703087171056191422229 12470892332211143258972917)
                  ·
                    refine ⟨1169146156144794680528711, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12470892332211143258972917 1169146156144794680528711)
                    ·
                      rfl

theorem cell23_6830712_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 2, 2, 6, 5].length) (baseStart_6830712 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830712 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830712 prefixEnd_6830712 := by exact prefixLift 6830712
  have htrace : WordTrace (prefixWord ++ tailWord_6830712) baseStart_6830712 baseEnd_6830712 := by
    simpa [prefixWord, tailWord_6830712, baseEnd_6830712] using wordTrace_append hprefix tailTrace_6830712
  have hstable : (prefixWord ++ tailWord_6830712).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830712).length < 2 ^ (prefixWord ++ tailWord_6830712).sum := by decide
  have hdescent : baseEnd_6830712 < baseStart_6830712 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830712) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830749 : List Nat := [1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 4]
def baseStart_6830749 : Nat := 118140960795 + 6830749 * 2 ^ 59
def prefixEnd_6830749 : Nat := 4983230072969 + 3 ^ 40 * 6830749 * 2
def baseEnd_6830749 : Nat := 3507457467218600396823463

theorem tailTrace_6830749 : CollatzResearch.WordTrace tailWord_6830749 prefixEnd_6830749 3507457467218600396823463 := by
  unfold tailWord_6830749
  simp only [CollatzResearch.WordTrace]
  refine ⟨249137883530370446896615301, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166091922353580297931076867 249137883530370446896615301)
  ·
    refine ⟨46713353161944458793115369, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249137883530370446896615301 46713353161944458793115369)
    ·
      refine ⟨35035014871458344094836527, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46713353161944458793115369 35035014871458344094836527)
      ·
        refine ⟨52552522307187516142254791, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35035014871458344094836527 52552522307187516142254791)
        ·
          refine ⟨78828783460781274213382187, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52552522307187516142254791 78828783460781274213382187)
          ·
            refine ⟨118243175191171911320073281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78828783460781274213382187 118243175191171911320073281)
            ·
              refine ⟨88682381393378933490054961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118243175191171911320073281 88682381393378933490054961)
              ·
                refine ⟨66511786045034200117541221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88682381393378933490054961 66511786045034200117541221)
                ·
                  refine ⟨12470959883443912522038979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66511786045034200117541221 12470959883443912522038979)
                  ·
                    refine ⟨18706439825165868783058469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12470959883443912522038979 18706439825165868783058469)
                    ·
                      refine ⟨3507457467218600396823463, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18706439825165868783058469 3507457467218600396823463)
                      ·
                        rfl

theorem cell23_6830749_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 2, 2, 4, 1, 4].length) (baseStart_6830749 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830749 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830749 prefixEnd_6830749 := by exact prefixLift 6830749
  have htrace : WordTrace (prefixWord ++ tailWord_6830749) baseStart_6830749 baseEnd_6830749 := by
    simpa [prefixWord, tailWord_6830749, baseEnd_6830749] using wordTrace_append hprefix tailTrace_6830749
  have hstable : (prefixWord ++ tailWord_6830749).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830749).length < 2 ^ (prefixWord ++ tailWord_6830749).sum := by decide
  have hdescent : baseEnd_6830749 < baseStart_6830749 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830749) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830837 : List Nat := [1, 3, 6, 1, 1, 1, 1, 2, 2, 2, 3]
def baseStart_6830837 : Nat := 118140960795 + 6830837 * 2 ^ 59
def prefixEnd_6830837 : Nat := 4983230072969 + 3 ^ 40 * 6830837 * 2
def baseEnd_6830837 : Nat := 3507502653516196052523059

theorem tailTrace_6830837 : CollatzResearch.WordTrace tailWord_6830837 prefixEnd_6830837 3507502653516196052523059 := by
  unfold tailWord_6830837
  simp only [CollatzResearch.WordTrace]
  refine ⟨249141093154051637925818765, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166094062102701091950545843 249141093154051637925818765)
  ·
    refine ⟨93427909932769364222182037, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249141093154051637925818765 93427909932769364222182037)
    ·
      refine ⟨4379433278098563947914783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 93427909932769364222182037 4379433278098563947914783)
      ·
        refine ⟨6569149917147845921872175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4379433278098563947914783 6569149917147845921872175)
        ·
          refine ⟨9853724875721768882808263, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569149917147845921872175 9853724875721768882808263)
          ·
            refine ⟨14780587313582653324212395, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9853724875721768882808263 14780587313582653324212395)
            ·
              refine ⟨22170880970373979986318593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14780587313582653324212395 22170880970373979986318593)
              ·
                refine ⟨16628160727780484989738945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22170880970373979986318593 16628160727780484989738945)
                ·
                  refine ⟨12471120545835363742304209, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16628160727780484989738945 12471120545835363742304209)
                  ·
                    refine ⟨9353340409376522806728157, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12471120545835363742304209 9353340409376522806728157)
                    ·
                      refine ⟨3507502653516196052523059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353340409376522806728157 3507502653516196052523059)
                      ·
                        rfl

theorem cell23_6830837_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 6, 1, 1, 1, 1, 2, 2, 2, 3].length) (baseStart_6830837 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830837 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830837 prefixEnd_6830837 := by exact prefixLift 6830837
  have htrace : WordTrace (prefixWord ++ tailWord_6830837) baseStart_6830837 baseEnd_6830837 := by
    simpa [prefixWord, tailWord_6830837, baseEnd_6830837] using wordTrace_append hprefix tailTrace_6830837
  have hstable : (prefixWord ++ tailWord_6830837).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830837).length < 2 ^ (prefixWord ++ tailWord_6830837).sum := by decide
  have hdescent : baseEnd_6830837 < baseStart_6830837 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830837) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830839 : List Nat := [1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 4]
def baseStart_6830839 : Nat := 118140960795 + 6830839 * 2 ^ 59
def prefixEnd_6830839 : Nat := 4983230072969 + 3 ^ 40 * 6830839 * 2
def baseEnd_6830839 : Nat := 3507503680477505044698049

theorem tailTrace_6830839 : CollatzResearch.WordTrace tailWord_6830839 prefixEnd_6830839 3507503680477505044698049 := by
  unfold tailWord_6830839
  simp only [CollatzResearch.WordTrace]
  refine ⟨249141166100044392267391571, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166094110733362928178261047 249141166100044392267391571)
  ·
    refine ⟨373711749150066588401087357, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249141166100044392267391571 373711749150066588401087357)
    ·
      refine ⟨140141905931274970650407759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373711749150066588401087357 140141905931274970650407759)
      ·
        refine ⟨210212858896912455975611639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140141905931274970650407759 210212858896912455975611639)
        ·
          refine ⟨315319288345368683963417459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210212858896912455975611639 315319288345368683963417459)
          ·
            refine ⟨472978932518053025945126189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315319288345368683963417459 472978932518053025945126189)
            ·
              refine ⟨177367099694269884729422321, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 472978932518053025945126189 177367099694269884729422321)
              ·
                refine ⟨133025324770702413547066741, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177367099694269884729422321 133025324770702413547066741)
                ·
                  refine ⟨12471124197253351270037507, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133025324770702413547066741 12471124197253351270037507)
                  ·
                    refine ⟨18706686295880026905056261, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12471124197253351270037507 18706686295880026905056261)
                    ·
                      refine ⟨3507503680477505044698049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18706686295880026905056261 3507503680477505044698049)
                      ·
                        rfl

theorem cell23_6830839_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 3, 2, 5, 1, 4].length) (baseStart_6830839 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830839 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830839 prefixEnd_6830839 := by exact prefixLift 6830839
  have htrace : WordTrace (prefixWord ++ tailWord_6830839) baseStart_6830839 baseEnd_6830839 := by
    simpa [prefixWord, tailWord_6830839, baseEnd_6830839] using wordTrace_append hprefix tailTrace_6830839
  have hstable : (prefixWord ++ tailWord_6830839).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830839).length < 2 ^ (prefixWord ++ tailWord_6830839).sum := by decide
  have hdescent : baseEnd_6830839 < baseStart_6830839 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830839) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830850 : List Nat := [3, 4, 1, 1, 1, 2, 3, 1, 3, 1, 3]
def baseStart_6830850 : Nat := 118140960795 + 6830850 * 2 ^ 59
def prefixEnd_6830850 : Nat := 4983230072969 + 3 ^ 40 * 6830850 * 2
def baseEnd_6830850 : Nat := 3507509328764704501660499

theorem tailTrace_6830850 : CollatzResearch.WordTrace tailWord_6830850 prefixEnd_6830850 3507509328764704501660499 := by
  unfold tailWord_6830850
  simp only [CollatzResearch.WordTrace]
  refine ⟨62285391825751135286510501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166094378202003027430694669 62285391825751135286510501)
  ·
    refine ⟨11678510967328337866220719, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62285391825751135286510501 11678510967328337866220719)
    ·
      refine ⟨17517766450992506799331079, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11678510967328337866220719 17517766450992506799331079)
      ·
        refine ⟨26276649676488760198996619, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17517766450992506799331079 26276649676488760198996619)
        ·
          refine ⟨39414974514733140298494929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26276649676488760198996619 39414974514733140298494929)
          ·
            refine ⟨29561230886049855223871197, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39414974514733140298494929 29561230886049855223871197)
            ·
              refine ⟨11085461582268695708951699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29561230886049855223871197 11085461582268695708951699)
              ·
                refine ⟨16628192373403043563427549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11085461582268695708951699 16628192373403043563427549)
                ·
                  refine ⟨6235572140026141336285331, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16628192373403043563427549 6235572140026141336285331)
                  ·
                    refine ⟨9353358210039212004427997, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6235572140026141336285331 9353358210039212004427997)
                    ·
                      refine ⟨3507509328764704501660499, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353358210039212004427997 3507509328764704501660499)
                      ·
                        rfl

theorem cell23_6830850_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 1, 2, 3, 1, 3, 1, 3].length) (baseStart_6830850 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830850 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830850 prefixEnd_6830850 := by exact prefixLift 6830850
  have htrace : WordTrace (prefixWord ++ tailWord_6830850) baseStart_6830850 baseEnd_6830850 := by
    simpa [prefixWord, tailWord_6830850, baseEnd_6830850] using wordTrace_append hprefix tailTrace_6830850
  have hstable : (prefixWord ++ tailWord_6830850).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830850).length < 2 ^ (prefixWord ++ tailWord_6830850).sum := by decide
  have hdescent : baseEnd_6830850 < baseStart_6830850 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830850) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830859 : List Nat := [1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 3]
def baseStart_6830859 : Nat := 118140960795 + 6830859 * 2 ^ 59
def prefixEnd_6830859 : Nat := 4983230072969 + 3 ^ 40 * 6830859 * 2
def baseEnd_6830859 : Nat := 3507513950090594966447957

theorem tailTrace_6830859 : CollatzResearch.WordTrace tailWord_6830859 prefixEnd_6830859 3507513950090594966447957 := by
  unfold tailWord_6830859
  simp only [CollatzResearch.WordTrace]
  refine ⟨249141895559971935683119631, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166094597039981290455413087 249141895559971935683119631)
  ·
    refine ⟨373712843339957903524679447, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249141895559971935683119631 373712843339957903524679447)
    ·
      refine ⟨560569265009936855287019171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373712843339957903524679447 560569265009936855287019171)
      ·
        refine ⟨840853897514905282930528757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560569265009936855287019171 840853897514905282930528757)
        ·
          refine ⟨78830052892022370274737071, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 840853897514905282930528757 78830052892022370274737071)
          ·
            refine ⟨118245079338033555412105607, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78830052892022370274737071 118245079338033555412105607)
            ·
              refine ⟨177367619007050333118158411, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118245079338033555412105607 177367619007050333118158411)
              ·
                refine ⟨266051428510575499677237617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177367619007050333118158411 266051428510575499677237617)
                ·
                  refine ⟨199538571382931624757928213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 266051428510575499677237617 199538571382931624757928213)
                  ·
                    refine ⟨9353370533574919910527885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 199538571382931624757928213 9353370533574919910527885)
                    ·
                      refine ⟨3507513950090594966447957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353370533574919910527885 3507513950090594966447957)
                      ·
                        rfl

theorem cell23_6830859_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 1, 1, 1, 2, 6, 3].length) (baseStart_6830859 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830859 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830859 prefixEnd_6830859 := by exact prefixLift 6830859
  have htrace : WordTrace (prefixWord ++ tailWord_6830859) baseStart_6830859 baseEnd_6830859 := by
    simpa [prefixWord, tailWord_6830859, baseEnd_6830859] using wordTrace_append hprefix tailTrace_6830859
  have hstable : (prefixWord ++ tailWord_6830859).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830859).length < 2 ^ (prefixWord ++ tailWord_6830859).sum := by decide
  have hdescent : baseEnd_6830859 < baseStart_6830859 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830859) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830869 : List Nat := [1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 6]
def baseStart_6830869 : Nat := 118140960795 + 6830869 * 2 ^ 59
def prefixEnd_6830869 : Nat := 4983230072969 + 3 ^ 40 * 6830869 * 2
def baseEnd_6830869 : Nat := 3507519084897139927322911

theorem tailTrace_6830869 : CollatzResearch.WordTrace tailWord_6830869 prefixEnd_6830869 3507519084897139927322911 := by
  unfold tailWord_6830869
  simp only [CollatzResearch.WordTrace]
  refine ⟨249142260289935707390983661, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166094840193290471593989107 249142260289935707390983661)
  ·
    refine ⟨93428347608725890271618873, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249142260289935707390983661 93428347608725890271618873)
    ·
      refine ⟨70071260706544417703714155, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93428347608725890271618873 70071260706544417703714155)
      ·
        refine ⟨105106891059816626555571233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70071260706544417703714155 105106891059816626555571233)
        ·
          refine ⟨78830168294862469916678425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105106891059816626555571233 78830168294862469916678425)
          ·
            refine ⟨59122626221146852437508819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78830168294862469916678425 59122626221146852437508819)
            ·
              refine ⟨88683939331720278656263229, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59122626221146852437508819 88683939331720278656263229)
              ·
                refine ⟨33256477249395104496098711, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88683939331720278656263229 33256477249395104496098711)
                ·
                  refine ⟨49884715874092656744148067, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33256477249395104496098711 49884715874092656744148067)
                  ·
                    refine ⟨74827073811138985116222101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49884715874092656744148067 74827073811138985116222101)
                    ·
                      refine ⟨3507519084897139927322911, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74827073811138985116222101 3507519084897139927322911)
                      ·
                        rfl

theorem cell23_6830869_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 2, 1, 3, 1, 1, 6].length) (baseStart_6830869 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830869 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830869 prefixEnd_6830869 := by exact prefixLift 6830869
  have htrace : WordTrace (prefixWord ++ tailWord_6830869) baseStart_6830869 baseEnd_6830869 := by
    simpa [prefixWord, tailWord_6830869, baseEnd_6830869] using wordTrace_append hprefix tailTrace_6830869
  have hstable : (prefixWord ++ tailWord_6830869).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830869).length < 2 ^ (prefixWord ++ tailWord_6830869).sum := by decide
  have hdescent : baseEnd_6830869 < baseStart_6830869 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830869) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830877 : List Nat := [1, 4, 2, 4, 1, 1, 2, 1, 2, 3, 2]
def baseStart_6830877 : Nat := 118140960795 + 6830877 * 2 ^ 59
def prefixEnd_6830877 : Nat := 4983230072969 + 3 ^ 40 * 6830877 * 2
def baseEnd_6830877 : Nat := 3507523192742375896022875

theorem tailTrace_6830877 : CollatzResearch.WordTrace tailWord_6830877 prefixEnd_6830877 3507523192742375896022875 := by
  unfold tailWord_6830877
  simp only [CollatzResearch.WordTrace]
  refine ⟨249142552073906724757274885, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166095034715937816504849923 249142552073906724757274885)
  ·
    refine ⟨46714228513857510891989041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249142552073906724757274885 46714228513857510891989041)
    ·
      refine ⟨35035671385393133168991781, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46714228513857510891989041 35035671385393133168991781)
      ·
        refine ⟨6569188384761212469185959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 35035671385393133168991781 6569188384761212469185959)
        ·
          refine ⟨9853782577141818703778939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6569188384761212469185959 9853782577141818703778939)
          ·
            refine ⟨14780673865712728055668409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9853782577141818703778939 14780673865712728055668409)
            ·
              refine ⟨11085505399284546041751307, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14780673865712728055668409 11085505399284546041751307)
              ·
                refine ⟨16628258098926819062626961, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11085505399284546041751307 16628258098926819062626961)
                ·
                  refine ⟨12471193574195114296970221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16628258098926819062626961 12471193574195114296970221)
                  ·
                    refine ⟨4676697590323167861363833, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12471193574195114296970221 4676697590323167861363833)
                    ·
                      refine ⟨3507523192742375896022875, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676697590323167861363833 3507523192742375896022875)
                      ·
                        rfl

theorem cell23_6830877_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 4, 1, 1, 2, 1, 2, 3, 2].length) (baseStart_6830877 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830877 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830877 prefixEnd_6830877 := by exact prefixLift 6830877
  have htrace : WordTrace (prefixWord ++ tailWord_6830877) baseStart_6830877 baseEnd_6830877 := by
    simpa [prefixWord, tailWord_6830877, baseEnd_6830877] using wordTrace_append hprefix tailTrace_6830877
  have hstable : (prefixWord ++ tailWord_6830877).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830877).length < 2 ^ (prefixWord ++ tailWord_6830877).sum := by decide
  have hdescent : baseEnd_6830877 < baseStart_6830877 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830877) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830879 : List Nat := [1, 1, 2, 4, 2, 2, 2, 9]
def baseStart_6830879 : Nat := 118140960795 + 6830879 * 2 ^ 59
def prefixEnd_6830879 : Nat := 4983230072969 + 3 ^ 40 * 6830879 * 2
def baseEnd_6830879 : Nat := 129908304433469810673995

theorem tailTrace_6830879 : CollatzResearch.WordTrace tailWord_6830879 prefixEnd_6830879 129908304433469810673995 := by
  unfold tailWord_6830879
  simp only [CollatzResearch.WordTrace]
  refine ⟨249142625019899479098847691, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166095083346599652732565127 249142625019899479098847691)
  ·
    refine ⟨373713937529849218648271537, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249142625019899479098847691 373713937529849218648271537)
    ·
      refine ⟨280285453147386913986203653, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373713937529849218648271537 280285453147386913986203653)
      ·
        refine ⟨52553522465135046372413185, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280285453147386913986203653 52553522465135046372413185)
        ·
          refine ⟨39415141848851284779309889, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52553522465135046372413185 39415141848851284779309889)
          ·
            refine ⟨29561356386638463584482417, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39415141848851284779309889 29561356386638463584482417)
            ·
              refine ⟨22171017289978847688361813, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29561356386638463584482417 22171017289978847688361813)
              ·
                refine ⟨129908304433469810673995, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22171017289978847688361813 129908304433469810673995)
                ·
                  rfl

theorem cell23_6830879_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 2, 2, 2, 9].length) (baseStart_6830879 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830879 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830879 prefixEnd_6830879 := by exact prefixLift 6830879
  have htrace : WordTrace (prefixWord ++ tailWord_6830879) baseStart_6830879 baseEnd_6830879 := by
    simpa [prefixWord, tailWord_6830879, baseEnd_6830879] using wordTrace_append hprefix tailTrace_6830879
  have hstable : (prefixWord ++ tailWord_6830879).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830879).length < 2 ^ (prefixWord ++ tailWord_6830879).sum := by decide
  have hdescent : baseEnd_6830879 < baseStart_6830879 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830879) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830919 : List Nat := [1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 5]
def baseStart_6830919 : Nat := 118140960795 + 6830919 * 2 ^ 59
def prefixEnd_6830919 : Nat := 4983230072969 + 3 ^ 40 * 6830919 * 2
def baseEnd_6830919 : Nat := 3507544758929864731697681

theorem tailTrace_6830919 : CollatzResearch.WordTrace tailWord_6830919 prefixEnd_6830919 3507544758929864731697681 := by
  unfold tailWord_6830919
  simp only [CollatzResearch.WordTrace]
  refine ⟨249144083939754565930303811, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166096055959836377286869207 249144083939754565930303811)
  ·
    refine ⟨373716125909631848895455717, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249144083939754565930303811 373716125909631848895455717)
    ·
      refine ⟨70071773608055971667897947, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373716125909631848895455717 70071773608055971667897947)
      ·
        refine ⟨105107660412083957501846921, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70071773608055971667897947 105107660412083957501846921)
        ·
          refine ⟨78830745309062968126385191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105107660412083957501846921 78830745309062968126385191)
          ·
            refine ⟨118246117963594452189577787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78830745309062968126385191 118246117963594452189577787)
            ·
              refine ⟨177369176945391678284366681, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118246117963594452189577787 177369176945391678284366681)
              ·
                refine ⟨133026882709043758713275011, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177369176945391678284366681 133026882709043758713275011)
                ·
                  refine ⟨199540324063565638069912517, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133026882709043758713275011 199540324063565638069912517)
                  ·
                    refine ⟨37413810761918557138108597, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 199540324063565638069912517 37413810761918557138108597)
                    ·
                      refine ⟨3507544758929864731697681, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37413810761918557138108597 3507544758929864731697681)
                      ·
                        rfl

theorem cell23_6830919_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 1, 1, 2, 1, 4, 5].length) (baseStart_6830919 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830919 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830919 prefixEnd_6830919 := by exact prefixLift 6830919
  have htrace : WordTrace (prefixWord ++ tailWord_6830919) baseStart_6830919 baseEnd_6830919 := by
    simpa [prefixWord, tailWord_6830919, baseEnd_6830919] using wordTrace_append hprefix tailTrace_6830919
  have hstable : (prefixWord ++ tailWord_6830919).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830919).length < 2 ^ (prefixWord ++ tailWord_6830919).sum := by decide
  have hdescent : baseEnd_6830919 < baseStart_6830919 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830919) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830933 : List Nat := [1, 3, 2, 2, 2, 1, 1, 3, 3, 3, 2]
def baseStart_6830933 : Nat := 118140960795 + 6830933 * 2 ^ 59
def prefixEnd_6830933 : Nat := 4983230072969 + 3 ^ 40 * 6830933 * 2
def baseEnd_6830933 : Nat := 3507551947659027676922617

theorem tailTrace_6830933 : CollatzResearch.WordTrace tailWord_6830933 prefixEnd_6830933 3507551947659027676922617 := by
  unfold tailWord_6830933
  simp only [CollatzResearch.WordTrace]
  refine ⟨249144594561703846321313453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166096396374469230880875635 249144594561703846321313453)
  ·
    refine ⟨93429222960638942370492545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249144594561703846321313453 93429222960638942370492545)
    ·
      refine ⟨70071917220479206777869409, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93429222960638942370492545 70071917220479206777869409)
      ·
        refine ⟨52553937915359405083402057, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70071917220479206777869409 52553937915359405083402057)
        ·
          refine ⟨39415453436519553812551543, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52553937915359405083402057 39415453436519553812551543)
          ·
            refine ⟨59123180154779330718827315, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39415453436519553812551543 59123180154779330718827315)
            ·
              refine ⟨88684770232168996078240973, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59123180154779330718827315 88684770232168996078240973)
              ·
                refine ⟨33256788837063373529340365, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88684770232168996078240973 33256788837063373529340365)
                ·
                  refine ⟨12471295813898765073502637, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33256788837063373529340365 12471295813898765073502637)
                  ·
                    refine ⟨4676735930212036902563489, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12471295813898765073502637 4676735930212036902563489)
                    ·
                      refine ⟨3507551947659027676922617, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676735930212036902563489 3507551947659027676922617)
                      ·
                        rfl

theorem cell23_6830933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 2, 1, 1, 3, 3, 3, 2].length) (baseStart_6830933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830933 prefixEnd_6830933 := by exact prefixLift 6830933
  have htrace : WordTrace (prefixWord ++ tailWord_6830933) baseStart_6830933 baseEnd_6830933 := by
    simpa [prefixWord, tailWord_6830933, baseEnd_6830933] using wordTrace_append hprefix tailTrace_6830933
  have hstable : (prefixWord ++ tailWord_6830933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830933).length < 2 ^ (prefixWord ++ tailWord_6830933).sum := by decide
  have hdescent : baseEnd_6830933 < baseStart_6830933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6830974 : List Nat := [4, 2, 3, 1, 3, 1, 1, 1, 1, 3, 3]
def baseStart_6830974 : Nat := 118140960795 + 6830974 * 2 ^ 59
def prefixEnd_6830974 : Nat := 4983230072969 + 3 ^ 40 * 6830974 * 2
def baseEnd_6830974 : Nat := 3507573000365862016509929

theorem tailTrace_6830974 : CollatzResearch.WordTrace tailWord_6830974 prefixEnd_6830974 3507573000365862016509929 := by
  unfold tailWord_6830974
  simp only [CollatzResearch.WordTrace]
  refine ⟨31143261244319413790444497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166097393303036873549037317 31143261244319413790444497)
  ·
    refine ⟨23357445933239560342833373, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31143261244319413790444497 23357445933239560342833373)
    ·
      refine ⟨8759042224964835128562515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23357445933239560342833373 8759042224964835128562515)
      ·
        refine ⟨13138563337447252692843773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759042224964835128562515 13138563337447252692843773)
        ·
          refine ⟨4926961251542719759816415, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13138563337447252692843773 4926961251542719759816415)
          ·
            refine ⟨7390441877314079639724623, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4926961251542719759816415 7390441877314079639724623)
            ·
              refine ⟨11085662815971119459586935, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390441877314079639724623 11085662815971119459586935)
              ·
                refine ⟨16628494223956679189380403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11085662815971119459586935 16628494223956679189380403)
                ·
                  refine ⟨24942741335935018784070605, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16628494223956679189380403 24942741335935018784070605)
                  ·
                    refine ⟨9353528000975632044026477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24942741335935018784070605 9353528000975632044026477)
                    ·
                      refine ⟨3507573000365862016509929, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353528000975632044026477 3507573000365862016509929)
                      ·
                        rfl

theorem cell23_6830974_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 3, 1, 3, 1, 1, 1, 1, 3, 3].length) (baseStart_6830974 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6830974 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6830974 prefixEnd_6830974 := by exact prefixLift 6830974
  have htrace : WordTrace (prefixWord ++ tailWord_6830974) baseStart_6830974 baseEnd_6830974 := by
    simpa [prefixWord, tailWord_6830974, baseEnd_6830974] using wordTrace_append hprefix tailTrace_6830974
  have hstable : (prefixWord ++ tailWord_6830974).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6830974).length < 2 ^ (prefixWord ++ tailWord_6830974).sum := by decide
  have hdescent : baseEnd_6830974 < baseStart_6830974 := by decide
  rcases family_descends (prefixWord ++ tailWord_6830974) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831130 : List Nat := [3, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2]
def baseStart_6831130 : Nat := 118140960795 + 6831130 * 2 ^ 59
def prefixEnd_6831130 : Nat := 4983230072969 + 3 ^ 40 * 6831130 * 2
def baseEnd_6831130 : Nat := 3507653103347963406159211

theorem tailTrace_6831130 : CollatzResearch.WordTrace tailWord_6831130 prefixEnd_6831130 3507653103347963406159211 := by
  unfold tailWord_6831130
  simp only [CollatzResearch.WordTrace]
  refine ⟨62287944935497537241558711, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166101186494660099310823229 62287944935497537241558711)
  ·
    refine ⟨93431917403246305862338067, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62287944935497537241558711 93431917403246305862338067)
    ·
      refine ⟨140147876104869458793507101, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93431917403246305862338067 140147876104869458793507101)
      ·
        refine ⟨52555453539326047047565163, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140147876104869458793507101 52555453539326047047565163)
        ·
          refine ⟨78833180308989070571347745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52555453539326047047565163 78833180308989070571347745)
          ·
            refine ⟨59124885231741802928510809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78833180308989070571347745 59124885231741802928510809)
            ·
              refine ⟨44343663923806352196383107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59124885231741802928510809 44343663923806352196383107)
              ·
                refine ⟨66515495885709528294574661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44343663923806352196383107 66515495885709528294574661)
                ·
                  refine ⟨12471655478570536555232749, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66515495885709528294574661 12471655478570536555232749)
                  ·
                    refine ⟨4676870804463951208212281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12471655478570536555232749 4676870804463951208212281)
                    ·
                      refine ⟨3507653103347963406159211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676870804463951208212281 3507653103347963406159211)
                      ·
                        rfl

theorem cell23_6831130_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 3, 1, 2, 2, 1, 4, 3, 2].length) (baseStart_6831130 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831130 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831130 prefixEnd_6831130 := by exact prefixLift 6831130
  have htrace : WordTrace (prefixWord ++ tailWord_6831130) baseStart_6831130 baseEnd_6831130 := by
    simpa [prefixWord, tailWord_6831130, baseEnd_6831130] using wordTrace_append hprefix tailTrace_6831130
  have hstable : (prefixWord ++ tailWord_6831130).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831130).length < 2 ^ (prefixWord ++ tailWord_6831130).sum := by decide
  have hdescent : baseEnd_6831130 < baseStart_6831130 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831130) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831137 : List Nat := [1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 3]
def baseStart_6831137 : Nat := 118140960795 + 6831137 * 2 ^ 59
def prefixEnd_6831137 : Nat := 4983230072969 + 3 ^ 40 * 6831137 * 2
def baseEnd_6831137 : Nat := 3507656697712544878771679

theorem tailTrace_6831137 : CollatzResearch.WordTrace tailWord_6831137 prefixEnd_6831137 3507656697712544878771679 := by
  unfold tailWord_6831137
  simp only [CollatzResearch.WordTrace]
  refine ⟨249152035052964789161739665, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166101356701976526107826443 249152035052964789161739665)
  ·
    refine ⟨186864026289723591871304749, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249152035052964789161739665 186864026289723591871304749)
    ·
      refine ⟨70074009858646346951739281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186864026289723591871304749 70074009858646346951739281)
      ·
        refine ⟨52555507393984760213804461, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70074009858646346951739281 52555507393984760213804461)
        ·
          refine ⟨19708315272744285080176673, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52555507393984760213804461 19708315272744285080176673)
          ·
            refine ⟨14781236454558213810132505, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19708315272744285080176673 14781236454558213810132505)
            ·
              refine ⟨11085927340918660357599379, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14781236454558213810132505 11085927340918660357599379)
              ·
                refine ⟨16628891011377990536399069, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11085927340918660357599379 16628891011377990536399069)
                ·
                  refine ⟨6235834129266746451149651, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16628891011377990536399069 6235834129266746451149651)
                  ·
                    refine ⟨9353751193900119676724477, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6235834129266746451149651 9353751193900119676724477)
                    ·
                      refine ⟨3507656697712544878771679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353751193900119676724477 3507656697712544878771679)
                      ·
                        rfl

theorem cell23_6831137_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 2, 3, 2, 2, 1, 3, 1, 3].length) (baseStart_6831137 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831137 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831137 prefixEnd_6831137 := by exact prefixLift 6831137
  have htrace : WordTrace (prefixWord ++ tailWord_6831137) baseStart_6831137 baseEnd_6831137 := by
    simpa [prefixWord, tailWord_6831137, baseEnd_6831137] using wordTrace_append hprefix tailTrace_6831137
  have hstable : (prefixWord ++ tailWord_6831137).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831137).length < 2 ^ (prefixWord ++ tailWord_6831137).sum := by decide
  have hdescent : baseEnd_6831137 < baseStart_6831137 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831137) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831160 : List Nat := [2, 1, 2, 1, 5, 1, 1, 4, 1, 1, 4]
def baseStart_6831160 : Nat := 118140960795 + 6831160 * 2 ^ 59
def prefixEnd_6831160 : Nat := 4983230072969 + 3 ^ 40 * 6831160 * 2
def baseEnd_6831160 : Nat := 3507668507767598288784073

theorem tailTrace_6831160 : CollatzResearch.WordTrace tailWord_6831160 prefixEnd_6831160 3507668507767598288784073 := by
  unfold tailWord_6831160
  simp only [CollatzResearch.WordTrace]
  refine ⟨124576436965940732044913467, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166101915954587642726551289 124576436965940732044913467)
  ·
    refine ⟨186864655448911098067370201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124576436965940732044913467 186864655448911098067370201)
    ·
      refine ⟨140148491586683323550527651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186864655448911098067370201 140148491586683323550527651)
      ·
        refine ⟨210222737380024985325791477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140148491586683323550527651 210222737380024985325791477)
        ·
          refine ⟨19708381629377342374292951, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210222737380024985325791477 19708381629377342374292951)
          ·
            refine ⟨29562572444066013561439427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19708381629377342374292951 29562572444066013561439427)
            ·
              refine ⟨44343858666099020342159141, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29562572444066013561439427 44343858666099020342159141)
              ·
                refine ⟨8314473499893566314154839, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44343858666099020342159141 8314473499893566314154839)
                ·
                  refine ⟨12471710249840349471232259, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8314473499893566314154839 12471710249840349471232259)
                  ·
                    refine ⟨18707565374760524206848389, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12471710249840349471232259 18707565374760524206848389)
                    ·
                      refine ⟨3507668507767598288784073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18707565374760524206848389 3507668507767598288784073)
                      ·
                        rfl

theorem cell23_6831160_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 5, 1, 1, 4, 1, 1, 4].length) (baseStart_6831160 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831160 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831160 prefixEnd_6831160 := by exact prefixLift 6831160
  have htrace : WordTrace (prefixWord ++ tailWord_6831160) baseStart_6831160 baseEnd_6831160 := by
    simpa [prefixWord, tailWord_6831160, baseEnd_6831160] using wordTrace_append hprefix tailTrace_6831160
  have hstable : (prefixWord ++ tailWord_6831160).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831160).length < 2 ^ (prefixWord ++ tailWord_6831160).sum := by decide
  have hdescent : baseEnd_6831160 < baseStart_6831160 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831160) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831173 : List Nat := [1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 4]
def baseStart_6831173 : Nat := 118140960795 + 6831173 * 2 ^ 59
def prefixEnd_6831173 : Nat := 4983230072969 + 3 ^ 40 * 6831173 * 2
def baseEnd_6831173 : Nat := 3507675183016106737921513

theorem tailTrace_6831173 : CollatzResearch.WordTrace tailWord_6831173 prefixEnd_6831173 3507675183016106737921513 := by
  unfold tailWord_6831173
  simp only [CollatzResearch.WordTrace]
  refine ⟨249153348080834367310050173, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166102232053889578206700115 249153348080834367310050173)
  ·
    refine ⟨93432505530312887741268815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249153348080834367310050173 93432505530312887741268815)
    ·
      refine ⟨140148758295469331611903223, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93432505530312887741268815 140148758295469331611903223)
      ·
        refine ⟨210223137443203997417854835, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140148758295469331611903223 210223137443203997417854835)
        ·
          refine ⟨315334706164805996126782253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210223137443203997417854835 315334706164805996126782253)
          ·
            refine ⟨118250514811802248547543345, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315334706164805996126782253 118250514811802248547543345)
            ·
              refine ⟨88687886108851686410657509, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118250514811802248547543345 88687886108851686410657509)
              ·
                refine ⟨16628978645409691201998283, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88687886108851686410657509 16628978645409691201998283)
                ·
                  refine ⟨24943467968114536802997425, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16628978645409691201998283 24943467968114536802997425)
                  ·
                    refine ⟨18707600976085902602248069, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24943467968114536802997425 18707600976085902602248069)
                    ·
                      refine ⟨3507675183016106737921513, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18707600976085902602248069 3507675183016106737921513)
                      ·
                        rfl

theorem cell23_6831173_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 3, 2, 4, 1, 2, 4].length) (baseStart_6831173 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831173 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831173 prefixEnd_6831173 := by exact prefixLift 6831173
  have htrace : WordTrace (prefixWord ++ tailWord_6831173) baseStart_6831173 baseEnd_6831173 := by
    simpa [prefixWord, tailWord_6831173, baseEnd_6831173] using wordTrace_append hprefix tailTrace_6831173
  have hstable : (prefixWord ++ tailWord_6831173).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831173).length < 2 ^ (prefixWord ++ tailWord_6831173).sum := by decide
  have hdescent : baseEnd_6831173 < baseStart_6831173 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831173) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831193 : List Nat := [1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 3]
def baseStart_6831193 : Nat := 118140960795 + 6831193 * 2 ^ 59
def prefixEnd_6831193 : Nat := 4983230072969 + 3 ^ 40 * 6831193 * 2
def baseEnd_6831193 : Nat := 3507685452629196659671421

theorem tailTrace_6831193 : CollatzResearch.WordTrace tailWord_6831193 prefixEnd_6831193 3507685452629196659671421 := by
  unfold tailWord_6831193
  simp only [CollatzResearch.WordTrace]
  refine ⟨249154077540761910725778233, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166102718360507940483852155 249154077540761910725778233)
  ·
    refine ⟨186865558155571433044333675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249154077540761910725778233 186865558155571433044333675)
    ·
      refine ⟨280298337233357149566500513, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186865558155571433044333675 280298337233357149566500513)
      ·
        refine ⟨210223752925017862174875385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280298337233357149566500513 210223752925017862174875385)
        ·
          refine ⟨157667814693763396631156539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210223752925017862174875385 157667814693763396631156539)
          ·
            refine ⟨236501722040645094946734809, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157667814693763396631156539 236501722040645094946734809)
            ·
              refine ⟨177376291530483821210051107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236501722040645094946734809 177376291530483821210051107)
              ·
                refine ⟨266064437295725731815076661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177376291530483821210051107 266064437295725731815076661)
                ·
                  refine ⟨24943540996474287357663437, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266064437295725731815076661 24943540996474287357663437)
                  ·
                    refine ⟨9353827873677857759123789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24943540996474287357663437 9353827873677857759123789)
                    ·
                      refine ⟨3507685452629196659671421, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353827873677857759123789 3507685452629196659671421)
                      ·
                        rfl

theorem cell23_6831193_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 2, 1, 2, 1, 5, 3, 3].length) (baseStart_6831193 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831193 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831193 prefixEnd_6831193 := by exact prefixLift 6831193
  have htrace : WordTrace (prefixWord ++ tailWord_6831193) baseStart_6831193 baseEnd_6831193 := by
    simpa [prefixWord, tailWord_6831193, baseEnd_6831193] using wordTrace_append hprefix tailTrace_6831193
  have hstable : (prefixWord ++ tailWord_6831193).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831193).length < 2 ^ (prefixWord ++ tailWord_6831193).sum := by decide
  have hdescent : baseEnd_6831193 < baseStart_6831193 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831193) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831214 : List Nat := [4, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3]
def baseStart_6831214 : Nat := 118140960795 + 6831214 * 2 ^ 59
def prefixEnd_6831214 : Nat := 4983230072969 + 3 ^ 40 * 6831214 * 2
def baseEnd_6831214 : Nat := 3507696235722941077508825

theorem tailTrace_6831214 : CollatzResearch.WordTrace tailWord_6831214 prefixEnd_6831214 3507696235722941077508825 := by
  unfold tailWord_6831214
  simp only [CollatzResearch.WordTrace]
  refine ⟨31144355434210728914036587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166103228982457220874861797 31144355434210728914036587)
  ·
    refine ⟨46716533151316093371054881, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31144355434210728914036587 46716533151316093371054881)
    ·
      refine ⟨35037399863487070028291161, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46716533151316093371054881 35037399863487070028291161)
      ·
        refine ⟨26278049897615302521218371, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35037399863487070028291161 26278049897615302521218371)
        ·
          refine ⟨39417074846422953781827557, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26278049897615302521218371 39417074846422953781827557)
          ·
            refine ⟨7390701533704303834092667, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39417074846422953781827557 7390701533704303834092667)
            ·
              refine ⟨11086052300556455751139001, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390701533704303834092667 11086052300556455751139001)
              ·
                refine ⟨8314539225417341813354251, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11086052300556455751139001 8314539225417341813354251)
                ·
                  refine ⟨12471808838126012720031377, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8314539225417341813354251 12471808838126012720031377)
                  ·
                    refine ⟨9353856628594509540023533, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12471808838126012720031377 9353856628594509540023533)
                    ·
                      refine ⟨3507696235722941077508825, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353856628594509540023533 3507696235722941077508825)
                      ·
                        rfl

theorem cell23_6831214_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 2, 1, 4, 1, 2, 1, 2, 3].length) (baseStart_6831214 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831214 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831214 prefixEnd_6831214 := by exact prefixLift 6831214
  have htrace : WordTrace (prefixWord ++ tailWord_6831214) baseStart_6831214 baseEnd_6831214 := by
    simpa [prefixWord, tailWord_6831214, baseEnd_6831214] using wordTrace_append hprefix tailTrace_6831214
  have hstable : (prefixWord ++ tailWord_6831214).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831214).length < 2 ^ (prefixWord ++ tailWord_6831214).sum := by decide
  have hdescent : baseEnd_6831214 < baseStart_6831214 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831214) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831250 : List Nat := [3, 2, 3, 1, 1, 2, 1, 1, 2, 3, 4]
def baseStart_6831250 : Nat := 118140960795 + 6831250 * 2 ^ 59
def prefixEnd_6831250 : Nat := 4983230072969 + 3 ^ 40 * 6831250 * 2
def baseEnd_6831250 : Nat := 3507714721026502936658659

theorem tailTrace_6831250 : CollatzResearch.WordTrace tailWord_6831250 prefixEnd_6831250 3507714721026502936658659 := by
  unfold tailWord_6831250
  simp only [CollatzResearch.WordTrace]
  refine ⟨62289039125388852365150801, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166104104334370272973735469 62289039125388852365150801)
  ·
    refine ⟨46716779344041639273863101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62289039125388852365150801 46716779344041639273863101)
    ·
      refine ⟨17518792254015614727698663, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46716779344041639273863101 17518792254015614727698663)
      ·
        refine ⟨26278188381023422091547995, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17518792254015614727698663 26278188381023422091547995)
        ·
          refine ⟨39417282571535133137321993, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26278188381023422091547995 39417282571535133137321993)
          ·
            refine ⟨29562961928651349852991495, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39417282571535133137321993 29562961928651349852991495)
            ·
              refine ⟨44344442892977024779487243, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29562961928651349852991495 44344442892977024779487243)
              ·
                refine ⟨66516664339465537169230865, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44344442892977024779487243 66516664339465537169230865)
                ·
                  refine ⟨49887498254599152876923149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66516664339465537169230865 49887498254599152876923149)
                  ·
                    refine ⟨18707811845474682328846181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49887498254599152876923149 18707811845474682328846181)
                    ·
                      refine ⟨3507714721026502936658659, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18707811845474682328846181 3507714721026502936658659)
                      ·
                        rfl

theorem cell23_6831250_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 1, 2, 1, 1, 2, 3, 4].length) (baseStart_6831250 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831250 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831250 prefixEnd_6831250 := by exact prefixLift 6831250
  have htrace : WordTrace (prefixWord ++ tailWord_6831250) baseStart_6831250 baseEnd_6831250 := by
    simpa [prefixWord, tailWord_6831250, baseEnd_6831250] using wordTrace_append hprefix tailTrace_6831250
  have hstable : (prefixWord ++ tailWord_6831250).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831250).length < 2 ^ (prefixWord ++ tailWord_6831250).sum := by decide
  have hdescent : baseEnd_6831250 < baseStart_6831250 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831250) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831253 : List Nat := [1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 5]
def baseStart_6831253 : Nat := 118140960795 + 6831253 * 2 ^ 59
def prefixEnd_6831253 : Nat := 4983230072969 + 3 ^ 40 * 6831253 * 2
def baseEnd_6831253 : Nat := 3507716261468466424921145

theorem tailTrace_6831253 : CollatzResearch.WordTrace tailWord_6831253 prefixEnd_6831253 3507716261468466424921145 := by
  unfold tailWord_6831253
  simp only [CollatzResearch.WordTrace]
  refine ⟨249156265920544540972962413, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166104177280363027315308275 249156265920544540972962413)
  ·
    refine ⟨93433599720204202864860905, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249156265920544540972962413 93433599720204202864860905)
    ·
      refine ⟨70075199790153152148645679, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93433599720204202864860905 70075199790153152148645679)
      ·
        refine ⟨105112799685229728222968519, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70075199790153152148645679 105112799685229728222968519)
        ·
          refine ⟨157669199527844592334452779, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105112799685229728222968519 157669199527844592334452779)
          ·
            refine ⟨236503799291766888501679169, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157669199527844592334452779 236503799291766888501679169)
            ·
              refine ⟨177377849468825166376259377, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 236503799291766888501679169 177377849468825166376259377)
              ·
                refine ⟨133033387101618874782194533, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177377849468825166376259377 133033387101618874782194533)
                ·
                  refine ⟨24943760081553539021661475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 133033387101618874782194533 24943760081553539021661475)
                  ·
                    refine ⟨37415640122330308532492213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24943760081553539021661475 37415640122330308532492213)
                    ·
                      refine ⟨3507716261468466424921145, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37415640122330308532492213 3507716261468466424921145)
                      ·
                        rfl

theorem cell23_6831253_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 2, 2, 4, 1, 5].length) (baseStart_6831253 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831253 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831253 prefixEnd_6831253 := by exact prefixLift 6831253
  have htrace : WordTrace (prefixWord ++ tailWord_6831253) baseStart_6831253 baseEnd_6831253 := by
    simpa [prefixWord, tailWord_6831253, baseEnd_6831253] using wordTrace_append hprefix tailTrace_6831253
  have hstable : (prefixWord ++ tailWord_6831253).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831253).length < 2 ^ (prefixWord ++ tailWord_6831253).sum := by decide
  have hdescent : baseEnd_6831253 < baseStart_6831253 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831253) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831260 : List Nat := [2, 2, 3, 2, 1, 3, 1, 1, 2, 6]
def baseStart_6831260 : Nat := 118140960795 + 6831260 * 2 ^ 59
def prefixEnd_6831260 : Nat := 4983230072969 + 3 ^ 40 * 6831260 * 2
def baseEnd_6831260 : Nat := 1169239951944349299177871

theorem tailTrace_6831260 : CollatzResearch.WordTrace tailWord_6831260 prefixEnd_6831260 1169239951944349299177871 := by
  unfold tailWord_6831260
  simp only [CollatzResearch.WordTrace]
  refine ⟨124578260615759590584233617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166104347487679454112311489 124578260615759590584233617)
  ·
    refine ⟨93433695461819692938175213, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124578260615759590584233617 93433695461819692938175213)
    ·
      refine ⟨35037635798182384851815705, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93433695461819692938175213 35037635798182384851815705)
      ·
        refine ⟨26278226848636788638861779, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35037635798182384851815705 26278226848636788638861779)
        ·
          refine ⟨39417340272955182958292669, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26278226848636788638861779 39417340272955182958292669)
          ·
            refine ⟨14781502602358193609359751, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39417340272955182958292669 14781502602358193609359751)
            ·
              refine ⟨22172253903537290414039627, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14781502602358193609359751 22172253903537290414039627)
              ·
                refine ⟨33258380855305935621059441, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22172253903537290414039627 33258380855305935621059441)
                ·
                  refine ⟨24943785641479451715794581, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33258380855305935621059441 24943785641479451715794581)
                  ·
                    refine ⟨1169239951944349299177871, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24943785641479451715794581 1169239951944349299177871)
                    ·
                      rfl

theorem cell23_6831260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 3, 1, 1, 2, 6].length) (baseStart_6831260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831260 prefixEnd_6831260 := by exact prefixLift 6831260
  have htrace : WordTrace (prefixWord ++ tailWord_6831260) baseStart_6831260 baseEnd_6831260 := by
    simpa [prefixWord, tailWord_6831260, baseEnd_6831260] using wordTrace_append hprefix tailTrace_6831260
  have hstable : (prefixWord ++ tailWord_6831260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831260).length < 2 ^ (prefixWord ++ tailWord_6831260).sum := by decide
  have hdescent : baseEnd_6831260 < baseStart_6831260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831297 : List Nat := [1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 4]
def baseStart_6831297 : Nat := 118140960795 + 6831297 * 2 ^ 59
def prefixEnd_6831297 : Nat := 4983230072969 + 3 ^ 40 * 6831297 * 2
def baseEnd_6831297 : Nat := 3507738854617264252770943

theorem tailTrace_6831297 : CollatzResearch.WordTrace tailWord_6831297 prefixEnd_6831297 3507738854617264252770943 := by
  unfold tailWord_6831297
  simp only [CollatzResearch.WordTrace]
  refine ⟨249157870732385136487564145, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166105247154923424325042763 249157870732385136487564145)
  ·
    refine ⟨186868403049288852365673109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249157870732385136487564145 186868403049288852365673109)
    ·
      refine ⟨8759456392935414954640927, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186868403049288852365673109 8759456392935414954640927)
      ·
        refine ⟨13139184589403122431961391, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759456392935414954640927 13139184589403122431961391)
        ·
          refine ⟨19708776884104683647942087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139184589403122431961391 19708776884104683647942087)
          ·
            refine ⟨29563165326157025471913131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19708776884104683647942087 29563165326157025471913131)
            ·
              refine ⟨44344747989235538207869697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29563165326157025471913131 44344747989235538207869697)
              ·
                refine ⟨33258560991926653655902273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44344747989235538207869697 33258560991926653655902273)
                ·
                  refine ⟨24943920743944990241926705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33258560991926653655902273 24943920743944990241926705)
                  ·
                    refine ⟨18707940557958742681445029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24943920743944990241926705 18707940557958742681445029)
                    ·
                      refine ⟨3507738854617264252770943, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18707940557958742681445029 3507738854617264252770943)
                      ·
                        rfl

theorem cell23_6831297_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 6, 1, 1, 1, 1, 2, 2, 2, 4].length) (baseStart_6831297 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831297 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831297 prefixEnd_6831297 := by exact prefixLift 6831297
  have htrace : WordTrace (prefixWord ++ tailWord_6831297) baseStart_6831297 baseEnd_6831297 := by
    simpa [prefixWord, tailWord_6831297, baseEnd_6831297] using wordTrace_append hprefix tailTrace_6831297
  have hstable : (prefixWord ++ tailWord_6831297).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831297).length < 2 ^ (prefixWord ++ tailWord_6831297).sum := by decide
  have hdescent : baseEnd_6831297 < baseStart_6831297 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831297) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831313 : List Nat := [1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 7]
def baseStart_6831313 : Nat := 118140960795 + 6831313 * 2 ^ 59
def prefixEnd_6831313 : Nat := 4983230072969 + 3 ^ 40 * 6831313 * 2
def baseEnd_6831313 : Nat := 3507747070307736190170869

theorem tailTrace_6831313 : CollatzResearch.WordTrace tailWord_6831313 prefixEnd_6831313 3507747070307736190170869 := by
  unfold tailWord_6831313
  simp only [CollatzResearch.WordTrace]
  refine ⟨249158454300327171220146593, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166105636200218114146764395 249158454300327171220146593)
  ·
    refine ⟨186868840725245378415109945, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249158454300327171220146593 186868840725245378415109945)
    ·
      refine ⟨140151630543934033811332459, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186868840725245378415109945 140151630543934033811332459)
      ·
        refine ⟨210227445815901050716998689, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140151630543934033811332459 210227445815901050716998689)
        ·
          refine ⟨157670584361925788037749017, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210227445815901050716998689 157670584361925788037749017)
          ·
            refine ⟨118252938271444341028311763, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157670584361925788037749017 118252938271444341028311763)
            ·
              refine ⟨177379407407166511542467645, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118252938271444341028311763 177379407407166511542467645)
              ·
                refine ⟨66517277777687441828425367, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177379407407166511542467645 66517277777687441828425367)
                ·
                  refine ⟨99775916666531162742638051, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66517277777687441828425367 99775916666531162742638051)
                  ·
                    refine ⟨149663874999796744113957077, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99775916666531162742638051 149663874999796744113957077)
                    ·
                      refine ⟨3507747070307736190170869, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149663874999796744113957077 3507747070307736190170869)
                      ·
                        rfl

theorem cell23_6831313_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 1, 2, 2, 1, 3, 1, 1, 7].length) (baseStart_6831313 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831313 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831313 prefixEnd_6831313 := by exact prefixLift 6831313
  have htrace : WordTrace (prefixWord ++ tailWord_6831313) baseStart_6831313 baseEnd_6831313 := by
    simpa [prefixWord, tailWord_6831313, baseEnd_6831313] using wordTrace_append hprefix tailTrace_6831313
  have hstable : (prefixWord ++ tailWord_6831313).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831313).length < 2 ^ (prefixWord ++ tailWord_6831313).sum := by decide
  have hdescent : baseEnd_6831313 < baseStart_6831313 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831313) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831317 : List Nat := [1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 3]
def baseStart_6831317 : Nat := 118140960795 + 6831317 * 2 ^ 59
def prefixEnd_6831317 : Nat := 4983230072969 + 3 ^ 40 * 6831317 * 2
def baseEnd_6831317 : Nat := 3507749124230354174520851

theorem tailTrace_6831317 : CollatzResearch.WordTrace tailWord_6831317 prefixEnd_6831317 3507749124230354174520851 := by
  unfold tailWord_6831317
  simp only [CollatzResearch.WordTrace]
  refine ⟨249158600192312679903292205, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166105733461541786602194803 249158600192312679903292205)
  ·
    refine ⟨93434475072117254963734577, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249158600192312679903292205 93434475072117254963734577)
    ·
      refine ⟨70075856304087941222800933, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93434475072117254963734577 70075856304087941222800933)
      ·
        refine ⟨13139223057016488979275175, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70075856304087941222800933 13139223057016488979275175)
        ·
          refine ⟨19708834585524733468912763, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139223057016488979275175 19708834585524733468912763)
          ·
            refine ⟨29563251878287100203369145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19708834585524733468912763 29563251878287100203369145)
            ·
              refine ⟨22172438908715325152526859, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29563251878287100203369145 22172438908715325152526859)
              ·
                refine ⟨33258658363072987728790289, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22172438908715325152526859 33258658363072987728790289)
                ·
                  refine ⟨24943993772304740796592717, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33258658363072987728790289 24943993772304740796592717)
                  ·
                    refine ⟨9353997664614277798722269, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24943993772304740796592717 9353997664614277798722269)
                    ·
                      refine ⟨3507749124230354174520851, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9353997664614277798722269 3507749124230354174520851)
                      ·
                        rfl

theorem cell23_6831317_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 4, 1, 1, 2, 1, 2, 3, 3].length) (baseStart_6831317 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831317 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831317 prefixEnd_6831317 := by exact prefixLift 6831317
  have htrace : WordTrace (prefixWord ++ tailWord_6831317) baseStart_6831317 baseEnd_6831317 := by
    simpa [prefixWord, tailWord_6831317, baseEnd_6831317] using wordTrace_append hprefix tailTrace_6831317
  have hstable : (prefixWord ++ tailWord_6831317).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831317).length < 2 ^ (prefixWord ++ tailWord_6831317).sum := by decide
  have hdescent : baseEnd_6831317 < baseStart_6831317 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831317) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831318 : List Nat := [5, 2, 1, 2, 2, 2, 1, 1, 1, 4, 2]
def baseStart_6831318 : Nat := 118140960795 + 6831318 * 2 ^ 59
def prefixEnd_6831318 : Nat := 4983230072969 + 3 ^ 40 * 6831318 * 2
def baseEnd_6831318 : Nat := 3507749637711008670608347

theorem tailTrace_6831318 : CollatzResearch.WordTrace tailWord_6831318 prefixEnd_6831318 3507749637711008670608347 := by
  unfold tailWord_6831318
  simp only [CollatzResearch.WordTrace]
  refine ⟨15572414791581816067129913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166105757776872704716052405 15572414791581816067129913)
  ·
    refine ⟨11679311093686362050347435, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15572414791581816067129913 11679311093686362050347435)
    ·
      refine ⟨17518966640529543075521153, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11679311093686362050347435 17518966640529543075521153)
      ·
        refine ⟨13139224980397157306640865, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17518966640529543075521153 13139224980397157306640865)
        ·
          refine ⟨9854418735297867979980649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13139224980397157306640865 9854418735297867979980649)
          ·
            refine ⟨7390814051473400984985487, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9854418735297867979980649 7390814051473400984985487)
            ·
              refine ⟨11086221077210101477478231, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7390814051473400984985487 11086221077210101477478231)
              ·
                refine ⟨16629331615815152216217347, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11086221077210101477478231 16629331615815152216217347)
                ·
                  refine ⟨24943997423722728324326021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16629331615815152216217347 24943997423722728324326021)
                  ·
                    refine ⟨4676999516948011560811129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24943997423722728324326021 4676999516948011560811129)
                    ·
                      refine ⟨3507749637711008670608347, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4676999516948011560811129 3507749637711008670608347)
                      ·
                        rfl

theorem cell23_6831318_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 2, 2, 1, 1, 1, 4, 2].length) (baseStart_6831318 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831318 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831318 prefixEnd_6831318 := by exact prefixLift 6831318
  have htrace : WordTrace (prefixWord ++ tailWord_6831318) baseStart_6831318 baseEnd_6831318 := by
    simpa [prefixWord, tailWord_6831318, baseEnd_6831318] using wordTrace_append hprefix tailTrace_6831318
  have hstable : (prefixWord ++ tailWord_6831318).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831318).length < 2 ^ (prefixWord ++ tailWord_6831318).sum := by decide
  have hdescent : baseEnd_6831318 < baseStart_6831318 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831318) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831340 : List Nat := [2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 4]
def baseStart_6831340 : Nat := 118140960795 + 6831340 * 2 ^ 59
def prefixEnd_6831340 : Nat := 4983230072969 + 3 ^ 40 * 6831340 * 2
def baseEnd_6831340 : Nat := 3507760934285407584533245

theorem tailTrace_6831340 : CollatzResearch.WordTrace tailWord_6831340 prefixEnd_6831340 3507760934285407584533245 := by
  unfold tailWord_6831340
  simp only [CollatzResearch.WordTrace]
  refine ⟨124579719535614677415689737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166106292714152903220919649 124579719535614677415689737)
  ·
    refine ⟨93434789651711008061767303, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124579719535614677415689737 93434789651711008061767303)
    ·
      refine ⟨140152184477566512092650955, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93434789651711008061767303 140152184477566512092650955)
      ·
        refine ⟨210228276716349768138976433, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140152184477566512092650955 210228276716349768138976433)
        ·
          refine ⟨157671207537262326104232325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210228276716349768138976433 157671207537262326104232325)
          ·
            refine ⟨29563351413236686144543561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157671207537262326104232325 29563351413236686144543561)
            ·
              refine ⟨22172513559927514608407671, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29563351413236686144543561 22172513559927514608407671)
              ·
                refine ⟨33258770339891271912611507, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22172513559927514608407671 33258770339891271912611507)
                ·
                  refine ⟨49888155509836907868917261, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33258770339891271912611507 49888155509836907868917261)
                  ·
                    refine ⟨18708058316188840450843973, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49888155509836907868917261 18708058316188840450843973)
                    ·
                      refine ⟨3507760934285407584533245, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18708058316188840450843973 3507760934285407584533245)
                      ·
                        rfl

theorem cell23_6831340_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 3, 4].length) (baseStart_6831340 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831340 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831340 prefixEnd_6831340 := by exact prefixLift 6831340
  have htrace : WordTrace (prefixWord ++ tailWord_6831340) baseStart_6831340 baseEnd_6831340 := by
    simpa [prefixWord, tailWord_6831340, baseEnd_6831340] using wordTrace_append hprefix tailTrace_6831340
  have hstable : (prefixWord ++ tailWord_6831340).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831340).length < 2 ^ (prefixWord ++ tailWord_6831340).sum := by decide
  have hdescent : baseEnd_6831340 < baseStart_6831340 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831340) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831447 : List Nat := [1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 4]
def baseStart_6831447 : Nat := 118140960795 + 6831447 * 2 ^ 59
def prefixEnd_6831447 : Nat := 4983230072969 + 3 ^ 40 * 6831447 * 2
def baseEnd_6831447 : Nat := 3507815876715438665895253

theorem tailTrace_6831447 : CollatzResearch.WordTrace tailWord_6831447 prefixEnd_6831447 3507815876715438665895253 := by
  unfold tailWord_6831447
  simp only [CollatzResearch.WordTrace]
  refine ⟨249163341681841712105524595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166108894454561141403683063 249163341681841712105524595)
  ·
    refine ⟨373745012522762568158286893, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249163341681841712105524595 373745012522762568158286893)
    ·
      refine ⟨140154379696035963059357585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373745012522762568158286893 140154379696035963059357585)
      ·
        refine ⟨105115784772026972294518189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140154379696035963059357585 105115784772026972294518189)
        ·
          refine ⟨39418419289510114610444321, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105115784772026972294518189 39418419289510114610444321)
          ·
            refine ⟨29563814467132585957833241, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39418419289510114610444321 29563814467132585957833241)
            ·
              refine ⟨22172860850349439468374931, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29563814467132585957833241 22172860850349439468374931)
              ·
                refine ⟨33259291275524159202562397, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22172860850349439468374931 33259291275524159202562397)
                ·
                  refine ⟨12472234228321559700960899, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33259291275524159202562397 12472234228321559700960899)
                  ·
                    refine ⟨18708351342482339551441349, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12472234228321559700960899 18708351342482339551441349)
                    ·
                      refine ⟨3507815876715438665895253, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18708351342482339551441349 3507815876715438665895253)
                      ·
                        rfl

theorem cell23_6831447_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 2, 2, 1, 3, 1, 4].length) (baseStart_6831447 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831447 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831447 prefixEnd_6831447 := by exact prefixLift 6831447
  have htrace : WordTrace (prefixWord ++ tailWord_6831447) baseStart_6831447 baseEnd_6831447 := by
    simpa [prefixWord, tailWord_6831447, baseEnd_6831447] using wordTrace_append hprefix tailTrace_6831447
  have hstable : (prefixWord ++ tailWord_6831447).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831447).length < 2 ^ (prefixWord ++ tailWord_6831447).sum := by decide
  have hdescent : baseEnd_6831447 < baseStart_6831447 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831447) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831458 : List Nat := [3, 3, 2, 1, 1, 1, 4, 3, 1, 1, 3]
def baseStart_6831458 : Nat := 118140960795 + 6831458 * 2 ^ 59
def prefixEnd_6831458 : Nat := 4983230072969 + 3 ^ 40 * 6831458 * 2
def baseEnd_6831458 : Nat := 3507821525002638122857703

theorem tailTrace_6831458 : CollatzResearch.WordTrace tailWord_6831458 prefixEnd_6831458 3507821525002638122857703 := by
  unfold tailWord_6831458
  simp only [CollatzResearch.WordTrace]
  refine ⟨62290935721200465246043757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166109161923201240656116685 62290935721200465246043757)
  ·
    refine ⟨23359100895450174467266409, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62290935721200465246043757 23359100895450174467266409)
    ·
      refine ⟨17519325671587630850449807, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23359100895450174467266409 17519325671587630850449807)
      ·
        refine ⟨26278988507381446275674711, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17519325671587630850449807 26278988507381446275674711)
        ·
          refine ⟨39418482761072169413512067, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26278988507381446275674711 39418482761072169413512067)
          ·
            refine ⟨59127724141608254120268101, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39418482761072169413512067 59127724141608254120268101)
            ·
              refine ⟨11086448276551547647550269, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59127724141608254120268101 11086448276551547647550269)
              ·
                refine ⟨4157418103706830367831351, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11086448276551547647550269 4157418103706830367831351)
                ·
                  refine ⟨6236127155560245551747027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157418103706830367831351 6236127155560245551747027)
                  ·
                    refine ⟨9354190733340368327620541, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6236127155560245551747027 9354190733340368327620541)
                    ·
                      refine ⟨3507821525002638122857703, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354190733340368327620541 3507821525002638122857703)
                      ·
                        rfl

theorem cell23_6831458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 2, 1, 1, 1, 4, 3, 1, 1, 3].length) (baseStart_6831458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831458 prefixEnd_6831458 := by exact prefixLift 6831458
  have htrace : WordTrace (prefixWord ++ tailWord_6831458) baseStart_6831458 baseEnd_6831458 := by
    simpa [prefixWord, tailWord_6831458, baseEnd_6831458] using wordTrace_append hprefix tailTrace_6831458
  have hstable : (prefixWord ++ tailWord_6831458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831458).length < 2 ^ (prefixWord ++ tailWord_6831458).sum := by decide
  have hdescent : baseEnd_6831458 < baseStart_6831458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831491 : List Nat := [1, 1, 1, 3, 5, 2, 3, 1, 2, 4]
def baseStart_6831491 : Nat := 118140960795 + 6831491 * 2 ^ 59
def prefixEnd_6831491 : Nat := 4983230072969 + 3 ^ 40 * 6831491 * 2
def baseEnd_6831491 : Nat := 1169279489954745497915017

theorem tailTrace_6831491 : CollatzResearch.WordTrace tailWord_6831491 prefixEnd_6831491 1169279489954745497915017 := by
  unfold tailWord_6831491
  simp only [CollatzResearch.WordTrace]
  refine ⟨249164946493682307620126327, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166109964329121538413417551 249164946493682307620126327)
  ·
    refine ⟨373747419740523461430189491, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249164946493682307620126327 373747419740523461430189491)
    ·
      refine ⟨560621129610785192145284237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373747419740523461430189491 560621129610785192145284237)
      ·
        refine ⟨210232923604044447054481589, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560621129610785192145284237 210232923604044447054481589)
        ·
          refine ⟨19709336587879166911357649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210232923604044447054481589 19709336587879166911357649)
          ·
            refine ⟨14782002440909375183518237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19709336587879166911357649 14782002440909375183518237)
            ·
              refine ⟨5543250915341015693819339, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14782002440909375183518237 5543250915341015693819339)
              ·
                refine ⟨8314876373011523540729009, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5543250915341015693819339 8314876373011523540729009)
                ·
                  refine ⟨6236157279758642655546757, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8314876373011523540729009 6236157279758642655546757)
                  ·
                    refine ⟨1169279489954745497915017, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6236157279758642655546757 1169279489954745497915017)
                    ·
                      rfl

theorem cell23_6831491_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 5, 2, 3, 1, 2, 4].length) (baseStart_6831491 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831491 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831491 prefixEnd_6831491 := by exact prefixLift 6831491
  have htrace : WordTrace (prefixWord ++ tailWord_6831491) baseStart_6831491 baseEnd_6831491 := by
    simpa [prefixWord, tailWord_6831491, baseEnd_6831491] using wordTrace_append hprefix tailTrace_6831491
  have hstable : (prefixWord ++ tailWord_6831491).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831491).length < 2 ^ (prefixWord ++ tailWord_6831491).sum := by decide
  have hdescent : baseEnd_6831491 < baseStart_6831491 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831491) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831507 : List Nat := [1, 1, 1, 2, 1, 2, 1, 1, 4, 7, 2]
def baseStart_6831507 : Nat := 118140960795 + 6831507 * 2 ^ 59
def prefixEnd_6831507 : Nat := 4983230072969 + 3 ^ 40 * 6831507 * 2
def baseEnd_6831507 : Nat := 3507846685554708431144977

theorem tailTrace_6831507 : CollatzResearch.WordTrace tailWord_6831507 prefixEnd_6831507 3507846685554708431144977 := by
  unfold tailWord_6831507
  simp only [CollatzResearch.WordTrace]
  refine ⟨249165530061624342352708775, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166110353374416228235139183 249165530061624342352708775)
  ·
    refine ⟨373748295092436513529063163, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249165530061624342352708775 373748295092436513529063163)
    ·
      refine ⟨560622442638654770293594745, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373748295092436513529063163 560622442638654770293594745)
      ·
        refine ⟨420466831978991077720196059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560622442638654770293594745 420466831978991077720196059)
        ·
          refine ⟨630700247968486616580294089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420466831978991077720196059 630700247968486616580294089)
          ·
            refine ⟨473025185976364962435220567, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630700247968486616580294089 473025185976364962435220567)
            ·
              refine ⟨709537778964547443652830851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473025185976364962435220567 709537778964547443652830851)
              ·
                refine ⟨1064306668446821165479246277, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709537778964547443652830851 1064306668446821165479246277)
                ·
                  refine ⟨199557500333778968527358677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 1064306668446821165479246277 199557500333778968527358677)
                  ·
                    refine ⟨4677128914072944574859969, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 199557500333778968527358677 4677128914072944574859969)
                    ·
                      refine ⟨3507846685554708431144977, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677128914072944574859969 3507846685554708431144977)
                      ·
                        rfl

theorem cell23_6831507_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 1, 1, 4, 7, 2].length) (baseStart_6831507 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831507 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831507 prefixEnd_6831507 := by exact prefixLift 6831507
  have htrace : WordTrace (prefixWord ++ tailWord_6831507) baseStart_6831507 baseEnd_6831507 := by
    simpa [prefixWord, tailWord_6831507, baseEnd_6831507] using wordTrace_append hprefix tailTrace_6831507
  have hstable : (prefixWord ++ tailWord_6831507).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831507).length < 2 ^ (prefixWord ++ tailWord_6831507).sum := by decide
  have hdescent : baseEnd_6831507 < baseStart_6831507 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831507) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831514 : List Nat := [3, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3]
def baseStart_6831514 : Nat := 118140960795 + 6831514 * 2 ^ 59
def prefixEnd_6831514 : Nat := 4983230072969 + 3 ^ 40 * 6831514 * 2
def baseEnd_6831514 : Nat := 3507850279919289903757445

theorem tailTrace_6831514 : CollatzResearch.WordTrace tailWord_6831514 prefixEnd_6831514 3507850279919289903757445 := by
  unfold tailWord_6831514
  simp only [CollatzResearch.WordTrace]
  refine ⟨62291446343149745637053399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166110523581732655032142397 62291446343149745637053399)
  ·
    refine ⟨93437169514724618455580099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62291446343149745637053399 93437169514724618455580099)
    ·
      refine ⟨140155754272086927683370149, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93437169514724618455580099 140155754272086927683370149)
      ·
        refine ⟨26279203926016298940631903, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140155754272086927683370149 26279203926016298940631903)
        ·
          refine ⟨39418805889024448410947855, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26279203926016298940631903 39418805889024448410947855)
          ·
            refine ⟨59128208833536672616421783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39418805889024448410947855 59128208833536672616421783)
            ·
              refine ⟨88692313250305008924632675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59128208833536672616421783 88692313250305008924632675)
              ·
                refine ⟨133038469875457513386949013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88692313250305008924632675 133038469875457513386949013)
                ·
                  refine ⟨6236178275412070940013235, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 133038469875457513386949013 6236178275412070940013235)
                  ·
                    refine ⟨9354267413118106410019853, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6236178275412070940013235 9354267413118106410019853)
                    ·
                      refine ⟨3507850279919289903757445, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354267413118106410019853 3507850279919289903757445)
                      ·
                        rfl

theorem cell23_6831514_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 4, 1, 1, 1, 1, 6, 1, 3].length) (baseStart_6831514 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831514 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831514 prefixEnd_6831514 := by exact prefixLift 6831514
  have htrace : WordTrace (prefixWord ++ tailWord_6831514) baseStart_6831514 baseEnd_6831514 := by
    simpa [prefixWord, tailWord_6831514, baseEnd_6831514] using wordTrace_append hprefix tailTrace_6831514
  have hstable : (prefixWord ++ tailWord_6831514).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831514).length < 2 ^ (prefixWord ++ tailWord_6831514).sum := by decide
  have hdescent : baseEnd_6831514 < baseStart_6831514 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831514) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831524 : List Nat := [2, 3, 1, 2, 1, 1, 1, 2, 5, 3, 2]
def baseStart_6831524 : Nat := 118140960795 + 6831524 * 2 ^ 59
def prefixEnd_6831524 : Nat := 4983230072969 + 3 ^ 40 * 6831524 * 2
def baseEnd_6831524 : Nat := 3507855414725834864632399

theorem tailTrace_6831524 : CollatzResearch.WordTrace tailWord_6831524 prefixEnd_6831524 3507855414725834864632399 := by
  unfold tailWord_6831524
  simp only [CollatzResearch.WordTrace]
  refine ⟨124583075051281377128038813, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166110766735041836170718417 124583075051281377128038813)
  ·
    refine ⟨46718653144230516423014555, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124583075051281377128038813 46718653144230516423014555)
    ·
      refine ⟨70077979716345774634521833, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46718653144230516423014555 70077979716345774634521833)
      ·
        refine ⟨52558484787259330975891375, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70077979716345774634521833 52558484787259330975891375)
        ·
          refine ⟨78837727180888996463837063, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52558484787259330975891375 78837727180888996463837063)
          ·
            refine ⟨118256590771333494695755595, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78837727180888996463837063 118256590771333494695755595)
            ·
              refine ⟨177384886157000242043633393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118256590771333494695755595 177384886157000242043633393)
              ·
                refine ⟨133038664617750181532725045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177384886157000242043633393 133038664617750181532725045)
                ·
                  refine ⟨12472374807914079518692973, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 133038664617750181532725045 12472374807914079518692973)
                  ·
                    refine ⟨4677140552967779819509865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12472374807914079518692973 4677140552967779819509865)
                    ·
                      refine ⟨3507855414725834864632399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677140552967779819509865 3507855414725834864632399)
                      ·
                        rfl

theorem cell23_6831524_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 1, 1, 1, 2, 5, 3, 2].length) (baseStart_6831524 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831524 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831524 prefixEnd_6831524 := by exact prefixLift 6831524
  have htrace : WordTrace (prefixWord ++ tailWord_6831524) baseStart_6831524 baseEnd_6831524 := by
    simpa [prefixWord, tailWord_6831524, baseEnd_6831524] using wordTrace_append hprefix tailTrace_6831524
  have hstable : (prefixWord ++ tailWord_6831524).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831524).length < 2 ^ (prefixWord ++ tailWord_6831524).sum := by decide
  have hdescent : baseEnd_6831524 < baseStart_6831524 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831524) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831527 : List Nat := [1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 5]
def baseStart_6831527 : Nat := 118140960795 + 6831527 * 2 ^ 59
def prefixEnd_6831527 : Nat := 4983230072969 + 3 ^ 40 * 6831527 * 2
def baseEnd_6831527 : Nat := 3507856955167798352894885

theorem tailTrace_6831527 : CollatzResearch.WordTrace tailWord_6831527 prefixEnd_6831527 3507856955167798352894885 := by
  unfold tailWord_6831527
  simp only [CollatzResearch.WordTrace]
  refine ⟨249166259521551885768436835, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166110839681034590512291223 249166259521551885768436835)
  ·
    refine ⟨373749389282327828652655253, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249166259521551885768436835 373749389282327828652655253)
    ·
      refine ⟨17519502622609116968093215, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 373749389282327828652655253 17519502622609116968093215)
      ·
        refine ⟨26279253933913675452139823, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17519502622609116968093215 26279253933913675452139823)
        ·
          refine ⟨39418880900870513178209735, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26279253933913675452139823 39418880900870513178209735)
          ·
            refine ⟨59128321351305769767314603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39418880900870513178209735 59128321351305769767314603)
            ·
              refine ⟨88692482026958654650971905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59128321351305769767314603 88692482026958654650971905)
              ·
                refine ⟨66519361520218990988228929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88692482026958654650971905 66519361520218990988228929)
                ·
                  refine ⟨49889521140164243241171697, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66519361520218990988228929 49889521140164243241171697)
                  ·
                    refine ⟨37417140855123182430878773, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49889521140164243241171697 37417140855123182430878773)
                    ·
                      refine ⟨3507856955167798352894885, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37417140855123182430878773 3507856955167798352894885)
                      ·
                        rfl

theorem cell23_6831527_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 6, 1, 1, 1, 1, 2, 2, 2, 5].length) (baseStart_6831527 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831527 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831527 prefixEnd_6831527 := by exact prefixLift 6831527
  have htrace : WordTrace (prefixWord ++ tailWord_6831527) baseStart_6831527 baseEnd_6831527 := by
    simpa [prefixWord, tailWord_6831527, baseEnd_6831527] using wordTrace_append hprefix tailTrace_6831527
  have hstable : (prefixWord ++ tailWord_6831527).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831527).length < 2 ^ (prefixWord ++ tailWord_6831527).sum := by decide
  have hdescent : baseEnd_6831527 < baseStart_6831527 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831527) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831537 : List Nat := [1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6831537 : Nat := 118140960795 + 6831537 * 2 ^ 59
def prefixEnd_6831537 : Nat := 4983230072969 + 3 ^ 40 * 6831537 * 2
def baseEnd_6831537 : Nat := 3507862089974343313769839

theorem tailTrace_6831537 : CollatzResearch.WordTrace tailWord_6831537 prefixEnd_6831537 3507862089974343313769839 := by
  unfold tailWord_6831537
  simp only [CollatzResearch.WordTrace]
  refine ⟨249166624251515657476300865, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166111082834343771650867243 249166624251515657476300865)
  ·
    refine ⟨186874968188636743107225649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249166624251515657476300865 186874968188636743107225649)
    ·
      refine ⟨140156226141477557330419237, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186874968188636743107225649 140156226141477557330419237)
      ·
        refine ⟨26279292401527041999453607, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140156226141477557330419237 26279292401527041999453607)
        ·
          refine ⟨39418938602290562999180411, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26279292401527041999453607 39418938602290562999180411)
          ·
            refine ⟨59128407903435844498770617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39418938602290562999180411 59128407903435844498770617)
            ·
              refine ⟨44346305927576883374077963, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59128407903435844498770617 44346305927576883374077963)
              ·
                refine ⟨66519458891365325061116945, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44346305927576883374077963 66519458891365325061116945)
                ·
                  refine ⟨49889594168523993795837709, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66519458891365325061116945 49889594168523993795837709)
                  ·
                    refine ⟨18708597813196497673439141, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49889594168523993795837709 18708597813196497673439141)
                    ·
                      refine ⟨3507862089974343313769839, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18708597813196497673439141 3507862089974343313769839)
                      ·
                        rfl

theorem cell23_6831537_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 4, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6831537 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831537 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831537 prefixEnd_6831537 := by exact prefixLift 6831537
  have htrace : WordTrace (prefixWord ++ tailWord_6831537) baseStart_6831537 baseEnd_6831537 := by
    simpa [prefixWord, tailWord_6831537, baseEnd_6831537] using wordTrace_append hprefix tailTrace_6831537
  have hstable : (prefixWord ++ tailWord_6831537).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831537).length < 2 ^ (prefixWord ++ tailWord_6831537).sum := by decide
  have hdescent : baseEnd_6831537 < baseStart_6831537 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831537) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831548 : List Nat := [2, 2, 2, 4, 2, 1, 1, 3, 2, 1, 3]
def baseStart_6831548 : Nat := 118140960795 + 6831548 * 2 ^ 59
def prefixEnd_6831548 : Nat := 4983230072969 + 3 ^ 40 * 6831548 * 2
def baseEnd_6831548 : Nat := 3507867738261542770732289

theorem tailTrace_6831548 : CollatzResearch.WordTrace tailWord_6831548 prefixEnd_6831548 3507867738261542770732289 := by
  unfold tailWord_6831548
  simp only [CollatzResearch.WordTrace]
  refine ⟨124583512727237903177475649, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166111350302983870903300865 124583512727237903177475649)
  ·
    refine ⟨93437634545428427383106737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124583512727237903177475649 93437634545428427383106737)
    ·
      refine ⟨70078225909071320537330053, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93437634545428427383106737 70078225909071320537330053)
      ·
        refine ⟨13139667357950872600749385, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 70078225909071320537330053 13139667357950872600749385)
        ·
          refine ⟨9854750518463154450562039, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13139667357950872600749385 9854750518463154450562039)
          ·
            refine ⟨14782125777694731675843059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9854750518463154450562039 14782125777694731675843059)
            ·
              refine ⟨22173188666542097513764589, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14782125777694731675843059 22173188666542097513764589)
              ·
                refine ⟨8314945749953286567661721, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22173188666542097513764589 8314945749953286567661721)
                ·
                  refine ⟨6236209312464964925746291, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8314945749953286567661721 6236209312464964925746291)
                  ·
                    refine ⟨9354313968697447388619437, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6236209312464964925746291 9354313968697447388619437)
                    ·
                      refine ⟨3507867738261542770732289, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354313968697447388619437 3507867738261542770732289)
                      ·
                        rfl

theorem cell23_6831548_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 4, 2, 1, 1, 3, 2, 1, 3].length) (baseStart_6831548 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831548 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831548 prefixEnd_6831548 := by exact prefixLift 6831548
  have htrace : WordTrace (prefixWord ++ tailWord_6831548) baseStart_6831548 baseEnd_6831548 := by
    simpa [prefixWord, tailWord_6831548, baseEnd_6831548] using wordTrace_append hprefix tailTrace_6831548
  have hstable : (prefixWord ++ tailWord_6831548).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831548).length < 2 ^ (prefixWord ++ tailWord_6831548).sum := by decide
  have hdescent : baseEnd_6831548 < baseStart_6831548 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831548) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831605 : List Nat := [1, 3, 5, 1, 1, 1, 2, 3, 2, 2, 2]
def baseStart_6831605 : Nat := 118140960795 + 6831605 * 2 ^ 59
def prefixEnd_6831605 : Nat := 4983230072969 + 3 ^ 40 * 6831605 * 2
def baseEnd_6831605 : Nat := 3507897006658849047719527

theorem tailTrace_6831605 : CollatzResearch.WordTrace tailWord_6831605 prefixEnd_6831605 3507897006658849047719527 := by
  unfold tailWord_6831605
  simp only [CollatzResearch.WordTrace]
  refine ⟨249169104415269305089776269, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166112736276846203393184179 249169104415269305089776269)
  ·
    refine ⟨93438414155725989408666101, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249169104415269305089776269 93438414155725989408666101)
    ·
      refine ⟨8759851327099311507062447, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93438414155725989408666101 8759851327099311507062447)
      ·
        refine ⟨13139776990648967260593671, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8759851327099311507062447 13139776990648967260593671)
        ·
          refine ⟨19709665485973450890890507, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13139776990648967260593671 19709665485973450890890507)
          ·
            refine ⟨29564498228960176336335761, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19709665485973450890890507 29564498228960176336335761)
            ·
              refine ⟨22173373671720132252251821, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29564498228960176336335761 22173373671720132252251821)
              ·
                refine ⟨8315015126895049594594433, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22173373671720132252251821 8315015126895049594594433)
                ·
                  refine ⟨6236261345171287195945825, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8315015126895049594594433 6236261345171287195945825)
                  ·
                    refine ⟨4677196008878465396959369, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6236261345171287195945825 4677196008878465396959369)
                    ·
                      refine ⟨3507897006658849047719527, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677196008878465396959369 3507897006658849047719527)
                      ·
                        rfl

theorem cell23_6831605_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 5, 1, 1, 1, 2, 3, 2, 2, 2].length) (baseStart_6831605 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831605 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831605 prefixEnd_6831605 := by exact prefixLift 6831605
  have htrace : WordTrace (prefixWord ++ tailWord_6831605) baseStart_6831605 baseEnd_6831605 := by
    simpa [prefixWord, tailWord_6831605, baseEnd_6831605] using wordTrace_append hprefix tailTrace_6831605
  have hstable : (prefixWord ++ tailWord_6831605).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831605).length < 2 ^ (prefixWord ++ tailWord_6831605).sum := by decide
  have hdescent : baseEnd_6831605 < baseStart_6831605 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831605) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831624 : List Nat := [2, 1, 3, 2, 1, 1, 5, 1, 2, 5]
def baseStart_6831624 : Nat := 118140960795 + 6831624 * 2 ^ 59
def prefixEnd_6831624 : Nat := 4983230072969 + 3 ^ 40 * 6831624 * 2
def baseEnd_6831624 : Nat := 1169302254263761491127313

theorem tailTrace_6831624 : CollatzResearch.WordTrace tailWord_6831624 prefixEnd_6831624 1169302254263761491127313 := by
  unfold tailWord_6831624
  simp only [CollatzResearch.WordTrace]
  refine ⟨124584898701100235667358963, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166113198268133647556478617 124584898701100235667358963)
  ·
    refine ⟨186877348051650353501038445, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124584898701100235667358963 186877348051650353501038445)
    ·
      refine ⟨70079005519368882562889417, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186877348051650353501038445 70079005519368882562889417)
      ·
        refine ⟨52559254139526661922167063, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70079005519368882562889417 52559254139526661922167063)
        ·
          refine ⟨78838881209289992883250595, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52559254139526661922167063 78838881209289992883250595)
          ·
            refine ⟨118258321813934989324875893, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78838881209289992883250595 118258321813934989324875893)
            ·
              refine ⟨11086717670056405249207115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118258321813934989324875893 11086717670056405249207115)
              ·
                refine ⟨16630076505084607873810673, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11086717670056405249207115 16630076505084607873810673)
                ·
                  refine ⟨12472557378813455905358005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16630076505084607873810673 12472557378813455905358005)
                  ·
                    refine ⟨1169302254263761491127313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12472557378813455905358005 1169302254263761491127313)
                    ·
                      rfl

theorem cell23_6831624_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 2, 1, 1, 5, 1, 2, 5].length) (baseStart_6831624 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831624 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831624 prefixEnd_6831624 := by exact prefixLift 6831624
  have htrace : WordTrace (prefixWord ++ tailWord_6831624) baseStart_6831624 baseEnd_6831624 := by
    simpa [prefixWord, tailWord_6831624, baseEnd_6831624] using wordTrace_append hprefix tailTrace_6831624
  have hstable : (prefixWord ++ tailWord_6831624).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831624).length < 2 ^ (prefixWord ++ tailWord_6831624).sum := by decide
  have hdescent : baseEnd_6831624 < baseStart_6831624 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831624) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831644 : List Nat := [2, 2, 3, 1, 2, 1, 2, 1, 4, 1, 4]
def baseStart_6831644 : Nat := 118140960795 + 6831644 * 2 ^ 59
def prefixEnd_6831644 : Nat := 4983230072969 + 3 ^ 40 * 6831644 * 2
def baseEnd_6831644 : Nat := 3507917032404374395131847

theorem tailTrace_6831644 : CollatzResearch.WordTrace tailWord_6831644 prefixEnd_6831644 3507917032404374395131847 := by
  unfold tailWord_6831644
  simp only [CollatzResearch.WordTrace]
  refine ⟨124585263431064007375222993, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166113684574752009833630657 124585263431064007375222993)
  ·
    refine ⟨93438947573298005531417245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124585263431064007375222993 93438947573298005531417245)
    ·
      refine ⟨35039605339986752074281467, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93438947573298005531417245 35039605339986752074281467)
      ·
        refine ⟨52559408009980128111422201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35039605339986752074281467 52559408009980128111422201)
        ·
          refine ⟨39419556007485096083566651, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52559408009980128111422201 39419556007485096083566651)
          ·
            refine ⟨59129334011227644125349977, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39419556007485096083566651 59129334011227644125349977)
            ·
              refine ⟨44347000508420733094012483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59129334011227644125349977 44347000508420733094012483)
              ·
                refine ⟨66520500762631099641018725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44347000508420733094012483 66520500762631099641018725)
                ·
                  refine ⟨12472593892993331182691011, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66520500762631099641018725 12472593892993331182691011)
                  ·
                    refine ⟨18708890839489996774036517, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12472593892993331182691011 18708890839489996774036517)
                    ·
                      refine ⟨3507917032404374395131847, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18708890839489996774036517 3507917032404374395131847)
                      ·
                        rfl

theorem cell23_6831644_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 2, 1, 2, 1, 4, 1, 4].length) (baseStart_6831644 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831644 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831644 prefixEnd_6831644 := by exact prefixLift 6831644
  have htrace : WordTrace (prefixWord ++ tailWord_6831644) baseStart_6831644 baseEnd_6831644 := by
    simpa [prefixWord, tailWord_6831644, baseEnd_6831644] using wordTrace_append hprefix tailTrace_6831644
  have hstable : (prefixWord ++ tailWord_6831644).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831644).length < 2 ^ (prefixWord ++ tailWord_6831644).sum := by decide
  have hdescent : baseEnd_6831644 < baseStart_6831644 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831644) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831647 : List Nat := [1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 5]
def baseStart_6831647 : Nat := 118140960795 + 6831647 * 2 ^ 59
def prefixEnd_6831647 : Nat := 4983230072969 + 3 ^ 40 * 6831647 * 2
def baseEnd_6831647 : Nat := 3507918572846337883394333

theorem tailTrace_6831647 : CollatzResearch.WordTrace tailWord_6831647 prefixEnd_6831647 3507918572846337883394333 := by
  unfold tailWord_6831647
  simp only [CollatzResearch.WordTrace]
  refine ⟨249170636281117146262805195, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166113757520744764175203463 249170636281117146262805195)
  ·
    refine ⟨373755954421675719394207793, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249170636281117146262805195 373755954421675719394207793)
    ·
      refine ⟨280316965816256789545655845, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373755954421675719394207793 280316965816256789545655845)
      ·
        refine ⟨52559431090548148039810471, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280316965816256789545655845 52559431090548148039810471)
        ·
          refine ⟨78839146635822222059715707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52559431090548148039810471 78839146635822222059715707)
          ·
            refine ⟨118258719953733333089573561, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78839146635822222059715707 118258719953733333089573561)
            ·
              refine ⟨88694039965299999817180171, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118258719953733333089573561 88694039965299999817180171)
              ·
                refine ⟨133041059947949999725770257, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88694039965299999817180171 133041059947949999725770257)
                ·
                  refine ⟨99780794960962499794327693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133041059947949999725770257 99780794960962499794327693)
                  ·
                    refine ⟨37417798110360937422872885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99780794960962499794327693 37417798110360937422872885)
                    ·
                      refine ⟨3507918572846337883394333, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37417798110360937422872885 3507918572846337883394333)
                      ·
                        rfl

theorem cell23_6831647_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 1, 1, 2, 1, 2, 3, 5].length) (baseStart_6831647 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831647 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831647 prefixEnd_6831647 := by exact prefixLift 6831647
  have htrace : WordTrace (prefixWord ++ tailWord_6831647) baseStart_6831647 baseEnd_6831647 := by
    simpa [prefixWord, tailWord_6831647, baseEnd_6831647] using wordTrace_append hprefix tailTrace_6831647
  have hstable : (prefixWord ++ tailWord_6831647).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831647).length < 2 ^ (prefixWord ++ tailWord_6831647).sum := by decide
  have hdescent : baseEnd_6831647 < baseStart_6831647 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831647) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831681 : List Nat := [1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 3]
def baseStart_6831681 : Nat := 118140960795 + 6831681 * 2 ^ 59
def prefixEnd_6831681 : Nat := 4983230072969 + 3 ^ 40 * 6831681 * 2
def baseEnd_6831681 : Nat := 3507936031188590750369177

theorem tailTrace_6831681 : CollatzResearch.WordTrace tailWord_6831681 prefixEnd_6831681 3507936031188590750369177 := by
  unfold tailWord_6831681
  simp only [CollatzResearch.WordTrace]
  refine ⟨249171876362993970069542897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166114584241995980046361931 249171876362993970069542897)
  ·
    refine ⟨186878907272245477552157173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249171876362993970069542897 186878907272245477552157173)
    ·
      refine ⟨17519897556773013520514735, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186878907272245477552157173 17519897556773013520514735)
      ·
        refine ⟨26279846335159520280772103, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17519897556773013520514735 26279846335159520280772103)
        ·
          refine ⟨39419769502739280421158155, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26279846335159520280772103 39419769502739280421158155)
          ·
            refine ⟨59129654254108920631737233, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39419769502739280421158155 59129654254108920631737233)
            ·
              refine ⟨44347240690581690473802925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59129654254108920631737233 44347240690581690473802925)
              ·
                refine ⟨16630215258968133927676097, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44347240690581690473802925 16630215258968133927676097)
                ·
                  refine ⟨12472661444226100445757073, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16630215258968133927676097 12472661444226100445757073)
                  ·
                    refine ⟨9354496083169575334317805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12472661444226100445757073 9354496083169575334317805)
                    ·
                      refine ⟨3507936031188590750369177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354496083169575334317805 3507936031188590750369177)
                      ·
                        rfl

theorem cell23_6831681_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 1, 2, 3, 2, 2, 3].length) (baseStart_6831681 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831681 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831681 prefixEnd_6831681 := by exact prefixLift 6831681
  have htrace : WordTrace (prefixWord ++ tailWord_6831681) baseStart_6831681 baseEnd_6831681 := by
    simpa [prefixWord, tailWord_6831681, baseEnd_6831681] using wordTrace_append hprefix tailTrace_6831681
  have hstable : (prefixWord ++ tailWord_6831681).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831681).length < 2 ^ (prefixWord ++ tailWord_6831681).sum := by decide
  have hdescent : baseEnd_6831681 < baseStart_6831681 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831681) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831744 : List Nat := [2, 1, 1, 2, 1, 4, 3, 2, 1, 6]
def baseStart_6831744 : Nat := 118140960795 + 6831744 * 2 ^ 59
def prefixEnd_6831744 : Nat := 4983230072969 + 3 ^ 40 * 6831744 * 2
def baseEnd_6831744 : Nat := 1169322793489941334627129

theorem tailTrace_6831744 : CollatzResearch.WordTrace tailWord_6831744 prefixEnd_6831744 1169322793489941334627129 := by
  unfold tailWord_6831744
  simp only [CollatzResearch.WordTrace]
  refine ⟨124587087080882865914543143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166116116107843821219390857 124587087080882865914543143)
  ·
    refine ⟨186880630621324298871814715, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124587087080882865914543143 186880630621324298871814715)
    ·
      refine ⟨280320945931986448307722073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186880630621324298871814715 280320945931986448307722073)
      ·
        refine ⟨210240709448989836230791555, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280320945931986448307722073 210240709448989836230791555)
        ·
          refine ⟨315361064173484754346187333, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210240709448989836230791555 315361064173484754346187333)
          ·
            refine ⟨59130199532528391439910125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315361064173484754346187333 59130199532528391439910125)
            ·
              refine ⟨22173824824698146789966297, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59130199532528391439910125 22173824824698146789966297)
              ·
                refine ⟨16630368618523610092474723, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22173824824698146789966297 16630368618523610092474723)
                ·
                  refine ⟨24945552927785415138712085, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16630368618523610092474723 24945552927785415138712085)
                  ·
                    refine ⟨1169322793489941334627129, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24945552927785415138712085 1169322793489941334627129)
                    ·
                      rfl

theorem cell23_6831744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 4, 3, 2, 1, 6].length) (baseStart_6831744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831744 prefixEnd_6831744 := by exact prefixLift 6831744
  have htrace : WordTrace (prefixWord ++ tailWord_6831744) baseStart_6831744 baseEnd_6831744 := by
    simpa [prefixWord, tailWord_6831744, baseEnd_6831744] using wordTrace_append hprefix tailTrace_6831744
  have hstable : (prefixWord ++ tailWord_6831744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831744).length < 2 ^ (prefixWord ++ tailWord_6831744).sum := by decide
  have hdescent : baseEnd_6831744 < baseStart_6831744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831757 : List Nat := [1, 22]
def baseStart_6831757 : Nat := 118140960795 + 6831757 * 2 ^ 59
def prefixEnd_6831757 : Nat := 4983230072969 + 3 ^ 40 * 6831757 * 2
def baseEnd_6831757 : Nat := 178223596795119262969

theorem tailTrace_6831757 : CollatzResearch.WordTrace tailWord_6831757 prefixEnd_6831757 178223596795119262969 := by
  unfold tailWord_6831757
  simp only [CollatzResearch.WordTrace]
  refine ⟨249174648310718635049309525, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166116432207145756699539683 249174648310718635049309525)
  ·
    refine ⟨178223596795119262969, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 22 249174648310718635049309525 178223596795119262969)
    ·
      rfl

theorem cell23_6831757_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 22].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 22].length) (baseStart_6831757 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831757 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831757 prefixEnd_6831757 := by exact prefixLift 6831757
  have htrace : WordTrace (prefixWord ++ tailWord_6831757) baseStart_6831757 baseEnd_6831757 := by
    simpa [prefixWord, tailWord_6831757, baseEnd_6831757] using wordTrace_append hprefix tailTrace_6831757
  have hstable : (prefixWord ++ tailWord_6831757).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831757).length < 2 ^ (prefixWord ++ tailWord_6831757).sum := by decide
  have hdescent : baseEnd_6831757 < baseStart_6831757 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831757) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831762 : List Nat := [3, 2, 3, 1, 3, 1, 1, 4, 1, 1, 3]
def baseStart_6831762 : Nat := 118140960795 + 6831762 * 2 ^ 59
def prefixEnd_6831762 : Nat := 4983230072969 + 3 ^ 40 * 6831762 * 2
def baseEnd_6831762 : Nat := 3507977623121604933456305

theorem tailTrace_6831762 : CollatzResearch.WordTrace tailWord_6831762 prefixEnd_6831762 3507977623121604933456305 := by
  unfold tailWord_6831762
  simp only [CollatzResearch.WordTrace]
  refine ⟨62293707668925130225810385, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166116553783800347268827693 62293707668925130225810385)
  ·
    refine ⟨46720280751693847669357789, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62293707668925130225810385 46720280751693847669357789)
    ·
      refine ⟨17520105281885192876009171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46720280751693847669357789 17520105281885192876009171)
      ·
        refine ⟨26280157922827789314013757, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17520105281885192876009171 26280157922827789314013757)
        ·
          refine ⟨9855059221060420992755159, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26280157922827789314013757 9855059221060420992755159)
          ·
            refine ⟨14782588831590631489132739, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855059221060420992755159 14782588831590631489132739)
            ·
              refine ⟨22173883247385947233699109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14782588831590631489132739 22173883247385947233699109)
              ·
                refine ⟨4157603108884865106318583, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22173883247385947233699109 4157603108884865106318583)
                ·
                  refine ⟨6236404663327297659477875, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157603108884865106318583 6236404663327297659477875)
                  ·
                    refine ⟨9354606994990946489216813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6236404663327297659477875 9354606994990946489216813)
                    ·
                      refine ⟨3507977623121604933456305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354606994990946489216813 3507977623121604933456305)
                      ·
                        rfl

theorem cell23_6831762_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 1, 3, 1, 1, 4, 1, 1, 3].length) (baseStart_6831762 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831762 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831762 prefixEnd_6831762 := by exact prefixLift 6831762
  have htrace : WordTrace (prefixWord ++ tailWord_6831762) baseStart_6831762 baseEnd_6831762 := by
    simpa [prefixWord, tailWord_6831762, baseEnd_6831762] using wordTrace_append hprefix tailTrace_6831762
  have hstable : (prefixWord ++ tailWord_6831762).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831762).length < 2 ^ (prefixWord ++ tailWord_6831762).sum := by decide
  have hdescent : baseEnd_6831762 < baseStart_6831762 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831762) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831801 : List Nat := [1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 3]
def baseStart_6831801 : Nat := 118140960795 + 6831801 * 2 ^ 59
def prefixEnd_6831801 : Nat := 4983230072969 + 3 ^ 40 * 6831801 * 2
def baseEnd_6831801 : Nat := 3507997648867130280868625

theorem tailTrace_6831801 : CollatzResearch.WordTrace tailWord_6831801 prefixEnd_6831801 3507997648867130280868625 := by
  unfold tailWord_6831801
  simp only [CollatzResearch.WordTrace]
  refine ⟨249176253122559230563911257, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166117502081706153709274171 249176253122559230563911257)
  ·
    refine ⟨186882189841919422922933443, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249176253122559230563911257 186882189841919422922933443)
    ·
      refine ⟨280323284762879134384400165, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186882189841919422922933443 280323284762879134384400165)
      ·
        refine ⟨52560615893039837697075031, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280323284762879134384400165 52560615893039837697075031)
        ·
          refine ⟨78840923839559756545612547, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52560615893039837697075031 78840923839559756545612547)
          ·
            refine ⟨118261385759339634818418821, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78840923839559756545612547 118261385759339634818418821)
            ·
              refine ⟨22174009829876181528453529, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118261385759339634818418821 22174009829876181528453529)
              ·
                refine ⟨16630507372407136146340147, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22174009829876181528453529 16630507372407136146340147)
                ·
                  refine ⟨24945761058610704219510221, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16630507372407136146340147 24945761058610704219510221)
                  ·
                    refine ⟨9354660396979014082316333, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24945761058610704219510221 9354660396979014082316333)
                    ·
                      refine ⟨3507997648867130280868625, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354660396979014082316333 3507997648867130280868625)
                      ·
                        rfl

theorem cell23_6831801_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 4, 1, 1, 4, 2, 1, 3, 3].length) (baseStart_6831801 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831801 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831801 prefixEnd_6831801 := by exact prefixLift 6831801
  have htrace : WordTrace (prefixWord ++ tailWord_6831801) baseStart_6831801 baseEnd_6831801 := by
    simpa [prefixWord, tailWord_6831801, baseEnd_6831801] using wordTrace_append hprefix tailTrace_6831801
  have hstable : (prefixWord ++ tailWord_6831801).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831801).length < 2 ^ (prefixWord ++ tailWord_6831801).sum := by decide
  have hdescent : baseEnd_6831801 < baseStart_6831801 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831801) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831802 : List Nat := [3, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2]
def baseStart_6831802 : Nat := 118140960795 + 6831802 * 2 ^ 59
def prefixEnd_6831802 : Nat := 4983230072969 + 3 ^ 40 * 6831802 * 2
def baseEnd_6831802 : Nat := 3507998162347784776956121

theorem tailTrace_6831802 : CollatzResearch.WordTrace tailWord_6831802 prefixEnd_6831802 3507998162347784776956121 := by
  unfold tailWord_6831802
  simp only [CollatzResearch.WordTrace]
  refine ⟨62294072398888901933674415, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166117526397037071823131773 62294072398888901933674415)
  ·
    refine ⟨93441108598333352900511623, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62294072398888901933674415 93441108598333352900511623)
    ·
      refine ⟨140161662897500029350767435, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93441108598333352900511623 140161662897500029350767435)
      ·
        refine ⟨210242494346250044026151153, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140161662897500029350767435 210242494346250044026151153)
        ·
          refine ⟨157681870759687533019613365, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210242494346250044026151153 157681870759687533019613365)
          ·
            refine ⟨14782675383720706220588753, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157681870759687533019613365 14782675383720706220588753)
            ·
              refine ⟨11087006537790529665441565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14782675383720706220588753 11087006537790529665441565)
              ·
                refine ⟨4157627451671448624540587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11087006537790529665441565 4157627451671448624540587)
                ·
                  refine ⟨6236441177507172936810881, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4157627451671448624540587 6236441177507172936810881)
                  ·
                    refine ⟨4677330883130379702608161, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6236441177507172936810881 4677330883130379702608161)
                    ·
                      refine ⟨3507998162347784776956121, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677330883130379702608161 3507998162347784776956121)
                      ·
                        rfl

theorem cell23_6831802_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 5, 2, 3, 1, 2, 2].length) (baseStart_6831802 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831802 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831802 prefixEnd_6831802 := by exact prefixLift 6831802
  have htrace : WordTrace (prefixWord ++ tailWord_6831802) baseStart_6831802 baseEnd_6831802 := by
    simpa [prefixWord, tailWord_6831802, baseEnd_6831802] using wordTrace_append hprefix tailTrace_6831802
  have hstable : (prefixWord ++ tailWord_6831802).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831802).length < 2 ^ (prefixWord ++ tailWord_6831802).sum := by decide
  have hdescent : baseEnd_6831802 < baseStart_6831802 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831802) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831824 : List Nat := [2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4]
def baseStart_6831824 : Nat := 118140960795 + 6831824 * 2 ^ 59
def prefixEnd_6831824 : Nat := 4983230072969 + 3 ^ 40 * 6831824 * 2
def baseEnd_6831824 : Nat := 3508009458922183690881019

theorem tailTrace_6831824 : CollatzResearch.WordTrace tailWord_6831824 prefixEnd_6831824 3508009458922183690881019 := by
  unfold tailWord_6831824
  simp only [CollatzResearch.WordTrace]
  refine ⟨124588546000737952745999263, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166118061334317270327999017 124588546000737952745999263)
  ·
    refine ⟨186882819001106929118998895, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124588546000737952745999263 186882819001106929118998895)
    ·
      refine ⟨280324228501660393678498343, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186882819001106929118998895 280324228501660393678498343)
      ·
        refine ⟨420486342752490590517747515, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280324228501660393678498343 420486342752490590517747515)
        ·
          refine ⟨630729514128735885776621273, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420486342752490590517747515 630729514128735885776621273)
          ·
            refine ⟨473047135596551914332465955, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630729514128735885776621273 473047135596551914332465955)
            ·
              refine ⟨709570703394827871498698933, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473047135596551914332465955 709570703394827871498698933)
              ·
                refine ⟨66522253443265112953003025, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 709570703394827871498698933 66522253443265112953003025)
                ·
                  refine ⟨49891690082448834714752269, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66522253443265112953003025 49891690082448834714752269)
                  ·
                    refine ⟨18709383780918313018032101, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49891690082448834714752269 18709383780918313018032101)
                    ·
                      refine ⟨3508009458922183690881019, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18709383780918313018032101 3508009458922183690881019)
                      ·
                        rfl

theorem cell23_6831824_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 2, 1, 5, 2, 3, 4].length) (baseStart_6831824 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831824 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831824 prefixEnd_6831824 := by exact prefixLift 6831824
  have htrace : WordTrace (prefixWord ++ tailWord_6831824) baseStart_6831824 baseEnd_6831824 := by
    simpa [prefixWord, tailWord_6831824, baseEnd_6831824] using wordTrace_append hprefix tailTrace_6831824
  have hstable : (prefixWord ++ tailWord_6831824).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831824).length < 2 ^ (prefixWord ++ tailWord_6831824).sum := by decide
  have hdescent : baseEnd_6831824 < baseStart_6831824 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831824) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831845 : List Nat := [1, 3, 1, 4, 1, 1, 4, 2, 1, 3, 2]
def baseStart_6831845 : Nat := 118140960795 + 6831845 * 2 ^ 59
def prefixEnd_6831845 : Nat := 4983230072969 + 3 ^ 40 * 6831845 * 2
def baseEnd_6831845 : Nat := 3508020242015928108718423

theorem tailTrace_6831845 : CollatzResearch.WordTrace tailWord_6831845 prefixEnd_6831845 3508020242015928108718423 := by
  unfold tailWord_6831845
  simp only [CollatzResearch.WordTrace]
  refine ⟨249177857934399826078512989, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166118571956266550719008659 249177857934399826078512989)
  ·
    refine ⟨93441696725399934779442371, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249177857934399826078512989 93441696725399934779442371)
    ·
      refine ⟨140162545088099902169163557, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93441696725399934779442371 140162545088099902169163557)
      ·
        refine ⟨26280477204018731656718167, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 140162545088099902169163557 26280477204018731656718167)
        ·
          refine ⟨39420715806028097485077251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26280477204018731656718167 39420715806028097485077251)
          ·
            refine ⟨59131073709042146227615877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39420715806028097485077251 59131073709042146227615877)
            ·
              refine ⟨11087076320445402417677977, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59131073709042146227615877 11087076320445402417677977)
              ·
                refine ⟨8315307240334051813258483, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11087076320445402417677977 8315307240334051813258483)
                ·
                  refine ⟨12472960860501077719887725, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315307240334051813258483 12472960860501077719887725)
                  ·
                    refine ⟨4677360322687904144957897, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12472960860501077719887725 4677360322687904144957897)
                    ·
                      refine ⟨3508020242015928108718423, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677360322687904144957897 3508020242015928108718423)
                      ·
                        rfl

theorem cell23_6831845_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 4, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_6831845 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831845 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831845 prefixEnd_6831845 := by exact prefixLift 6831845
  have htrace : WordTrace (prefixWord ++ tailWord_6831845) baseStart_6831845 baseEnd_6831845 := by
    simpa [prefixWord, tailWord_6831845, baseEnd_6831845] using wordTrace_append hprefix tailTrace_6831845
  have hstable : (prefixWord ++ tailWord_6831845).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831845).length < 2 ^ (prefixWord ++ tailWord_6831845).sum := by decide
  have hdescent : baseEnd_6831845 < baseStart_6831845 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831845) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831858 : List Nat := [3, 2, 1, 3, 1, 1, 2, 1, 3, 4, 2]
def baseStart_6831858 : Nat := 118140960795 + 6831858 * 2 ^ 59
def prefixEnd_6831858 : Nat := 4983230072969 + 3 ^ 40 * 6831858 * 2
def baseEnd_6831858 : Nat := 3508026917264436557855863

theorem tailTrace_6831858 : CollatzResearch.WordTrace tailWord_6831858 prefixEnd_6831858 3508026917264436557855863 := by
  unfold tailWord_6831858
  simp only [CollatzResearch.WordTrace]
  refine ⟨62294583020838182324684057, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166118888055568486199157485 62294583020838182324684057)
  ·
    refine ⟨46720937265628636743513043, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62294583020838182324684057 46720937265628636743513043)
    ·
      refine ⟨70081405898442955115269565, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46720937265628636743513043 70081405898442955115269565)
      ·
        refine ⟨26280527211916108168226087, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70081405898442955115269565 26280527211916108168226087)
        ·
          refine ⟨39420790817874162252339131, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26280527211916108168226087 39420790817874162252339131)
          ·
            refine ⟨59131186226811243378508697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39420790817874162252339131 59131186226811243378508697)
            ·
              refine ⟨44348389670108432533881523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59131186226811243378508697 44348389670108432533881523)
              ·
                refine ⟨66522584505162648800822285, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44348389670108432533881523 66522584505162648800822285)
                ·
                  refine ⟨24945969189435993300308357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66522584505162648800822285 24945969189435993300308357)
                  ·
                    refine ⟨4677369223019248743807817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24945969189435993300308357 4677369223019248743807817)
                    ·
                      refine ⟨3508026917264436557855863, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677369223019248743807817 3508026917264436557855863)
                      ·
                        rfl

theorem cell23_6831858_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 3, 1, 1, 2, 1, 3, 4, 2].length) (baseStart_6831858 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831858 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831858 prefixEnd_6831858 := by exact prefixLift 6831858
  have htrace : WordTrace (prefixWord ++ tailWord_6831858) baseStart_6831858 baseEnd_6831858 := by
    simpa [prefixWord, tailWord_6831858, baseEnd_6831858] using wordTrace_append hprefix tailTrace_6831858
  have hstable : (prefixWord ++ tailWord_6831858).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831858).length < 2 ^ (prefixWord ++ tailWord_6831858).sum := by decide
  have hdescent : baseEnd_6831858 < baseStart_6831858 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831858) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831921 : List Nat := [1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 5]
def baseStart_6831921 : Nat := 118140960795 + 6831921 * 2 ^ 59
def prefixEnd_6831921 : Nat := 4983230072969 + 3 ^ 40 * 6831921 * 2
def baseEnd_6831921 : Nat := 3508059266545669811368073

theorem tailTrace_6831921 : CollatzResearch.WordTrace tailWord_6831921 prefixEnd_6831921 3508059266545669811368073 := by
  unfold tailWord_6831921
  simp only [CollatzResearch.WordTrace]
  refine ⟨249180629882124491058279617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166120419921416327372186411 249180629882124491058279617)
  ·
    refine ⟨186885472411593368293709713, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249180629882124491058279617 186885472411593368293709713)
    ·
      refine ⟨140164104308695026220282285, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186885472411593368293709713 140164104308695026220282285)
      ·
        refine ⟨52561539115760634832605857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140164104308695026220282285 52561539115760634832605857)
        ·
          refine ⟨39421154336820476124454393, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52561539115760634832605857 39421154336820476124454393)
          ·
            refine ⟨29565865752615357093340795, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39421154336820476124454393 29565865752615357093340795)
            ·
              refine ⟨44348798628923035640011193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29565865752615357093340795 44348798628923035640011193)
              ·
                refine ⟨33261598971692276730008395, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44348798628923035640011193 33261598971692276730008395)
                ·
                  refine ⟨49892398457538415095012593, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33261598971692276730008395 49892398457538415095012593)
                  ·
                    refine ⟨37419298843153811321259445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49892398457538415095012593 37419298843153811321259445)
                    ·
                      refine ⟨3508059266545669811368073, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37419298843153811321259445 3508059266545669811368073)
                      ·
                        rfl

theorem cell23_6831921_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 3, 2, 2, 1, 2, 1, 2, 5].length) (baseStart_6831921 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831921 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831921 prefixEnd_6831921 := by exact prefixLift 6831921
  have htrace : WordTrace (prefixWord ++ tailWord_6831921) baseStart_6831921 baseEnd_6831921 := by
    simpa [prefixWord, tailWord_6831921, baseEnd_6831921] using wordTrace_append hprefix tailTrace_6831921
  have hstable : (prefixWord ++ tailWord_6831921).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831921).length < 2 ^ (prefixWord ++ tailWord_6831921).sum := by decide
  have hdescent : baseEnd_6831921 < baseStart_6831921 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831921) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831942 : List Nat := [6, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3]
def baseStart_6831942 : Nat := 118140960795 + 6831942 * 2 ^ 59
def prefixEnd_6831942 : Nat := 4983230072969 + 3 ^ 40 * 6831942 * 2
def baseEnd_6831942 : Nat := 3508070049639414229205477

theorem tailTrace_6831942 : CollatzResearch.WordTrace tailWord_6831942 prefixEnd_6831942 3508070049639414229205477 := by
  unfold tailWord_6831942
  simp only [CollatzResearch.WordTrace]
  refine ⟨7786918619220262863899815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166120930543365607763196053 7786918619220262863899815)
  ·
    refine ⟨11680377928830394295849723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7786918619220262863899815 11680377928830394295849723)
    ·
      refine ⟨17520566893245591443774585, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11680377928830394295849723 17520566893245591443774585)
      ·
        refine ⟨13140425169934193582830939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17520566893245591443774585 13140425169934193582830939)
        ·
          refine ⟨19710637754901290374246409, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13140425169934193582830939 19710637754901290374246409)
          ·
            refine ⟨14782978316175967780684807, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19710637754901290374246409 14782978316175967780684807)
            ·
              refine ⟨22174467474263951671027211, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14782978316175967780684807 22174467474263951671027211)
              ·
                refine ⟨33261701211395927506540817, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22174467474263951671027211 33261701211395927506540817)
                ·
                  refine ⟨24946275908546945629905613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33261701211395927506540817 24946275908546945629905613)
                  ·
                    refine ⟨9354853465705104611214605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24946275908546945629905613 9354853465705104611214605)
                    ·
                      refine ⟨3508070049639414229205477, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354853465705104611214605 3508070049639414229205477)
                      ·
                        rfl

theorem cell23_6831942_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 1, 2, 1, 2, 1, 1, 2, 3, 3].length) (baseStart_6831942 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831942 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831942 prefixEnd_6831942 := by exact prefixLift 6831942
  have htrace : WordTrace (prefixWord ++ tailWord_6831942) baseStart_6831942 baseEnd_6831942 := by
    simpa [prefixWord, tailWord_6831942, baseEnd_6831942] using wordTrace_append hprefix tailTrace_6831942
  have hstable : (prefixWord ++ tailWord_6831942).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831942).length < 2 ^ (prefixWord ++ tailWord_6831942).sum := by decide
  have hdescent : baseEnd_6831942 < baseStart_6831942 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831942) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6831968 : List Nat := [2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3]
def baseStart_6831968 : Nat := 118140960795 + 6831968 * 2 ^ 59
def prefixEnd_6831968 : Nat := 4983230072969 + 3 ^ 40 * 6831968 * 2
def baseEnd_6831968 : Nat := 3508083400136431127480357

theorem tailTrace_6831968 : CollatzResearch.WordTrace tailWord_6831968 prefixEnd_6831968 3508083400136431127480357 := by
  unfold tailWord_6831968
  simp only [CollatzResearch.WordTrace]
  refine ⟨124591172056477109042620279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166121562741969478723493705 124591172056477109042620279)
  ·
    refine ⟨186886758084715663563930419, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124591172056477109042620279 186886758084715663563930419)
    ·
      refine ⟨280330137127073495345895629, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186886758084715663563930419 280330137127073495345895629)
      ·
        refine ⟨105123801422652560754710861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280330137127073495345895629 105123801422652560754710861)
        ·
          refine ⟨39421425533494710283016573, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105123801422652560754710861 39421425533494710283016573)
          ·
            refine ⟨14783034575060516356131215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39421425533494710283016573 14783034575060516356131215)
            ·
              refine ⟨22174551862590774534196823, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783034575060516356131215 22174551862590774534196823)
              ·
                refine ⟨33261827793886161801295235, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22174551862590774534196823 33261827793886161801295235)
                ·
                  refine ⟨49892741690829242701942853, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33261827793886161801295235 49892741690829242701942853)
                  ·
                    refine ⟨9354889067030483006614285, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49892741690829242701942853 9354889067030483006614285)
                    ·
                      refine ⟨3508083400136431127480357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9354889067030483006614285 3508083400136431127480357)
                      ·
                        rfl

theorem cell23_6831968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 3, 3, 1, 1, 1, 4, 3].length) (baseStart_6831968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6831968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6831968 prefixEnd_6831968 := by exact prefixLift 6831968
  have htrace : WordTrace (prefixWord ++ tailWord_6831968) baseStart_6831968 baseEnd_6831968 := by
    simpa [prefixWord, tailWord_6831968, baseEnd_6831968] using wordTrace_append hprefix tailTrace_6831968
  have hstable : (prefixWord ++ tailWord_6831968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6831968).length < 2 ^ (prefixWord ++ tailWord_6831968).sum := by decide
  have hdescent : baseEnd_6831968 < baseStart_6831968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6831968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832051 : List Nat := [1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6]
def baseStart_6832051 : Nat := 118140960795 + 6832051 * 2 ^ 59
def prefixEnd_6832051 : Nat := 4983230072969 + 3 ^ 40 * 6832051 * 2
def baseEnd_6832051 : Nat := 3508126019030754302742475

theorem tailTrace_6832051 : CollatzResearch.WordTrace tailWord_6832051 prefixEnd_6832051 3508126019030754302742475 := by
  unfold tailWord_6832051
  simp only [CollatzResearch.WordTrace]
  refine ⟨249185371371653523260512007, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166123580914435682173674671 249185371371653523260512007)
  ·
    refine ⟨373778057057480284890768011, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249185371371653523260512007 373778057057480284890768011)
    ·
      refine ⟨560667085586220427336152017, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373778057057480284890768011 560667085586220427336152017)
      ·
        refine ⟨420500314189665320502114013, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560667085586220427336152017 420500314189665320502114013)
        ·
          refine ⟨157687617821124495188292755, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 420500314189665320502114013 157687617821124495188292755)
          ·
            refine ⟨236531426731686742782439133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157687617821124495188292755 236531426731686742782439133)
            ·
              refine ⟨88699285024382528543414675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236531426731686742782439133 88699285024382528543414675)
              ·
                refine ⟨133048927536573792815122013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88699285024382528543414675 133048927536573792815122013)
                ·
                  refine ⟨49893347826215172305670755, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 133048927536573792815122013 49893347826215172305670755)
                  ·
                    refine ⟨74840021739322758458506133, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49893347826215172305670755 74840021739322758458506133)
                    ·
                      refine ⟨3508126019030754302742475, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74840021739322758458506133 3508126019030754302742475)
                      ·
                        rfl

theorem cell23_6832051_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 3, 1, 3, 1, 3, 1, 6].length) (baseStart_6832051 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832051 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832051 prefixEnd_6832051 := by exact prefixLift 6832051
  have htrace : WordTrace (prefixWord ++ tailWord_6832051) baseStart_6832051 baseEnd_6832051 := by
    simpa [prefixWord, tailWord_6832051, baseEnd_6832051] using wordTrace_append hprefix tailTrace_6832051
  have hstable : (prefixWord ++ tailWord_6832051).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832051).length < 2 ^ (prefixWord ++ tailWord_6832051).sum := by decide
  have hdescent : baseEnd_6832051 < baseStart_6832051 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832051) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832072 : List Nat := [2, 1, 3, 1, 4, 3, 1, 2, 1, 1, 4]
def baseStart_6832072 : Nat := 118140960795 + 6832072 * 2 ^ 59
def prefixEnd_6832072 : Nat := 4983230072969 + 3 ^ 40 * 6832072 * 2
def baseEnd_6832072 : Nat := 3508136802124498720579879

theorem tailTrace_6832072 : CollatzResearch.WordTrace tailWord_6832072 prefixEnd_6832072 3508136802124498720579879 := by
  unfold tailWord_6832072
  simp only [CollatzResearch.WordTrace]
  refine ⟨124593068652288721923513235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166124091536384962564684313 124593068652288721923513235)
  ·
    refine ⟨186889602978433082885269853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124593068652288721923513235 186889602978433082885269853)
    ·
      refine ⟨70083601116912406081976195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186889602978433082885269853 70083601116912406081976195)
      ·
        refine ⟨105125401675368609122964293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70083601116912406081976195 105125401675368609122964293)
        ·
          refine ⟨19711012814131614210555805, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105125401675368609122964293 19711012814131614210555805)
          ·
            refine ⟨7391629805299355328958427, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19711012814131614210555805 7391629805299355328958427)
            ·
              refine ⟨11087444707949032993437641, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391629805299355328958427 11087444707949032993437641)
              ·
                refine ⟨8315583530961774745078231, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11087444707949032993437641 8315583530961774745078231)
                ·
                  refine ⟨12473375296442662117617347, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315583530961774745078231 12473375296442662117617347)
                  ·
                    refine ⟨18710062944663993176426021, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12473375296442662117617347 18710062944663993176426021)
                    ·
                      refine ⟨3508136802124498720579879, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18710062944663993176426021 3508136802124498720579879)
                      ·
                        rfl

theorem cell23_6832072_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 4, 3, 1, 2, 1, 1, 4].length) (baseStart_6832072 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832072 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832072 prefixEnd_6832072 := by exact prefixLift 6832072
  have htrace : WordTrace (prefixWord ++ tailWord_6832072) baseStart_6832072 baseEnd_6832072 := by
    simpa [prefixWord, tailWord_6832072, baseEnd_6832072] using wordTrace_append hprefix tailTrace_6832072
  have hstable : (prefixWord ++ tailWord_6832072).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832072).length < 2 ^ (prefixWord ++ tailWord_6832072).sum := by decide
  have hdescent : baseEnd_6832072 < baseStart_6832072 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832072) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832085 : List Nat := [1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 4]
def baseStart_6832085 : Nat := 118140960795 + 6832085 * 2 ^ 59
def prefixEnd_6832085 : Nat := 4983230072969 + 3 ^ 40 * 6832085 * 2
def baseEnd_6832085 : Nat := 3508143477373007169717319

theorem tailTrace_6832085 : CollatzResearch.WordTrace tailWord_6832085 prefixEnd_6832085 3508143477373007169717319 := by
  unfold tailWord_6832085
  simp only [CollatzResearch.WordTrace]
  refine ⟨249186611453530347067249709, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166124407635686898044833139 249186611453530347067249709)
  ·
    refine ⟨93444979295073880150218641, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249186611453530347067249709 93444979295073880150218641)
    ·
      refine ⟨70083734471305410112663981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93444979295073880150218641 70083734471305410112663981)
      ·
        refine ⟨26281400426739528792248993, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70083734471305410112663981 26281400426739528792248993)
        ·
          refine ⟨19711050320054646594186745, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26281400426739528792248993 19711050320054646594186745)
          ·
            refine ⟨14783287740040984945640059, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19711050320054646594186745 14783287740040984945640059)
            ·
              refine ⟨22174931610061477418460089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783287740040984945640059 22174931610061477418460089)
              ·
                refine ⟨16631198707546108063845067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22174931610061477418460089 16631198707546108063845067)
                ·
                  refine ⟨24946798061319162095767601, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16631198707546108063845067 24946798061319162095767601)
                  ·
                    refine ⟨18710098545989371571825701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24946798061319162095767601 18710098545989371571825701)
                    ·
                      refine ⟨3508143477373007169717319, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18710098545989371571825701 3508143477373007169717319)
                      ·
                        rfl

theorem cell23_6832085_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 3, 2, 2, 1, 2, 1, 2, 4].length) (baseStart_6832085 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832085 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832085 prefixEnd_6832085 := by exact prefixLift 6832085
  have htrace : WordTrace (prefixWord ++ tailWord_6832085) baseStart_6832085 baseEnd_6832085 := by
    simpa [prefixWord, tailWord_6832085, baseEnd_6832085] using wordTrace_append hprefix tailTrace_6832085
  have hstable : (prefixWord ++ tailWord_6832085).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832085).length < 2 ^ (prefixWord ++ tailWord_6832085).sum := by decide
  have hdescent : baseEnd_6832085 < baseStart_6832085 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832085) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832149 : List Nat := [1, 3, 2, 1, 5, 1, 1, 3, 1, 3, 2]
def baseStart_6832149 : Nat := 118140960795 + 6832149 * 2 ^ 59
def prefixEnd_6832149 : Nat := 4983230072969 + 3 ^ 40 * 6832149 * 2
def baseEnd_6832149 : Nat := 3508176340134894919317025

theorem tailTrace_6832149 : CollatzResearch.WordTrace tailWord_6832149 prefixEnd_6832149 3508176340134894919317025 := by
  unfold tailWord_6832149
  simp only [CollatzResearch.WordTrace]
  refine ⟨249188945725298485997579501, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166125963816865657331719667 249188945725298485997579501)
  ·
    refine ⟨93445854646986932249092313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249188945725298485997579501 93445854646986932249092313)
    ·
      refine ⟨70084390985240199186819235, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93445854646986932249092313 70084390985240199186819235)
      ·
        refine ⟨105126586477860298780228853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70084390985240199186819235 105126586477860298780228853)
        ·
          refine ⟨9855617482299403010646455, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 105126586477860298780228853 9855617482299403010646455)
          ·
            refine ⟨14783426223449104515969683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855617482299403010646455 14783426223449104515969683)
            ·
              refine ⟨22175139335173656773954525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783426223449104515969683 22175139335173656773954525)
              ·
                refine ⟨8315677250690121290232947, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22175139335173656773954525 8315677250690121290232947)
                ·
                  refine ⟨12473515876035181935349421, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315677250690121290232947 12473515876035181935349421)
                  ·
                    refine ⟨4677568453513193225756033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12473515876035181935349421 4677568453513193225756033)
                    ·
                      refine ⟨3508176340134894919317025, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677568453513193225756033 3508176340134894919317025)
                      ·
                        rfl

theorem cell23_6832149_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 5, 1, 1, 3, 1, 3, 2].length) (baseStart_6832149 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832149 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832149 prefixEnd_6832149 := by exact prefixLift 6832149
  have htrace : WordTrace (prefixWord ++ tailWord_6832149) baseStart_6832149 baseEnd_6832149 := by
    simpa [prefixWord, tailWord_6832149, baseEnd_6832149] using wordTrace_append hprefix tailTrace_6832149
  have hstable : (prefixWord ++ tailWord_6832149).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832149).length < 2 ^ (prefixWord ++ tailWord_6832149).sum := by decide
  have hdescent : baseEnd_6832149 < baseStart_6832149 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832149) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832248 : List Nat := [2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_6832248 : Nat := 118140960795 + 6832248 * 2 ^ 59
def prefixEnd_6832248 : Nat := 4983230072969 + 3 ^ 40 * 6832248 * 2
def baseEnd_6832248 : Nat := 3508227174719690031979069

theorem tailTrace_6832248 : CollatzResearch.WordTrace tailWord_6832248 prefixEnd_6832248 3508227174719690031979069 := by
  unfold tailWord_6832248
  simp only [CollatzResearch.WordTrace]
  refine ⟨124596278275969912952716699, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166128371034626550603622265 124596278275969912952716699)
  ·
    refine ⟨186894417413954869429075049, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124596278275969912952716699 186894417413954869429075049)
    ·
      refine ⟨140170813060466152071806287, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186894417413954869429075049 140170813060466152071806287)
      ·
        refine ⟨210256219590699228107709431, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140170813060466152071806287 210256219590699228107709431)
        ·
          refine ⟨315384329386048842161564147, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210256219590699228107709431 315384329386048842161564147)
          ·
            refine ⟨473076494079073263242346221, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315384329386048842161564147 473076494079073263242346221)
            ·
              refine ⟨177403685279652473715879833, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473076494079073263242346221 177403685279652473715879833)
              ·
                refine ⟨133052763959739355286909875, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 177403685279652473715879833 133052763959739355286909875)
                ·
                  refine ⟨199579145939609032930364813, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 133052763959739355286909875 199579145939609032930364813)
                  ·
                    refine ⟨74842179727353387348886805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 199579145939609032930364813 74842179727353387348886805)
                    ·
                      refine ⟨3508227174719690031979069, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74842179727353387348886805 3508227174719690031979069)
                      ·
                        rfl

theorem cell23_6832248_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_6832248 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832248 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832248 prefixEnd_6832248 := by exact prefixLift 6832248
  have htrace : WordTrace (prefixWord ++ tailWord_6832248) baseStart_6832248 baseEnd_6832248 := by
    simpa [prefixWord, tailWord_6832248, baseEnd_6832248] using wordTrace_append hprefix tailTrace_6832248
  have hstable : (prefixWord ++ tailWord_6832248).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832248).length < 2 ^ (prefixWord ++ tailWord_6832248).sum := by decide
  have hdescent : baseEnd_6832248 < baseStart_6832248 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832248) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832252 : List Nat := [2, 2, 2, 1, 1, 5, 2, 1, 2, 1, 4]
def baseStart_6832252 : Nat := 118140960795 + 6832252 * 2 ^ 59
def prefixEnd_6832252 : Nat := 4983230072969 + 3 ^ 40 * 6832252 * 2
def baseEnd_6832252 : Nat := 3508229228642308016329051

theorem tailTrace_6832252 : CollatzResearch.WordTrace tailWord_6832252 prefixEnd_6832252 3508229228642308016329051 := by
  unfold tailWord_6832252
  simp only [CollatzResearch.WordTrace]
  refine ⟨124596351221962667294289505, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166128468295950223059052673 124596351221962667294289505)
  ·
    refine ⟨93447263416472000470717129, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124596351221962667294289505 93447263416472000470717129)
    ·
      refine ⟨70085447562354000353037847, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93447263416472000470717129 70085447562354000353037847)
      ·
        refine ⟨105128171343531000529556771, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70085447562354000353037847 105128171343531000529556771)
        ·
          refine ⟨157692257015296500794335157, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105128171343531000529556771 157692257015296500794335157)
          ·
            refine ⟨14783649095184046949468921, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157692257015296500794335157 14783649095184046949468921)
            ·
              refine ⟨11087736821388035212101691, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14783649095184046949468921 11087736821388035212101691)
              ·
                refine ⟨16631605232082052818152537, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11087736821388035212101691 16631605232082052818152537)
                ·
                  refine ⟨12473703924061539613614403, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16631605232082052818152537 12473703924061539613614403)
                  ·
                    refine ⟨18710555886092309420421605, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12473703924061539613614403 18710555886092309420421605)
                    ·
                      refine ⟨3508229228642308016329051, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18710555886092309420421605 3508229228642308016329051)
                      ·
                        rfl

theorem cell23_6832252_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 5, 2, 1, 2, 1, 4].length) (baseStart_6832252 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832252 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832252 prefixEnd_6832252 := by exact prefixLift 6832252
  have htrace : WordTrace (prefixWord ++ tailWord_6832252) baseStart_6832252 baseEnd_6832252 := by
    simpa [prefixWord, tailWord_6832252, baseEnd_6832252] using wordTrace_append hprefix tailTrace_6832252
  have hstable : (prefixWord ++ tailWord_6832252).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832252).length < 2 ^ (prefixWord ++ tailWord_6832252).sum := by decide
  have hdescent : baseEnd_6832252 < baseStart_6832252 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832252) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832286 : List Nat := [4, 3, 1, 1, 3, 1, 1, 1, 2, 4, 2]
def baseStart_6832286 : Nat := 118140960795 + 6832286 * 2 ^ 59
def prefixEnd_6832286 : Nat := 4983230072969 + 3 ^ 40 * 6832286 * 2
def baseEnd_6832286 : Nat := 3508246686984560883303895

theorem tailTrace_6832286 : CollatzResearch.WordTrace tailWord_6832286 prefixEnd_6832286 3508246686984560883303895 := by
  unfold tailWord_6832286
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149242815725269799414589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166129295017201438930211141 31149242815725269799414589)
  ·
    refine ⟨11680966055896976174780471, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31149242815725269799414589 11680966055896976174780471)
    ·
      refine ⟨17521449083845464262170707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11680966055896976174780471 17521449083845464262170707)
      ·
        refine ⟨26282173625768196393256061, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17521449083845464262170707 26282173625768196393256061)
        ·
          refine ⟨9855815109663073647471023, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26282173625768196393256061 9855815109663073647471023)
          ·
            refine ⟨14783722664494610471206535, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9855815109663073647471023 14783722664494610471206535)
            ·
              refine ⟨22175583996741915706809803, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14783722664494610471206535 22175583996741915706809803)
              ·
                refine ⟨33263375995112873560214705, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22175583996741915706809803 33263375995112873560214705)
                ·
                  refine ⟨24947531996334655170161029, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33263375995112873560214705 24947531996334655170161029)
                  ·
                    refine ⟨4677662249312747844405193, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24947531996334655170161029 4677662249312747844405193)
                    ·
                      refine ⟨3508246686984560883303895, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677662249312747844405193 3508246686984560883303895)
                      ·
                        rfl

theorem cell23_6832286_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 3, 1, 1, 1, 2, 4, 2].length) (baseStart_6832286 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832286 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832286 prefixEnd_6832286 := by exact prefixLift 6832286
  have htrace : WordTrace (prefixWord ++ tailWord_6832286) baseStart_6832286 baseEnd_6832286 := by
    simpa [prefixWord, tailWord_6832286, baseEnd_6832286] using wordTrace_append hprefix tailTrace_6832286
  have hstable : (prefixWord ++ tailWord_6832286).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832286).length < 2 ^ (prefixWord ++ tailWord_6832286).sum := by decide
  have hdescent : baseEnd_6832286 < baseStart_6832286 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832286) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832312 : List Nat := [2, 1, 2, 1, 2, 1, 5, 1, 1, 5, 2]
def baseStart_6832312 : Nat := 118140960795 + 6832312 * 2 ^ 59
def prefixEnd_6832312 : Nat := 4983230072969 + 3 ^ 40 * 6832312 * 2
def baseEnd_6832312 : Nat := 3508260037481577781578775

theorem tailTrace_6832312 : CollatzResearch.WordTrace tailWord_6832312 prefixEnd_6832312 3508260037481577781578775 := by
  unfold tailWord_6832312
  simp only [CollatzResearch.WordTrace]
  refine ⟨124597445411853982417881595, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166129927215805309890508793 124597445411853982417881595)
  ·
    refine ⟨186896168117780973626822393, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124597445411853982417881595 186896168117780973626822393)
    ·
      refine ⟨140172126088335730220116795, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186896168117780973626822393 140172126088335730220116795)
      ·
        refine ⟨210258189132503595330175193, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140172126088335730220116795 210258189132503595330175193)
        ·
          refine ⟨157693641849377696497631395, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210258189132503595330175193 157693641849377696497631395)
          ·
            refine ⟨236540462774066544746447093, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157693641849377696497631395 236540462774066544746447093)
            ·
              refine ⟨22175668385068738569979415, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236540462774066544746447093 22175668385068738569979415)
              ·
                refine ⟨33263502577603107854969123, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22175668385068738569979415 33263502577603107854969123)
                ·
                  refine ⟨49895253866404661782453685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33263502577603107854969123 49895253866404661782453685)
                  ·
                    refine ⟨4677680049975437042105033, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49895253866404661782453685 4677680049975437042105033)
                    ·
                      refine ⟨3508260037481577781578775, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677680049975437042105033 3508260037481577781578775)
                      ·
                        rfl

theorem cell23_6832312_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 1, 5, 1, 1, 5, 2].length) (baseStart_6832312 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832312 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832312 prefixEnd_6832312 := by exact prefixLift 6832312
  have htrace : WordTrace (prefixWord ++ tailWord_6832312) baseStart_6832312 baseEnd_6832312 := by
    simpa [prefixWord, tailWord_6832312, baseEnd_6832312] using wordTrace_append hprefix tailTrace_6832312
  have hstable : (prefixWord ++ tailWord_6832312).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832312).length < 2 ^ (prefixWord ++ tailWord_6832312).sum := by decide
  have hdescent : baseEnd_6832312 < baseStart_6832312 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832312) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832345 : List Nat := [1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 5]
def baseStart_6832345 : Nat := 118140960795 + 6832345 * 2 ^ 59
def prefixEnd_6832345 : Nat := 4983230072969 + 3 ^ 40 * 6832345 * 2
def baseEnd_6832345 : Nat := 3508276982343176152466123

theorem tailTrace_6832345 : CollatzResearch.WordTrace tailWord_6832345 prefixEnd_6832345 3508276982343176152466123 := by
  unfold tailWord_6832345
  simp only [CollatzResearch.WordTrace]
  refine ⟨249196094432588411471714489, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166130729621725607647809659 249196094432588411471714489)
  ·
    refine ⟨186897070824441308603785867, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249196094432588411471714489 186897070824441308603785867)
    ·
      refine ⟨280345606236661962905678801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186897070824441308603785867 280345606236661962905678801)
      ·
        refine ⟨210259204677496472179259101, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280345606236661962905678801 210259204677496472179259101)
        ·
          refine ⟨78847201754061177067222163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210259204677496472179259101 78847201754061177067222163)
          ·
            refine ⟨118270802631091765600833245, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78847201754061177067222163 118270802631091765600833245)
            ·
              refine ⟨44351550986659412100312467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118270802631091765600833245 44351550986659412100312467)
              ·
                refine ⟨66527326479989118150468701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44351550986659412100312467 66527326479989118150468701)
                ·
                  refine ⟨24947747429995919306425763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66527326479989118150468701 24947747429995919306425763)
                  ·
                    refine ⟨37421621144993878959638645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24947747429995919306425763 37421621144993878959638645)
                    ·
                      refine ⟨3508276982343176152466123, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37421621144993878959638645 3508276982343176152466123)
                      ·
                        rfl

theorem cell23_6832345_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 3, 1, 3, 1, 3, 1, 5].length) (baseStart_6832345 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832345 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832345 prefixEnd_6832345 := by exact prefixLift 6832345
  have htrace : WordTrace (prefixWord ++ tailWord_6832345) baseStart_6832345 baseEnd_6832345 := by
    simpa [prefixWord, tailWord_6832345, baseEnd_6832345] using wordTrace_append hprefix tailTrace_6832345
  have hstable : (prefixWord ++ tailWord_6832345).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832345).length < 2 ^ (prefixWord ++ tailWord_6832345).sum := by decide
  have hdescent : baseEnd_6832345 < baseStart_6832345 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832345) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832359 : List Nat := [1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 4]
def baseStart_6832359 : Nat := 118140960795 + 6832359 * 2 ^ 59
def prefixEnd_6832359 : Nat := 4983230072969 + 3 ^ 40 * 6832359 * 2
def baseEnd_6832359 : Nat := 3508284171072339097691059

theorem tailTrace_6832359 : CollatzResearch.WordTrace tailWord_6832359 prefixEnd_6832359 3508284171072339097691059 := by
  unfold tailWord_6832359
  simp only [CollatzResearch.WordTrace]
  refine ⟨249196605054537691862724131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166131070036358461241816087 249196605054537691862724131)
  ·
    refine ⟨373794907581806537794086197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249196605054537691862724131 373794907581806537794086197)
    ·
      refine ⟨35043272585794362918195581, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 373794907581806537794086197 35043272585794362918195581)
      ·
        refine ⟨13141227219672886094323343, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35043272585794362918195581 13141227219672886094323343)
        ·
          refine ⟨19711840829509329141485015, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141227219672886094323343 19711840829509329141485015)
          ·
            refine ⟨29567761244263993712227523, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19711840829509329141485015 29567761244263993712227523)
            ·
              refine ⟨44351641866395990568341285, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29567761244263993712227523 44351641866395990568341285)
              ·
                refine ⟨8315932849949248231563991, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44351641866395990568341285 8315932849949248231563991)
                ·
                  refine ⟨12473899274923872347345987, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315932849949248231563991 12473899274923872347345987)
                  ·
                    refine ⟨18710848912385808521018981, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12473899274923872347345987 18710848912385808521018981)
                    ·
                      refine ⟨3508284171072339097691059, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18710848912385808521018981 3508284171072339097691059)
                      ·
                        rfl

theorem cell23_6832359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 3, 1, 1, 1, 4, 1, 1, 4].length) (baseStart_6832359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832359 prefixEnd_6832359 := by exact prefixLift 6832359
  have htrace : WordTrace (prefixWord ++ tailWord_6832359) baseStart_6832359 baseEnd_6832359 := by
    simpa [prefixWord, tailWord_6832359, baseEnd_6832359] using wordTrace_append hprefix tailTrace_6832359
  have hstable : (prefixWord ++ tailWord_6832359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832359).length < 2 ^ (prefixWord ++ tailWord_6832359).sum := by decide
  have hdescent : baseEnd_6832359 < baseStart_6832359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832395 : List Nat := [1, 1, 1, 1, 5, 2, 2, 1, 2, 7]
def baseStart_6832395 : Nat := 118140960795 + 6832395 * 2 ^ 59
def prefixEnd_6832395 : Nat := 4983230072969 + 3 ^ 40 * 6832395 * 2
def baseEnd_6832395 : Nat := 1169434218791966985613631

theorem tailTrace_6832395 : CollatzResearch.WordTrace tailWord_6832395 prefixEnd_6832395 1169434218791966985613631 := by
  unfold tailWord_6832395
  simp only [CollatzResearch.WordTrace]
  refine ⟨249197918082407270011034639, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166131945388271513340689759 249197918082407270011034639)
  ·
    refine ⟨373796877123610905016551959, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249197918082407270011034639 373796877123610905016551959)
    ·
      refine ⟨560695315685416357524827939, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373796877123610905016551959 560695315685416357524827939)
      ·
        refine ⟨841042973528124536287241909, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560695315685416357524827939 841042973528124536287241909)
        ·
          refine ⟨78847778768261675276928929, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 841042973528124536287241909 78847778768261675276928929)
          ·
            refine ⟨59135834076196256457696697, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78847778768261675276928929 59135834076196256457696697)
            ·
              refine ⟨44351875557147192343272523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59135834076196256457696697 44351875557147192343272523)
              ·
                refine ⟨66527813335720788514908785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44351875557147192343272523 66527813335720788514908785)
                ·
                  refine ⟨49895860001790591386181589, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66527813335720788514908785 49895860001790591386181589)
                  ·
                    refine ⟨1169434218791966985613631, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49895860001790591386181589 1169434218791966985613631)
                    ·
                      rfl

theorem cell23_6832395_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 5, 2, 2, 1, 2, 7].length) (baseStart_6832395 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832395 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832395 prefixEnd_6832395 := by exact prefixLift 6832395
  have htrace : WordTrace (prefixWord ++ tailWord_6832395) baseStart_6832395 baseEnd_6832395 := by
    simpa [prefixWord, tailWord_6832395, baseEnd_6832395] using wordTrace_append hprefix tailTrace_6832395
  have hstable : (prefixWord ++ tailWord_6832395).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832395).length < 2 ^ (prefixWord ++ tailWord_6832395).sum := by decide
  have hdescent : baseEnd_6832395 < baseStart_6832395 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832395) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832413 : List Nat := [1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 3]
def baseStart_6832413 : Nat := 118140960795 + 6832413 * 2 ^ 59
def prefixEnd_6832413 : Nat := 4983230072969 + 3 ^ 40 * 6832413 * 2
def baseEnd_6832413 : Nat := 3508311899027681886415811

theorem tailTrace_6832413 : CollatzResearch.WordTrace tailWord_6832413 prefixEnd_6832413 3508311899027681886415811 := by
  unfold tailWord_6832413
  simp only [CollatzResearch.WordTrace]
  refine ⟨249198574596342059085189893, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166132383064228039390126595 249198574596342059085189893)
  ·
    refine ⟨46724732736814136078473105, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249198574596342059085189893 46724732736814136078473105)
    ·
      refine ⟨35043549552610602058854829, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46724732736814136078473105 35043549552610602058854829)
      ·
        refine ⟨13141331082228975772070561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35043549552610602058854829 13141331082228975772070561)
        ·
          refine ⟨9855998311671731829052921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13141331082228975772070561 9855998311671731829052921)
          ·
            refine ⟨7391998733753798871789691, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9855998311671731829052921 7391998733753798871789691)
            ·
              refine ⟨11087998100630698307684537, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7391998733753798871789691 11087998100630698307684537)
              ·
                refine ⟨8315998575473023730763403, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11087998100630698307684537 8315998575473023730763403)
                ·
                  refine ⟨12473997863209535596145105, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8315998575473023730763403 12473997863209535596145105)
                  ·
                    refine ⟨9355498397407151697108829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12473997863209535596145105 9355498397407151697108829)
                    ·
                      refine ⟨3508311899027681886415811, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9355498397407151697108829 3508311899027681886415811)
                      ·
                        rfl

theorem cell23_6832413_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 3, 2, 2, 1, 2, 1, 2, 3].length) (baseStart_6832413 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832413 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832413 prefixEnd_6832413 := by exact prefixLift 6832413
  have htrace : WordTrace (prefixWord ++ tailWord_6832413) baseStart_6832413 baseEnd_6832413 := by
    simpa [prefixWord, tailWord_6832413, baseEnd_6832413] using wordTrace_append hprefix tailTrace_6832413
  have hstable : (prefixWord ++ tailWord_6832413).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832413).length < 2 ^ (prefixWord ++ tailWord_6832413).sum := by decide
  have hdescent : baseEnd_6832413 < baseStart_6832413 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832413) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832419 : List Nat := [1, 1, 1, 4, 2, 2, 3, 1, 3, 3, 2]
def baseStart_6832419 : Nat := 118140960795 + 6832419 * 2 ^ 59
def prefixEnd_6832419 : Nat := 4983230072969 + 3 ^ 40 * 6832419 * 2
def baseEnd_6832419 : Nat := 3508314979911608862940783

theorem tailTrace_6832419 : CollatzResearch.WordTrace tailWord_6832419 prefixEnd_6832419 3508314979911608862940783 := by
  unfold tailWord_6832419
  simp only [CollatzResearch.WordTrace]
  refine ⟨249198793434320322109908311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166132528956213548073272207 249198793434320322109908311)
  ·
    refine ⟨373798190151480483164862467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249198793434320322109908311 373798190151480483164862467)
    ·
      refine ⟨560697285227220724747293701, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373798190151480483164862467 560697285227220724747293701)
      ·
        refine ⟨105130740980103885890117569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 560697285227220724747293701 105130740980103885890117569)
        ·
          refine ⟨78848055735077914417588177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105130740980103885890117569 78848055735077914417588177)
          ·
            refine ⟨59136041801308435813191133, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78848055735077914417588177 59136041801308435813191133)
            ·
              refine ⟨22176015675490663429946675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59136041801308435813191133 22176015675490663429946675)
              ·
                refine ⟨33264023513235995144920013, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22176015675490663429946675 33264023513235995144920013)
                ·
                  refine ⟨12474008817463498179345005, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33264023513235995144920013 12474008817463498179345005)
                  ·
                    refine ⟨4677753306548811817254377, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12474008817463498179345005 4677753306548811817254377)
                    ·
                      refine ⟨3508314979911608862940783, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677753306548811817254377 3508314979911608862940783)
                      ·
                        rfl

theorem cell23_6832419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 2, 2, 3, 1, 3, 3, 2].length) (baseStart_6832419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832419 prefixEnd_6832419 := by exact prefixLift 6832419
  have htrace : WordTrace (prefixWord ++ tailWord_6832419) baseStart_6832419 baseEnd_6832419 := by
    simpa [prefixWord, tailWord_6832419, baseEnd_6832419] using wordTrace_append hprefix tailTrace_6832419
  have hstable : (prefixWord ++ tailWord_6832419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832419).length < 2 ^ (prefixWord ++ tailWord_6832419).sum := by decide
  have hdescent : baseEnd_6832419 < baseStart_6832419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832423 : List Nat := [1, 1, 8, 1, 1, 1, 1, 2, 1, 2, 4]
def baseStart_6832423 : Nat := 118140960795 + 6832423 * 2 ^ 59
def prefixEnd_6832423 : Nat := 4983230072969 + 3 ^ 40 * 6832423 * 2
def baseEnd_6832423 : Nat := 3508317033834226847290765

theorem tailTrace_6832423 : CollatzResearch.WordTrace tailWord_6832423 prefixEnd_6832423 3508317033834226847290765 := by
  unfold tailWord_6832423
  simp only [CollatzResearch.WordTrace]
  refine ⟨249198939326305830793053923, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166132626217537220528702615 249198939326305830793053923)
  ·
    refine ⟨373798408989458746189580885, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249198939326305830793053923 373798408989458746189580885)
    ·
      refine ⟨4380450105345219681909151, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 8 373798408989458746189580885 4380450105345219681909151)
      ·
        refine ⟨6570675158017829522863727, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380450105345219681909151 6570675158017829522863727)
        ·
          refine ⟨9856012737026744284295591, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6570675158017829522863727 9856012737026744284295591)
          ·
            refine ⟨14784019105540116426443387, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856012737026744284295591 14784019105540116426443387)
            ·
              refine ⟨22176028658310174639665081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14784019105540116426443387 22176028658310174639665081)
              ·
                refine ⟨16632021493732630979748811, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22176028658310174639665081 16632021493732630979748811)
                ·
                  refine ⟨24948032240598946469623217, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16632021493732630979748811 24948032240598946469623217)
                  ·
                    refine ⟨18711024180449209852217413, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24948032240598946469623217 18711024180449209852217413)
                    ·
                      refine ⟨3508317033834226847290765, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18711024180449209852217413 3508317033834226847290765)
                      ·
                        rfl

theorem cell23_6832423_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 8, 1, 1, 1, 1, 2, 1, 2, 4].length) (baseStart_6832423 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832423 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832423 prefixEnd_6832423 := by exact prefixLift 6832423
  have htrace : WordTrace (prefixWord ++ tailWord_6832423) baseStart_6832423 baseEnd_6832423 := by
    simpa [prefixWord, tailWord_6832423, baseEnd_6832423] using wordTrace_append hprefix tailTrace_6832423
  have hstable : (prefixWord ++ tailWord_6832423).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832423).length < 2 ^ (prefixWord ++ tailWord_6832423).sum := by decide
  have hdescent : baseEnd_6832423 < baseStart_6832423 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832423) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832426 : List Nat := [3, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3]
def baseStart_6832426 : Nat := 118140960795 + 6832426 * 2 ^ 59
def prefixEnd_6832426 : Nat := 4983230072969 + 3 ^ 40 * 6832426 * 2
def baseEnd_6832426 : Nat := 3508318574276190335553251

theorem tailTrace_6832426 : CollatzResearch.WordTrace tailWord_6832426 prefixEnd_6832426 3508318574276190335553251 := by
  unfold tailWord_6832426
  simp only [CollatzResearch.WordTrace]
  refine ⟨62299762186323740576353283, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166132699163529974870275421 62299762186323740576353283)
  ·
    refine ⟨93449643279485610864529925, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62299762186323740576353283 93449643279485610864529925)
    ·
      refine ⟨17521808114903552037099361, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93449643279485610864529925 17521808114903552037099361)
      ·
        refine ⟨13141356086177664027824521, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17521808114903552037099361 13141356086177664027824521)
        ·
          refine ⟨9856017064633248020868391, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13141356086177664027824521 9856017064633248020868391)
          ·
            refine ⟨14784025596949872031302587, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856017064633248020868391 14784025596949872031302587)
            ·
              refine ⟨22176038395424808046953881, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14784025596949872031302587 22176038395424808046953881)
              ·
                refine ⟨16632028796568606035215411, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22176038395424808046953881 16632028796568606035215411)
                ·
                  refine ⟨24948043194852909052823117, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16632028796568606035215411 24948043194852909052823117)
                  ·
                    refine ⟨9355516198069840894808669, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24948043194852909052823117 9355516198069840894808669)
                    ·
                      refine ⟨3508318574276190335553251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9355516198069840894808669 3508318574276190335553251)
                      ·
                        rfl

theorem cell23_6832426_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 4, 2, 2, 1, 1, 2, 1, 3, 3].length) (baseStart_6832426 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832426 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832426 prefixEnd_6832426 := by exact prefixLift 6832426
  have htrace : WordTrace (prefixWord ++ tailWord_6832426) baseStart_6832426 baseEnd_6832426 := by
    simpa [prefixWord, tailWord_6832426, baseEnd_6832426] using wordTrace_append hprefix tailTrace_6832426
  have hstable : (prefixWord ++ tailWord_6832426).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832426).length < 2 ^ (prefixWord ++ tailWord_6832426).sum := by decide
  have hdescent : baseEnd_6832426 < baseStart_6832426 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832426) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832430 : List Nat := [4, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3]
def baseStart_6832430 : Nat := 118140960795 + 6832430 * 2 ^ 59
def prefixEnd_6832430 : Nat := 4983230072969 + 3 ^ 40 * 6832430 * 2
def baseEnd_6832430 : Nat := 3508320628198808319903233

theorem tailTrace_6832430 : CollatzResearch.WordTrace tailWord_6832430 prefixEnd_6832430 3508320628198808319903233 := by
  unfold tailWord_6832430
  simp only [CollatzResearch.WordTrace]
  refine ⟨31149899329660058873569843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166132796424853647325705829 31149899329660058873569843)
  ·
    refine ⟨46724848994490088310354765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31149899329660058873569843 46724848994490088310354765)
    ·
      refine ⟨17521818372933783116383037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46724848994490088310354765 17521818372933783116383037)
      ·
        refine ⟨6570681889850168668643639, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17521818372933783116383037 6570681889850168668643639)
        ·
          refine ⟨9856022834775253002965459, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6570681889850168668643639 9856022834775253002965459)
          ·
            refine ⟨14784034252162879504448189, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856022834775253002965459 14784034252162879504448189)
            ·
              refine ⟨5544012844561079814168071, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14784034252162879504448189 5544012844561079814168071)
              ·
                refine ⟨8316019266841619721252107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5544012844561079814168071 8316019266841619721252107)
                ·
                  refine ⟨12474028900262429581878161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8316019266841619721252107 12474028900262429581878161)
                  ·
                    refine ⟨9355521675196822186408621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12474028900262429581878161 9355521675196822186408621)
                    ·
                      refine ⟨3508320628198808319903233, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9355521675196822186408621 3508320628198808319903233)
                      ·
                        rfl

theorem cell23_6832430_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 3, 3, 1, 1, 3, 1, 1, 2, 3].length) (baseStart_6832430 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832430 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832430 prefixEnd_6832430 := by exact prefixLift 6832430
  have htrace : WordTrace (prefixWord ++ tailWord_6832430) baseStart_6832430 baseEnd_6832430 := by
    simpa [prefixWord, tailWord_6832430, baseEnd_6832430] using wordTrace_append hprefix tailTrace_6832430
  have hstable : (prefixWord ++ tailWord_6832430).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832430).length < 2 ^ (prefixWord ++ tailWord_6832430).sum := by decide
  have hdescent : baseEnd_6832430 < baseStart_6832430 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832430) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832489 : List Nat := [1, 2, 1, 1, 1, 3, 6, 3, 5]
def baseStart_6832489 : Nat := 118140960795 + 6832489 * 2 ^ 59
def prefixEnd_6832489 : Nat := 4983230072969 + 3 ^ 40 * 6832489 * 2
def baseEnd_6832489 : Nat := 389816769284158176562829

theorem tailTrace_6832489 : CollatzResearch.WordTrace tailWord_6832489 prefixEnd_6832489 389816769284158176562829 := by
  unfold tailWord_6832489
  simp only [CollatzResearch.WordTrace]
  refine ⟨249201346544066724064956521, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166134231029377816043304347 249201346544066724064956521)
  ·
    refine ⟨186901009908050043048717391, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249201346544066724064956521 186901009908050043048717391)
    ·
      refine ⟨280351514862075064573076087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186901009908050043048717391 280351514862075064573076087)
      ·
        refine ⟨420527272293112596859614131, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280351514862075064573076087 420527272293112596859614131)
        ·
          refine ⟨630790908439668895289421197, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420527272293112596859614131 630790908439668895289421197)
          ·
            refine ⟨236546590664875835733532949, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630790908439668895289421197 236546590664875835733532949)
            ·
              refine ⟨11088121437416054800009357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236546590664875835733532949 11088121437416054800009357)
              ·
                refine ⟨4158045539031020550003509, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11088121437416054800009357 4158045539031020550003509)
                ·
                  refine ⟨389816769284158176562829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4158045539031020550003509 389816769284158176562829)
                  ·
                    rfl

theorem cell23_6832489_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 3, 6, 3, 5].length) (baseStart_6832489 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832489 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832489 prefixEnd_6832489 := by exact prefixLift 6832489
  have htrace : WordTrace (prefixWord ++ tailWord_6832489) baseStart_6832489 baseEnd_6832489 := by
    simpa [prefixWord, tailWord_6832489, baseEnd_6832489] using wordTrace_append hprefix tailTrace_6832489
  have hstable : (prefixWord ++ tailWord_6832489).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832489).length < 2 ^ (prefixWord ++ tailWord_6832489).sum := by decide
  have hdescent : baseEnd_6832489 < baseStart_6832489 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832489) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832562 : List Nat := [3, 2, 1, 1, 1, 1, 3, 3, 8]
def baseStart_6832562 : Nat := 118140960795 + 6832562 * 2 ^ 59
def prefixEnd_6832562 : Nat := 4983230072969 + 3 ^ 40 * 6832562 * 2
def baseEnd_6832562 : Nat := 389820934182800200383625

theorem tailTrace_6832562 : CollatzResearch.WordTrace tailWord_6832562 prefixEnd_6832562 389820934182800200383625 := by
  unfold tailWord_6832562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62301002268200564383090985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166136006048534838354909293 62301002268200564383090985)
  ·
    refine ⟨46725751701150423287318239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62301002268200564383090985 46725751701150423287318239)
    ·
      refine ⟨70088627551725634930977359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46725751701150423287318239 70088627551725634930977359)
      ·
        refine ⟨105132941327588452396466039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70088627551725634930977359 105132941327588452396466039)
        ·
          refine ⟨157699411991382678594699059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105132941327588452396466039 157699411991382678594699059)
          ·
            refine ⟨236549117987074017892048589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157699411991382678594699059 236549117987074017892048589)
            ·
              refine ⟨88705919245152756709518221, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236549117987074017892048589 88705919245152756709518221)
              ·
                refine ⟨33264719716932283766069333, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88705919245152756709518221 33264719716932283766069333)
                ·
                  refine ⟨389820934182800200383625, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33264719716932283766069333 389820934182800200383625)
                  ·
                    rfl

theorem cell23_6832562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 1, 1, 1, 3, 3, 8].length) (baseStart_6832562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832562 prefixEnd_6832562 := by exact prefixLift 6832562
  have htrace : WordTrace (prefixWord ++ tailWord_6832562) baseStart_6832562 baseEnd_6832562 := by
    simpa [prefixWord, tailWord_6832562, baseEnd_6832562] using wordTrace_append hprefix tailTrace_6832562
  have hstable : (prefixWord ++ tailWord_6832562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832562).length < 2 ^ (prefixWord ++ tailWord_6832562).sum := by decide
  have hdescent : baseEnd_6832562 < baseStart_6832562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832639 : List Nat := [1, 1, 2, 2, 1, 2, 6, 1, 1, 6]
def baseStart_6832639 : Nat := 118140960795 + 6832639 * 2 ^ 59
def prefixEnd_6832639 : Nat := 4983230072969 + 3 ^ 40 * 6832639 * 2
def baseEnd_6832639 : Nat := 1169475981885199334063257

theorem tailTrace_6832639 : CollatzResearch.WordTrace tailWord_6832639 prefixEnd_6832639 1169475981885199334063257 := by
  unfold tailWord_6832639
  simp only [CollatzResearch.WordTrace]
  refine ⟨249206817493523299682916971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166137878329015533121944647 249206817493523299682916971)
  ·
    refine ⟨373810226240284949524375457, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249206817493523299682916971 373810226240284949524375457)
    ·
      refine ⟨280357669680213712143281593, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373810226240284949524375457 280357669680213712143281593)
      ·
        refine ⟨210268252260160284107461195, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280357669680213712143281593 210268252260160284107461195)
        ·
          refine ⟨315402378390240426161191793, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210268252260160284107461195 315402378390240426161191793)
          ·
            refine ⟨236551783792680319620893845, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315402378390240426161191793 236551783792680319620893845)
            ·
              refine ⟨11088364865281889982229399, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 236551783792680319620893845 11088364865281889982229399)
              ·
                refine ⟨16632547297922834973344099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11088364865281889982229399 16632547297922834973344099)
                ·
                  refine ⟨24948820946884252460016149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16632547297922834973344099 24948820946884252460016149)
                  ·
                    refine ⟨1169475981885199334063257, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24948820946884252460016149 1169475981885199334063257)
                    ·
                      rfl

theorem cell23_6832639_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 2, 6, 1, 1, 6].length) (baseStart_6832639 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832639 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832639 prefixEnd_6832639 := by exact prefixLift 6832639
  have htrace : WordTrace (prefixWord ++ tailWord_6832639) baseStart_6832639 baseEnd_6832639 := by
    simpa [prefixWord, tailWord_6832639, baseEnd_6832639] using wordTrace_append hprefix tailTrace_6832639
  have hstable : (prefixWord ++ tailWord_6832639).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832639).length < 2 ^ (prefixWord ++ tailWord_6832639).sum := by decide
  have hdescent : baseEnd_6832639 < baseStart_6832639 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832639) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832659 : List Nat := [1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4]
def baseStart_6832659 : Nat := 118140960795 + 6832659 * 2 ^ 59
def prefixEnd_6832659 : Nat := 4983230072969 + 3 ^ 40 * 6832659 * 2
def baseEnd_6832659 : Nat := 3508438215268687923939679

theorem tailTrace_6832659 : CollatzResearch.WordTrace tailWord_6832659 prefixEnd_6832659 3508438215268687923939679 := by
  unfold tailWord_6832659
  simp only [CollatzResearch.WordTrace]
  refine ⟨249207546953450843098645031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166138364635633895399096687 249207546953450843098645031)
  ·
    refine ⟨373811320430176264647967547, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249207546953450843098645031 373811320430176264647967547)
    ·
      refine ⟨560716980645264396971951321, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373811320430176264647967547 560716980645264396971951321)
      ·
        refine ⟨420537735483948297728963491, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560716980645264396971951321 420537735483948297728963491)
        ·
          refine ⟨630806603225922446593445237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420537735483948297728963491 630806603225922446593445237)
          ·
            refine ⟨59138119052430229368135491, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 630806603225922446593445237 59138119052430229368135491)
            ·
              refine ⟨88707178578645344052203237, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59138119052430229368135491 88707178578645344052203237)
              ·
                refine ⟨16632595983496002009788107, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88707178578645344052203237 16632595983496002009788107)
                ·
                  refine ⟨24948893975244003014682161, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16632595983496002009788107 24948893975244003014682161)
                  ·
                    refine ⟨18711670481433002261011621, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24948893975244003014682161 18711670481433002261011621)
                    ·
                      refine ⟨3508438215268687923939679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18711670481433002261011621 3508438215268687923939679)
                      ·
                        rfl

theorem cell23_6832659_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 5, 1, 4, 1, 2, 4].length) (baseStart_6832659 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832659 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832659 prefixEnd_6832659 := by exact prefixLift 6832659
  have htrace : WordTrace (prefixWord ++ tailWord_6832659) baseStart_6832659 baseEnd_6832659 := by
    simpa [prefixWord, tailWord_6832659, baseEnd_6832659] using wordTrace_append hprefix tailTrace_6832659
  have hstable : (prefixWord ++ tailWord_6832659).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832659).length < 2 ^ (prefixWord ++ tailWord_6832659).sum := by decide
  have hdescent : baseEnd_6832659 < baseStart_6832659 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832659) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832660 : List Nat := [2, 4, 3, 1, 1, 1, 4, 1, 1, 5]
def baseStart_6832660 : Nat := 118140960795 + 6832660 * 2 ^ 59
def prefixEnd_6832660 : Nat := 4983230072969 + 3 ^ 40 * 6832660 * 2
def baseEnd_6832660 : Nat := 1169479576249780806675725

theorem tailTrace_6832660 : CollatzResearch.WordTrace tailWord_6832660 prefixEnd_6832660 1169479576249780806675725 := by
  unfold tailWord_6832660
  simp only [CollatzResearch.WordTrace]
  refine ⟨124603791713223610134715717, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166138388950964813512954289 124603791713223610134715717)
  ·
    refine ⟨23363210946229426900259197, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124603791713223610134715717 23363210946229426900259197)
    ·
      refine ⟨8761204104836035087597199, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 23363210946229426900259197 8761204104836035087597199)
      ·
        refine ⟨13141806157254052631395799, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761204104836035087597199 13141806157254052631395799)
        ·
          refine ⟨19712709235881078947093699, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141806157254052631395799 19712709235881078947093699)
          ·
            refine ⟨29569063853821618420640549, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19712709235881078947093699 29569063853821618420640549)
            ·
              refine ⟨5544199472591553453870103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29569063853821618420640549 5544199472591553453870103)
              ·
                refine ⟨8316299208887330180805155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5544199472591553453870103 8316299208887330180805155)
                ·
                  refine ⟨12474448813330995271207733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8316299208887330180805155 12474448813330995271207733)
                  ·
                    refine ⟨1169479576249780806675725, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12474448813330995271207733 1169479576249780806675725)
                    ·
                      rfl

theorem cell23_6832660_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 3, 1, 1, 1, 4, 1, 1, 5].length) (baseStart_6832660 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832660 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832660 prefixEnd_6832660 := by exact prefixLift 6832660
  have htrace : WordTrace (prefixWord ++ tailWord_6832660) baseStart_6832660 baseEnd_6832660 := by
    simpa [prefixWord, tailWord_6832660, baseEnd_6832660] using wordTrace_append hprefix tailTrace_6832660
  have hstable : (prefixWord ++ tailWord_6832660).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832660).length < 2 ^ (prefixWord ++ tailWord_6832660).sum := by decide
  have hdescent : baseEnd_6832660 < baseStart_6832660 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832660) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832669 : List Nat := [1, 4, 2, 2, 1, 3, 10]
def baseStart_6832669 : Nat := 118140960795 + 6832669 * 2 ^ 59
def prefixEnd_6832669 : Nat := 4983230072969 + 3 ^ 40 * 6832669 * 2
def baseEnd_6832669 : Nat := 43314115433027566479193

theorem tailTrace_6832669 : CollatzResearch.WordTrace tailWord_6832669 prefixEnd_6832669 43314115433027566479193 := by
  unfold tailWord_6832669
  simp only [CollatzResearch.WordTrace]
  refine ⟨249207911683414614806509061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166138607788943076537672707 249207911683414614806509061)
  ·
    refine ⟨46726483440640240276220449, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249207911683414614806509061 46726483440640240276220449)
    ·
      refine ⟨35044862580480180207165337, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46726483440640240276220449 35044862580480180207165337)
      ·
        refine ⟨26283646935360135155374003, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35044862580480180207165337 26283646935360135155374003)
        ·
          refine ⟨39425470403040202733061005, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26283646935360135155374003 39425470403040202733061005)
          ·
            refine ⟨14784551401140076024897877, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39425470403040202733061005 14784551401140076024897877)
            ·
              refine ⟨43314115433027566479193, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14784551401140076024897877 43314115433027566479193)
              ·
                rfl

theorem cell23_6832669_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 3, 10].length) (baseStart_6832669 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832669 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832669 prefixEnd_6832669 := by exact prefixLift 6832669
  have htrace : WordTrace (prefixWord ++ tailWord_6832669) baseStart_6832669 baseEnd_6832669 := by
    simpa [prefixWord, tailWord_6832669, baseEnd_6832669] using wordTrace_append hprefix tailTrace_6832669
  have hstable : (prefixWord ++ tailWord_6832669).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832669).length < 2 ^ (prefixWord ++ tailWord_6832669).sum := by decide
  have hdescent : baseEnd_6832669 < baseStart_6832669 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832669) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832680 : List Nat := [2, 1, 5, 2, 1, 1, 1, 3, 3, 2, 2]
def baseStart_6832680 : Nat := 118140960795 + 6832680 * 2 ^ 59
def prefixEnd_6832680 : Nat := 4983230072969 + 3 ^ 40 * 6832680 * 2
def baseEnd_6832680 : Nat := 3508448998362432341777083

theorem tailTrace_6832680 : CollatzResearch.WordTrace tailWord_6832680 prefixEnd_6832680 3508448998362432341777083 := by
  unfold tailWord_6832680
  simp only [CollatzResearch.WordTrace]
  refine ⟨124604156443187381842579747, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166138875257583175790106329 124604156443187381842579747)
  ·
    refine ⟨186906234664781072763869621, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124604156443187381842579747 186906234664781072763869621)
    ·
      refine ⟨17522459499823225571612777, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186906234664781072763869621 17522459499823225571612777)
      ·
        refine ⟨13141844624867419178709583, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17522459499823225571612777 13141844624867419178709583)
        ·
          refine ⟨19712766937301128768064375, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13141844624867419178709583 19712766937301128768064375)
          ·
            refine ⟨29569150405951693152096563, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19712766937301128768064375 29569150405951693152096563)
            ·
              refine ⟨44353725608927539728144845, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29569150405951693152096563 44353725608927539728144845)
              ·
                refine ⟨16632647103347827398054317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 44353725608927539728144845 16632647103347827398054317)
                ·
                  refine ⟨6237242663755435274270369, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16632647103347827398054317 6237242663755435274270369)
                  ·
                    refine ⟨4677931997816576455702777, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6237242663755435274270369 4677931997816576455702777)
                    ·
                      refine ⟨3508448998362432341777083, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4677931997816576455702777 3508448998362432341777083)
                      ·
                        rfl

theorem cell23_6832680_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 5, 2, 1, 1, 1, 3, 3, 2, 2].length) (baseStart_6832680 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832680 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832680 prefixEnd_6832680 := by exact prefixLift 6832680
  have htrace : WordTrace (prefixWord ++ tailWord_6832680) baseStart_6832680 baseEnd_6832680 := by
    simpa [prefixWord, tailWord_6832680, baseEnd_6832680] using wordTrace_append hprefix tailTrace_6832680
  have hstable : (prefixWord ++ tailWord_6832680).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832680).length < 2 ^ (prefixWord ++ tailWord_6832680).sum := by decide
  have hdescent : baseEnd_6832680 < baseStart_6832680 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832680) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832708 : List Nat := [2, 3, 5, 1, 2, 1, 1, 3, 1, 1, 3]
def baseStart_6832708 : Nat := 118140960795 + 6832708 * 2 ^ 59
def prefixEnd_6832708 : Nat := 4983230072969 + 3 ^ 40 * 6832708 * 2
def baseEnd_6832708 : Nat := 3508463375820758232226955

theorem tailTrace_6832708 : CollatzResearch.WordTrace tailWord_6832708 prefixEnd_6832708 3508463375820758232226955 := by
  unfold tailWord_6832708
  simp only [CollatzResearch.WordTrace]
  refine ⟨124604667065136662233589389, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166139556086848882978119185 124604667065136662233589389)
  ·
    refine ⟨46726750149426248337596021, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124604667065136662233589389 46726750149426248337596021)
    ·
      refine ⟨4380632826508710781649627, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 46726750149426248337596021 4380632826508710781649627)
      ·
        refine ⟨6570949239763066172474441, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4380632826508710781649627 6570949239763066172474441)
        ·
          refine ⟨4928211929822299629355831, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6570949239763066172474441 4928211929822299629355831)
          ·
            refine ⟨7392317894733449444033747, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928211929822299629355831 7392317894733449444033747)
            ·
              refine ⟨11088476842100174166050621, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392317894733449444033747 11088476842100174166050621)
              ·
                refine ⟨4158178815787565312268983, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11088476842100174166050621 4158178815787565312268983)
                ·
                  refine ⟨6237268223681347968403475, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158178815787565312268983 6237268223681347968403475)
                  ·
                    refine ⟨9355902335522021952605213, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6237268223681347968403475 9355902335522021952605213)
                    ·
                      refine ⟨3508463375820758232226955, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9355902335522021952605213 3508463375820758232226955)
                      ·
                        rfl

theorem cell23_6832708_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 5, 1, 2, 1, 1, 3, 1, 1, 3].length) (baseStart_6832708 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832708 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832708 prefixEnd_6832708 := by exact prefixLift 6832708
  have htrace : WordTrace (prefixWord ++ tailWord_6832708) baseStart_6832708 baseEnd_6832708 := by
    simpa [prefixWord, tailWord_6832708, baseEnd_6832708] using wordTrace_append hprefix tailTrace_6832708
  have hstable : (prefixWord ++ tailWord_6832708).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832708).length < 2 ^ (prefixWord ++ tailWord_6832708).sum := by decide
  have hdescent : baseEnd_6832708 < baseStart_6832708 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832708) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832709 : List Nat := [1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 5]
def baseStart_6832709 : Nat := 118140960795 + 6832709 * 2 ^ 59
def prefixEnd_6832709 : Nat := 4983230072969 + 3 ^ 40 * 6832709 * 2
def baseEnd_6832709 : Nat := 3508463889301412728314449

theorem tailTrace_6832709 : CollatzResearch.WordTrace tailWord_6832709 prefixEnd_6832709 3508463889301412728314449 := by
  unfold tailWord_6832709
  simp only [CollatzResearch.WordTrace]
  refine ⟨249209370603269701637965181, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166139580402179801091976787 249209370603269701637965181)
  ·
    refine ⟨93453513976226138114236943, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249209370603269701637965181 93453513976226138114236943)
    ·
      refine ⟨140180270964339207171355415, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93453513976226138114236943 140180270964339207171355415)
      ·
        refine ⟨210270406446508810757033123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140180270964339207171355415 210270406446508810757033123)
        ·
          refine ⟨315405609669763216135549685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210270406446508810757033123 315405609669763216135549685)
          ·
            refine ⟨29569275906540301512707783, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 315405609669763216135549685 29569275906540301512707783)
            ·
              refine ⟨44353913859810452269061675, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29569275906540301512707783 44353913859810452269061675)
              ·
                refine ⟨66530870789715678403592513, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44353913859810452269061675 66530870789715678403592513)
                ·
                  refine ⟨49898153092286758802694385, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 66530870789715678403592513 49898153092286758802694385)
                  ·
                    refine ⟨37423614819215069102020789, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 49898153092286758802694385 37423614819215069102020789)
                    ·
                      refine ⟨3508463889301412728314449, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37423614819215069102020789 3508463889301412728314449)
                      ·
                        rfl

theorem cell23_6832709_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 5, 1, 1, 2, 2, 5].length) (baseStart_6832709 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832709 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832709 prefixEnd_6832709 := by exact prefixLift 6832709
  have htrace : WordTrace (prefixWord ++ tailWord_6832709) baseStart_6832709 baseEnd_6832709 := by
    simpa [prefixWord, tailWord_6832709, baseEnd_6832709] using wordTrace_append hprefix tailTrace_6832709
  have hstable : (prefixWord ++ tailWord_6832709).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832709).length < 2 ^ (prefixWord ++ tailWord_6832709).sum := by decide
  have hdescent : baseEnd_6832709 < baseStart_6832709 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832709) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832739 : List Nat := [1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5]
def baseStart_6832739 : Nat := 118140960795 + 6832739 * 2 ^ 59
def prefixEnd_6832739 : Nat := 4983230072969 + 3 ^ 40 * 6832739 * 2
def baseEnd_6832739 : Nat := 3508479293721047610939311

theorem tailTrace_6832739 : CollatzResearch.WordTrace tailWord_6832739 prefixEnd_6832739 3508479293721047610939311 := by
  unfold tailWord_6832739
  simp only [CollatzResearch.WordTrace]
  refine ⟨249210464793161016761557271, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166140309862107344507704847 249210464793161016761557271)
  ·
    refine ⟨373815697189741525142335907, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249210464793161016761557271 373815697189741525142335907)
    ·
      refine ⟨560723545784612287713503861, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373815697189741525142335907 560723545784612287713503861)
      ·
        refine ⟨52567832417307401973140987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 560723545784612287713503861 52567832417307401973140987)
        ·
          refine ⟨78851748625961102959711481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52567832417307401973140987 78851748625961102959711481)
          ·
            refine ⟨59138811469470827219783611, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78851748625961102959711481 59138811469470827219783611)
            ·
              refine ⟨88708217204206240829675417, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59138811469470827219783611 88708217204206240829675417)
              ·
                refine ⟨66531162903154680622256563, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88708217204206240829675417 66531162903154680622256563)
                ·
                  refine ⟨99796744354732020933384845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66531162903154680622256563 99796744354732020933384845)
                  ·
                    refine ⟨37423779133024507850019317, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99796744354732020933384845 37423779133024507850019317)
                    ·
                      refine ⟨3508479293721047610939311, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37423779133024507850019317 3508479293721047610939311)
                      ·
                        rfl

theorem cell23_6832739_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 5, 1, 2, 1, 2, 1, 3, 5].length) (baseStart_6832739 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832739 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832739 prefixEnd_6832739 := by exact prefixLift 6832739
  have htrace : WordTrace (prefixWord ++ tailWord_6832739) baseStart_6832739 baseEnd_6832739 := by
    simpa [prefixWord, tailWord_6832739, baseEnd_6832739] using wordTrace_append hprefix tailTrace_6832739
  have hstable : (prefixWord ++ tailWord_6832739).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832739).length < 2 ^ (prefixWord ++ tailWord_6832739).sum := by decide
  have hdescent : baseEnd_6832739 < baseStart_6832739 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832739) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832759 : List Nat := [1, 1, 3, 1, 1, 3, 2, 4, 7]
def baseStart_6832759 : Nat := 118140960795 + 6832759 * 2 ^ 59
def prefixEnd_6832759 : Nat := 4983230072969 + 3 ^ 40 * 6832759 * 2
def baseEnd_6832759 : Nat := 389832173703793059187691

theorem tailTrace_6832759 : CollatzResearch.WordTrace tailWord_6832759 prefixEnd_6832759 389832173703793059187691 := by
  unfold tailWord_6832759
  simp only [CollatzResearch.WordTrace]
  refine ⟨249211194253088560177285331, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166140796168725706784856887 249211194253088560177285331)
  ·
    refine ⟨373816791379632840265927997, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249211194253088560177285331 373816791379632840265927997)
    ·
      refine ⟨140181296767362315099722999, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373816791379632840265927997 140181296767362315099722999)
      ·
        refine ⟨210271945151043472649584499, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140181296767362315099722999 210271945151043472649584499)
        ·
          refine ⟨315407917726565208974376749, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210271945151043472649584499 315407917726565208974376749)
          ·
            refine ⟨118277969147461953365391281, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315407917726565208974376749 118277969147461953365391281)
            ·
              refine ⟨88708476860596465024043461, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118277969147461953365391281 88708476860596465024043461)
              ·
                refine ⟨16632839411361837192008149, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88708476860596465024043461 16632839411361837192008149)
                ·
                  refine ⟨389832173703793059187691, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16632839411361837192008149 389832173703793059187691)
                  ·
                    rfl

theorem cell23_6832759_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 2, 4, 7].length) (baseStart_6832759 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832759 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832759 prefixEnd_6832759 := by exact prefixLift 6832759
  have htrace : WordTrace (prefixWord ++ tailWord_6832759) baseStart_6832759 baseEnd_6832759 := by
    simpa [prefixWord, tailWord_6832759, baseEnd_6832759] using wordTrace_append hprefix tailTrace_6832759
  have hstable : (prefixWord ++ tailWord_6832759).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832759).length < 2 ^ (prefixWord ++ tailWord_6832759).sum := by decide
  have hdescent : baseEnd_6832759 < baseStart_6832759 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832759) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832789 : List Nat := [1, 3, 2, 1, 1, 1, 1, 1, 5, 7]
def baseStart_6832789 : Nat := 118140960795 + 6832789 * 2 ^ 59
def prefixEnd_6832789 : Nat := 4983230072969 + 3 ^ 40 * 6832789 * 2
def baseEnd_6832789 : Nat := 1169501655917924138438027

theorem tailTrace_6832789 : CollatzResearch.WordTrace tailWord_6832789 prefixEnd_6832789 1169501655917924138438027 := by
  unfold tailWord_6832789
  simp only [CollatzResearch.WordTrace]
  refine ⟨249212288442979875300877421, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166141525628653250200584947 249212288442979875300877421)
  ·
    refine ⟨93454608166117453237829033, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249212288442979875300877421 93454608166117453237829033)
    ·
      refine ⟨70090956124588089928371775, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93454608166117453237829033 70090956124588089928371775)
      ·
        refine ⟨105136434186882134892557663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70090956124588089928371775 105136434186882134892557663)
        ·
          refine ⟨157704651280323202338836495, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105136434186882134892557663 157704651280323202338836495)
          ·
            refine ⟨236556976920484803508254743, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157704651280323202338836495 236556976920484803508254743)
            ·
              refine ⟨354835465380727205262382115, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236556976920484803508254743 354835465380727205262382115)
              ·
                refine ⟨532253198071090807893573173, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354835465380727205262382115 532253198071090807893573173)
                ·
                  refine ⟨49898737319164763240022485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 532253198071090807893573173 49898737319164763240022485)
                  ·
                    refine ⟨1169501655917924138438027, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 49898737319164763240022485 1169501655917924138438027)
                    ·
                      rfl

theorem cell23_6832789_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 1, 1, 1, 1, 5, 7].length) (baseStart_6832789 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832789 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832789 prefixEnd_6832789 := by exact prefixLift 6832789
  have htrace : WordTrace (prefixWord ++ tailWord_6832789) baseStart_6832789 baseEnd_6832789 := by
    simpa [prefixWord, tailWord_6832789, baseEnd_6832789] using wordTrace_append hprefix tailTrace_6832789
  have hstable : (prefixWord ++ tailWord_6832789).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832789).length < 2 ^ (prefixWord ++ tailWord_6832789).sum := by decide
  have hdescent : baseEnd_6832789 < baseStart_6832789 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832789) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832810 : List Nat := [3, 1, 5, 2, 1, 1, 1, 2, 7]
def baseStart_6832810 : Nat := 118140960795 + 6832810 * 2 ^ 59
def prefixEnd_6832810 : Nat := 4983230072969 + 3 ^ 40 * 6832810 * 2
def baseEnd_6832810 : Nat := 389835083427501870350165

theorem tailTrace_6832810 : CollatzResearch.WordTrace tailWord_6832810 prefixEnd_6832810 389835083427501870350165 := by
  unfold tailWord_6832810
  simp only [CollatzResearch.WordTrace]
  refine ⟨62303263593975948971847971, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166142036250602530591594589 62303263593975948971847971)
  ·
    refine ⟨93454895390963923457771957, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62303263593975948971847971 93454895390963923457771957)
    ·
      refine ⟨8761396442902867824166121, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 93454895390963923457771957 8761396442902867824166121)
      ·
        refine ⟨6571047332177150868124591, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 8761396442902867824166121 6571047332177150868124591)
        ·
          refine ⟨9856570998265726302186887, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571047332177150868124591 9856570998265726302186887)
          ·
            refine ⟨14784856497398589453280331, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856570998265726302186887 14784856497398589453280331)
            ·
              refine ⟨22177284746097884179920497, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14784856497398589453280331 22177284746097884179920497)
              ·
                refine ⟨16632963559573413134940373, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22177284746097884179920497 16632963559573413134940373)
                ·
                  refine ⟨389835083427501870350165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16632963559573413134940373 389835083427501870350165)
                  ·
                    rfl

theorem cell23_6832810_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 5, 2, 1, 1, 1, 2, 7].length) (baseStart_6832810 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832810 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832810 prefixEnd_6832810 := by exact prefixLift 6832810
  have htrace : WordTrace (prefixWord ++ tailWord_6832810) baseStart_6832810 baseEnd_6832810 := by
    simpa [prefixWord, tailWord_6832810, baseEnd_6832810] using wordTrace_append hprefix tailTrace_6832810
  have hstable : (prefixWord ++ tailWord_6832810).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832810).length < 2 ^ (prefixWord ++ tailWord_6832810).sum := by decide
  have hdescent : baseEnd_6832810 < baseStart_6832810 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832810) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832826 : List Nat := [3, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4]
def baseStart_6832826 : Nat := 118140960795 + 6832826 * 2 ^ 59
def prefixEnd_6832826 : Nat := 4983230072969 + 3 ^ 40 * 6832826 * 2
def baseEnd_6832826 : Nat := 3508523966537988770551411

theorem tailTrace_6832826 : CollatzResearch.WordTrace tailWord_6832826 prefixEnd_6832826 3508523966537988770551411 := by
  unfold tailWord_6832826
  simp only [CollatzResearch.WordTrace]
  refine ⟨62303409485961457654993583, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166142425295897220413316221 62303409485961457654993583)
  ·
    refine ⟨93455114228942186482490375, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62303409485961457654993583 93455114228942186482490375)
    ·
      refine ⟨140182671343413279723735563, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93455114228942186482490375 140182671343413279723735563)
      ·
        refine ⟨210274007015119919585603345, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140182671343413279723735563 210274007015119919585603345)
        ·
          refine ⟨157705505261339939689202509, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210274007015119919585603345 157705505261339939689202509)
          ·
            refine ⟨59139564473002477383450941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157705505261339939689202509 59139564473002477383450941)
            ·
              refine ⟨22177336677375929018794103, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59139564473002477383450941 22177336677375929018794103)
              ·
                refine ⟨33266005016063893528191155, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22177336677375929018794103 33266005016063893528191155)
                ·
                  refine ⟨49899007524095840292286733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33266005016063893528191155 49899007524095840292286733)
                  ·
                    refine ⟨18712127821535940109607525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49899007524095840292286733 18712127821535940109607525)
                    ·
                      refine ⟨3508523966537988770551411, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18712127821535940109607525 3508523966537988770551411)
                      ·
                        rfl

theorem cell23_6832826_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 1, 2, 3, 3, 1, 1, 3, 4].length) (baseStart_6832826 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832826 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832826 prefixEnd_6832826 := by exact prefixLift 6832826
  have htrace : WordTrace (prefixWord ++ tailWord_6832826) baseStart_6832826 baseEnd_6832826 := by
    simpa [prefixWord, tailWord_6832826, baseEnd_6832826] using wordTrace_append hprefix tailTrace_6832826
  have hstable : (prefixWord ++ tailWord_6832826).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832826).length < 2 ^ (prefixWord ++ tailWord_6832826).sum := by decide
  have hdescent : baseEnd_6832826 < baseStart_6832826 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832826) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832838 : List Nat := [6, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2]
def baseStart_6832838 : Nat := 118140960795 + 6832838 * 2 ^ 59
def prefixEnd_6832838 : Nat := 4983230072969 + 3 ^ 40 * 6832838 * 2
def baseEnd_6832838 : Nat := 3508530128305842723601357

theorem tailTrace_6832838 : CollatzResearch.WordTrace tailWord_6832838 prefixEnd_6832838 3508530128305842723601357 := by
  unfold tailWord_6832838
  simp only [CollatzResearch.WordTrace]
  refine ⟨7787939863118823645919099, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166142717079868237779607445 7787939863118823645919099)
  ·
    refine ⟨11681909794678235468878649, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 7787939863118823645919099 11681909794678235468878649)
    ·
      refine ⟨8761432346008676601658987, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 11681909794678235468878649 8761432346008676601658987)
      ·
        refine ⟨13142148519013014902488481, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761432346008676601658987 13142148519013014902488481)
        ·
          refine ⟨9856611389259761176866361, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13142148519013014902488481 9856611389259761176866361)
          ·
            refine ⟨7392458541944820882649771, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9856611389259761176866361 7392458541944820882649771)
            ·
              refine ⟨11088687812917231323974657, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392458541944820882649771 11088687812917231323974657)
              ·
                refine ⟨8316515859687923492980993, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11088687812917231323974657 8316515859687923492980993)
                ·
                  refine ⟨6237386894765942619735745, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8316515859687923492980993 6237386894765942619735745)
                  ·
                    refine ⟨4678040171074456964801809, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6237386894765942619735745 4678040171074456964801809)
                    ·
                      refine ⟨3508530128305842723601357, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678040171074456964801809 3508530128305842723601357)
                      ·
                        rfl

theorem cell23_6832838_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 1, 2, 1, 2, 2, 1, 2, 2, 2, 2].length) (baseStart_6832838 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832838 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832838 prefixEnd_6832838 := by exact prefixLift 6832838
  have htrace : WordTrace (prefixWord ++ tailWord_6832838) baseStart_6832838 baseEnd_6832838 := by
    simpa [prefixWord, tailWord_6832838, baseEnd_6832838] using wordTrace_append hprefix tailTrace_6832838
  have hstable : (prefixWord ++ tailWord_6832838).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832838).length < 2 ^ (prefixWord ++ tailWord_6832838).sum := by decide
  have hdescent : baseEnd_6832838 < baseStart_6832838 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832838) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832876 : List Nat := [2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 3]
def baseStart_6832876 : Nat := 118140960795 + 6832876 * 2 ^ 59
def prefixEnd_6832876 : Nat := 4983230072969 + 3 ^ 40 * 6832876 * 2
def baseEnd_6832876 : Nat := 3508549640570713574926181

theorem tailTrace_6832876 : CollatzResearch.WordTrace tailWord_6832876 prefixEnd_6832876 3508549640570713574926181 := by
  unfold tailWord_6832876
  simp only [CollatzResearch.WordTrace]
  refine ⟨124607730796832344579647241, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166143641062443126106196321 124607730796832344579647241)
  ·
    refine ⟨93455798097624258434735431, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124607730796832344579647241 93455798097624258434735431)
    ·
      refine ⟨140183697146436387652103147, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93455798097624258434735431 140183697146436387652103147)
      ·
        refine ⟨210275545719654581478154721, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140183697146436387652103147 210275545719654581478154721)
        ·
          refine ⟨157706659289740936108616041, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210275545719654581478154721 157706659289740936108616041)
          ·
            refine ⟨118279994467305702081462031, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157706659289740936108616041 118279994467305702081462031)
            ·
              refine ⟨177419991700958553122193047, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118279994467305702081462031 177419991700958553122193047)
              ·
                refine ⟨266129987551437829683289571, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177419991700958553122193047 266129987551437829683289571)
                ·
                  refine ⟨399194981327156744524934357, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 266129987551437829683289571 399194981327156744524934357)
                  ·
                    refine ⟨9356132374855236199803149, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 7 399194981327156744524934357 9356132374855236199803149)
                    ·
                      refine ⟨3508549640570713574926181, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9356132374855236199803149 3508549640570713574926181)
                      ·
                        rfl

theorem cell23_6832876_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 1, 7, 3].length) (baseStart_6832876 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832876 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832876 prefixEnd_6832876 := by exact prefixLift 6832876
  have htrace : WordTrace (prefixWord ++ tailWord_6832876) baseStart_6832876 baseEnd_6832876 := by
    simpa [prefixWord, tailWord_6832876, baseEnd_6832876] using wordTrace_append hprefix tailTrace_6832876
  have hstable : (prefixWord ++ tailWord_6832876).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832876).length < 2 ^ (prefixWord ++ tailWord_6832876).sum := by decide
  have hdescent : baseEnd_6832876 < baseStart_6832876 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832876) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832930 : List Nat := [3, 3, 1, 1, 2, 2, 3, 2, 1, 5]
def baseStart_6832930 : Nat := 118140960795 + 6832930 * 2 ^ 59
def prefixEnd_6832930 : Nat := 4983230072969 + 3 ^ 40 * 6832930 * 2
def baseEnd_6832930 : Nat := 1169525789508685454550311

theorem tailTrace_6832930 : CollatzResearch.WordTrace tailWord_6832930 prefixEnd_6832930 1169525789508685454550311 := by
  unfold tailWord_6832930
  simp only [CollatzResearch.WordTrace]
  refine ⟨62304357783867264095440061, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166144954090312704254506829 62304357783867264095440061)
  ·
    refine ⟨23364134168950224035790023, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 62304357783867264095440061 23364134168950224035790023)
    ·
      refine ⟨35046201253425336053685035, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23364134168950224035790023 35046201253425336053685035)
      ·
        refine ⟨52569301880138004080527553, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35046201253425336053685035 52569301880138004080527553)
        ·
          refine ⟨39426976410103503060395665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52569301880138004080527553 39426976410103503060395665)
          ·
            refine ⟨29570232307577627295296749, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39426976410103503060395665 29570232307577627295296749)
            ·
              refine ⟨11088837115341610235736281, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29570232307577627295296749 11088837115341610235736281)
              ·
                refine ⟨8316627836506207676802211, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11088837115341610235736281 8316627836506207676802211)
                ·
                  refine ⟨12474941754759311515203317, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8316627836506207676802211 12474941754759311515203317)
                  ·
                    refine ⟨1169525789508685454550311, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12474941754759311515203317 1169525789508685454550311)
                    ·
                      rfl

theorem cell23_6832930_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 3, 1, 1, 2, 2, 3, 2, 1, 5].length) (baseStart_6832930 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832930 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832930 prefixEnd_6832930 := by exact prefixLift 6832930
  have htrace : WordTrace (prefixWord ++ tailWord_6832930) baseStart_6832930 baseEnd_6832930 := by
    simpa [prefixWord, tailWord_6832930, baseEnd_6832930] using wordTrace_append hprefix tailTrace_6832930
  have hstable : (prefixWord ++ tailWord_6832930).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832930).length < 2 ^ (prefixWord ++ tailWord_6832930).sum := by decide
  have hdescent : baseEnd_6832930 < baseStart_6832930 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832930) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832933 : List Nat := [1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 4]
def baseStart_6832933 : Nat := 118140960795 + 6832933 * 2 ^ 59
def prefixEnd_6832933 : Nat := 4983230072969 + 3 ^ 40 * 6832933 * 2
def baseEnd_6832933 : Nat := 3508578908968019851913419

theorem tailTrace_6832933 : CollatzResearch.WordTrace tailWord_6832933 prefixEnd_6832933 3508578908968019851913419 := by
  unfold tailWord_6832933
  simp only [CollatzResearch.WordTrace]
  refine ⟨249217540554458187894119453, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166145027036305458596079635 249217540554458187894119453)
  ·
    refine ⟨93456577707921820460294795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249217540554458187894119453 93456577707921820460294795)
    ·
      refine ⟨140184866561882730690442193, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93456577707921820460294795 140184866561882730690442193)
      ·
        refine ⟨105138649921412048017831645, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140184866561882730690442193 105138649921412048017831645)
        ·
          refine ⟨39426993720529518006686867, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105138649921412048017831645 39426993720529518006686867)
          ·
            refine ⟨59140490580794277010030301, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39426993720529518006686867 59140490580794277010030301)
            ·
              refine ⟨22177683967797853878761363, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59140490580794277010030301 22177683967797853878761363)
              ·
                refine ⟨33266525951696780818142045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22177683967797853878761363 33266525951696780818142045)
                ·
                  refine ⟨12474947231886292806803267, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33266525951696780818142045 12474947231886292806803267)
                  ·
                    refine ⟨18712420847829439210204901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12474947231886292806803267 18712420847829439210204901)
                    ·
                      refine ⟨3508578908968019851913419, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18712420847829439210204901 3508578908968019851913419)
                      ·
                        rfl

theorem cell23_6832933_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 3, 1, 3, 1, 3, 1, 4].length) (baseStart_6832933 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832933 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832933 prefixEnd_6832933 := by exact prefixLift 6832933
  have htrace : WordTrace (prefixWord ++ tailWord_6832933) baseStart_6832933 baseEnd_6832933 := by
    simpa [prefixWord, tailWord_6832933, baseEnd_6832933] using wordTrace_append hprefix tailTrace_6832933
  have hstable : (prefixWord ++ tailWord_6832933).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832933).length < 2 ^ (prefixWord ++ tailWord_6832933).sum := by decide
  have hdescent : baseEnd_6832933 < baseStart_6832933 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832933) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832961 : List Nat := [1, 2, 5, 3, 1, 1, 1, 4, 1, 1, 3]
def baseStart_6832961 : Nat := 118140960795 + 6832961 * 2 ^ 59
def prefixEnd_6832961 : Nat := 4983230072969 + 3 ^ 40 * 6832961 * 2
def baseEnd_6832961 : Nat := 3508593286426345742363291

theorem tailTrace_6832961 : CollatzResearch.WordTrace tailWord_6832961 prefixEnd_6832961 3508593286426345742363291 := by
  unfold tailWord_6832961
  simp only [CollatzResearch.WordTrace]
  refine ⟨249218561798356748676138737, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166145707865571165784092491 249218561798356748676138737)
  ·
    refine ⟨186913921348767561507104053, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249218561798356748676138737 186913921348767561507104053)
    ·
      refine ⟨17523180126446958891291005, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186913921348767561507104053 17523180126446958891291005)
      ·
        refine ⟨6571192547417609584234127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17523180126446958891291005 6571192547417609584234127)
        ·
          refine ⟨9856788821126414376351191, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571192547417609584234127 9856788821126414376351191)
          ·
            refine ⟨14785183231689621564526787, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9856788821126414376351191 14785183231689621564526787)
            ·
              refine ⟨22177774847534432346790181, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14785183231689621564526787 22177774847534432346790181)
              ·
                refine ⟨4158332783912706065023159, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22177774847534432346790181 4158332783912706065023159)
                ·
                  refine ⟨6237499175869059097534739, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158332783912706065023159 6237499175869059097534739)
                  ·
                    refine ⟨9356248763803588646302109, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6237499175869059097534739 9356248763803588646302109)
                    ·
                      refine ⟨3508593286426345742363291, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9356248763803588646302109 3508593286426345742363291)
                      ·
                        rfl

theorem cell23_6832961_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 3, 1, 1, 1, 4, 1, 1, 3].length) (baseStart_6832961 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832961 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832961 prefixEnd_6832961 := by exact prefixLift 6832961
  have htrace : WordTrace (prefixWord ++ tailWord_6832961) baseStart_6832961 baseEnd_6832961 := by
    simpa [prefixWord, tailWord_6832961, baseEnd_6832961] using wordTrace_append hprefix tailTrace_6832961
  have hstable : (prefixWord ++ tailWord_6832961).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832961).length < 2 ^ (prefixWord ++ tailWord_6832961).sum := by decide
  have hdescent : baseEnd_6832961 < baseStart_6832961 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832961) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6832976 : List Nat := [2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6]
def baseStart_6832976 : Nat := 118140960795 + 6832976 * 2 ^ 59
def prefixEnd_6832976 : Nat := 4983230072969 + 3 ^ 40 * 6832976 * 2
def baseEnd_6832976 : Nat := 3508600988636163183675721

theorem tailTrace_6832976 : CollatzResearch.WordTrace tailWord_6832976 prefixEnd_6832976 3508600988636163183675721 := by
  unfold tailWord_6832976
  simp only [CollatzResearch.WordTrace]
  refine ⟨124609554446651203118967391, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166146072595534937491956521 124609554446651203118967391)
  ·
    refine ⟨186914331669976804678451087, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124609554446651203118967391 186914331669976804678451087)
    ·
      refine ⟨280371497504965207017676631, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186914331669976804678451087 280371497504965207017676631)
      ·
        refine ⟨420557246257447810526514947, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280371497504965207017676631 420557246257447810526514947)
        ·
          refine ⟨630835869386171715789772421, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420557246257447810526514947 630835869386171715789772421)
          ·
            refine ⟨118281725509907196710582329, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 630835869386171715789772421 118281725509907196710582329)
            ·
              refine ⟨88711294132430397532936747, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118281725509907196710582329 88711294132430397532936747)
              ·
                refine ⟨133066941198645596299405121, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88711294132430397532936747 133066941198645596299405121)
                ·
                  refine ⟨99800205898984197224553841, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133066941198645596299405121 99800205898984197224553841)
                  ·
                    refine ⟨74850154424238147918415381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 99800205898984197224553841 74850154424238147918415381)
                    ·
                      refine ⟨3508600988636163183675721, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74850154424238147918415381 3508600988636163183675721)
                      ·
                        rfl

theorem cell23_6832976_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 4, 2, 1, 2, 2, 6].length) (baseStart_6832976 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6832976 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6832976 prefixEnd_6832976 := by exact prefixLift 6832976
  have htrace : WordTrace (prefixWord ++ tailWord_6832976) baseStart_6832976 baseEnd_6832976 := by
    simpa [prefixWord, tailWord_6832976, baseEnd_6832976] using wordTrace_append hprefix tailTrace_6832976
  have hstable : (prefixWord ++ tailWord_6832976).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6832976).length < 2 ^ (prefixWord ++ tailWord_6832976).sum := by decide
  have hdescent : baseEnd_6832976 < baseStart_6832976 := by decide
  rcases family_descends (prefixWord ++ tailWord_6832976) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833000 : List Nat := [2, 1, 4, 2, 1, 2, 2, 2, 1, 3, 3]
def baseStart_6833000 : Nat := 118140960795 + 6833000 * 2 ^ 59
def prefixEnd_6833000 : Nat := 4983230072969 + 3 ^ 40 * 6833000 * 2
def baseEnd_6833000 : Nat := 3508613312171871089775611

theorem tailTrace_6833000 : CollatzResearch.WordTrace tailWord_6833000 prefixEnd_6833000 3508613312171871089775611 := by
  unfold tailWord_6833000
  simp only [CollatzResearch.WordTrace]
  refine ⟨124609992122607729168404227, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166146656163476972224538969 124609992122607729168404227)
  ·
    refine ⟨186914988183911593752606341, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124609992122607729168404227 186914988183911593752606341)
    ·
      refine ⟨35046560284483423828613689, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186914988183911593752606341 35046560284483423828613689)
      ·
        refine ⟨26284920213362567871460267, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35046560284483423828613689 26284920213362567871460267)
        ·
          refine ⟨39427380320043851807190401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26284920213362567871460267 39427380320043851807190401)
          ·
            refine ⟨29570535240032888855392801, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39427380320043851807190401 29570535240032888855392801)
            ·
              refine ⟨22177901430024666641544601, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29570535240032888855392801 22177901430024666641544601)
              ·
                refine ⟨16633426072518499981158451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22177901430024666641544601 16633426072518499981158451)
                ·
                  refine ⟨24950139108777749971737677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16633426072518499981158451 24950139108777749971737677)
                  ·
                    refine ⟨9356302165791656239401629, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24950139108777749971737677 9356302165791656239401629)
                    ·
                      refine ⟨3508613312171871089775611, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9356302165791656239401629 3508613312171871089775611)
                      ·
                        rfl

theorem cell23_6833000_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 4, 2, 1, 2, 2, 2, 1, 3, 3].length) (baseStart_6833000 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833000 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833000 prefixEnd_6833000 := by exact prefixLift 6833000
  have htrace : WordTrace (prefixWord ++ tailWord_6833000) baseStart_6833000 baseEnd_6833000 := by
    simpa [prefixWord, tailWord_6833000, baseEnd_6833000] using wordTrace_append hprefix tailTrace_6833000
  have hstable : (prefixWord ++ tailWord_6833000).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833000).length < 2 ^ (prefixWord ++ tailWord_6833000).sum := by decide
  have hdescent : baseEnd_6833000 < baseStart_6833000 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833000) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833017 : List Nat := [1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 3]
def baseStart_6833017 : Nat := 118140960795 + 6833017 * 2 ^ 59
def prefixEnd_6833017 : Nat := 4983230072969 + 3 ^ 40 * 6833017 * 2
def baseEnd_6833017 : Nat := 3508622041342997523263033

theorem tailTrace_6833017 : CollatzResearch.WordTrace tailWord_6833017 prefixEnd_6833017 3508622041342997523263033 := by
  unfold tailWord_6833017
  simp only [CollatzResearch.WordTrace]
  refine ⟨249220604286153870240177305, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166147069524102580160118203 249220604286153870240177305)
  ·
    refine ⟨186915453214615402680132979, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249220604286153870240177305 186915453214615402680132979)
    ·
      refine ⟨280373179821923104020199469, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186915453214615402680132979 280373179821923104020199469)
      ·
        refine ⟨105139942433221164007574801, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280373179821923104020199469 105139942433221164007574801)
        ·
          refine ⟨78854956824915873005681101, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105139942433221164007574801 78854956824915873005681101)
          ·
            refine ⟨29570608809343452377130413, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78854956824915873005681101 29570608809343452377130413)
            ·
              refine ⟨11088978303503794641423905, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29570608809343452377130413 11088978303503794641423905)
              ·
                refine ⟨8316733727627845981067929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11088978303503794641423905 8316733727627845981067929)
                ·
                  refine ⟨6237550295720884485800947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8316733727627845981067929 6237550295720884485800947)
                  ·
                    refine ⟨9356325443581326728701421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6237550295720884485800947 9356325443581326728701421)
                    ·
                      refine ⟨3508622041342997523263033, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9356325443581326728701421 3508622041342997523263033)
                      ·
                        rfl

theorem cell23_6833017_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 3, 2, 3, 3, 2, 2, 1, 3].length) (baseStart_6833017 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833017 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833017 prefixEnd_6833017 := by exact prefixLift 6833017
  have htrace : WordTrace (prefixWord ++ tailWord_6833017) baseStart_6833017 baseEnd_6833017 := by
    simpa [prefixWord, tailWord_6833017, baseEnd_6833017] using wordTrace_append hprefix tailTrace_6833017
  have hstable : (prefixWord ++ tailWord_6833017).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833017).length < 2 ^ (prefixWord ++ tailWord_6833017).sum := by decide
  have hdescent : baseEnd_6833017 < baseStart_6833017 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833017) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833033 : List Nat := [1, 2, 1, 1, 5, 2, 2, 1, 2, 6]
def baseStart_6833033 : Nat := 118140960795 + 6833033 * 2 ^ 59
def prefixEnd_6833033 : Nat := 4983230072969 + 3 ^ 40 * 6833033 * 2
def baseEnd_6833033 : Nat := 1169543419011156486887653

theorem tailTrace_6833033 : CollatzResearch.WordTrace tailWord_6833033 prefixEnd_6833033 1169543419011156486887653 := by
  unfold tailWord_6833033
  simp only [CollatzResearch.WordTrace]
  refine ⟨249221187854095904972759753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166147458569397269981839835 249221187854095904972759753)
  ·
    refine ⟨186915890890571928729569815, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249221187854095904972759753 186915890890571928729569815)
    ·
      refine ⟨280373836335857893094354723, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186915890890571928729569815 280373836335857893094354723)
      ·
        refine ⟨420560754503786839641532085, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280373836335857893094354723 420560754503786839641532085)
        ·
          refine ⟨39427570734730016216393633, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 420560754503786839641532085 39427570734730016216393633)
          ·
            refine ⟨29570678051047512162295225, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39427570734730016216393633 29570678051047512162295225)
            ·
              refine ⟨22178008538285634121721419, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29570678051047512162295225 22178008538285634121721419)
              ·
                refine ⟨33267012807428451182582129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22178008538285634121721419 33267012807428451182582129)
                ·
                  refine ⟨24950259605571338386936597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33267012807428451182582129 24950259605571338386936597)
                  ·
                    refine ⟨1169543419011156486887653, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24950259605571338386936597 1169543419011156486887653)
                    ·
                      rfl

theorem cell23_6833033_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 5, 2, 2, 1, 2, 6].length) (baseStart_6833033 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833033 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833033 prefixEnd_6833033 := by exact prefixLift 6833033
  have htrace : WordTrace (prefixWord ++ tailWord_6833033) baseStart_6833033 baseEnd_6833033 := by
    simpa [prefixWord, tailWord_6833033, baseEnd_6833033] using wordTrace_append hprefix tailTrace_6833033
  have hstable : (prefixWord ++ tailWord_6833033).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833033).length < 2 ^ (prefixWord ++ tailWord_6833033).sum := by decide
  have hdescent : baseEnd_6833033 < baseStart_6833033 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833033) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833044 : List Nat := [2, 4, 2, 1, 1, 1, 4, 2, 1, 3, 2]
def baseStart_6833044 : Nat := 118140960795 + 6833044 * 2 ^ 59
def prefixEnd_6833044 : Nat := 4983230072969 + 3 ^ 40 * 6833044 * 2
def baseEnd_6833044 : Nat := 3508635905320668917625409

theorem tailTrace_6833044 : CollatzResearch.WordTrace tailWord_6833044 prefixEnd_6833044 3508635905320668917625409 := by
  unfold tailWord_6833044
  simp only [CollatzResearch.WordTrace]
  refine ⟨124610794528528026925705093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166147726038037369234273457 124610794528528026925705093)
  ·
    refine ⟨23364523974099005048569705, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124610794528528026925705093 23364523974099005048569705)
    ·
      refine ⟨17523392980574253786427279, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23364523974099005048569705 17523392980574253786427279)
      ·
        refine ⟨26285089470861380679640919, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17523392980574253786427279 26285089470861380679640919)
        ·
          refine ⟨39427634206292071019461379, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26285089470861380679640919 39427634206292071019461379)
          ·
            refine ⟨59141451309438106529192069, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39427634206292071019461379 59141451309438106529192069)
            ·
              refine ⟨11089022120519644974223513, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59141451309438106529192069 11089022120519644974223513)
              ·
                refine ⟨8316766590389733730667635, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11089022120519644974223513 8316766590389733730667635)
                ·
                  refine ⟨12475149885584600596001453, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8316766590389733730667635 12475149885584600596001453)
                  ·
                    refine ⟨4678181207094225223500545, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12475149885584600596001453 4678181207094225223500545)
                    ·
                      refine ⟨3508635905320668917625409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678181207094225223500545 3508635905320668917625409)
                      ·
                        rfl

theorem cell23_6833044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 2, 1, 1, 1, 4, 2, 1, 3, 2].length) (baseStart_6833044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833044 prefixEnd_6833044 := by exact prefixLift 6833044
  have htrace : WordTrace (prefixWord ++ tailWord_6833044) baseStart_6833044 baseEnd_6833044 := by
    simpa [prefixWord, tailWord_6833044, baseEnd_6833044] using wordTrace_append hprefix tailTrace_6833044
  have hstable : (prefixWord ++ tailWord_6833044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833044).length < 2 ^ (prefixWord ++ tailWord_6833044).sum := by decide
  have hdescent : baseEnd_6833044 < baseStart_6833044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833080 : List Nat := [2, 1, 2, 1, 2, 6, 1, 1, 7]
def baseStart_6833080 : Nat := 118140960795 + 6833080 * 2 ^ 59
def prefixEnd_6833080 : Nat := 4983230072969 + 3 ^ 40 * 6833080 * 2
def baseEnd_6833080 : Nat := 389850487847136752975027

theorem tailTrace_6833080 : CollatzResearch.WordTrace tailWord_6833080 prefixEnd_6833080 389850487847136752975027 := by
  unfold tailWord_6833080
  simp only [CollatzResearch.WordTrace]
  refine ⟨124611451042462815999860347, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166148601389950421333147129 124611451042462815999860347)
  ·
    refine ⟨186917176563694223999790521, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124611451042462815999860347 186917176563694223999790521)
    ·
      refine ⟨140187882422770667999842891, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186917176563694223999790521 140187882422770667999842891)
      ·
        refine ⟨210281823634156001999764337, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140187882422770667999842891 210281823634156001999764337)
        ·
          refine ⟨157711367725617001499823253, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210281823634156001999764337 157711367725617001499823253)
          ·
            refine ⟨7392720362138296945304215, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 6 157711367725617001499823253 7392720362138296945304215)
            ·
              refine ⟨11089080543207445417956323, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392720362138296945304215 11089080543207445417956323)
              ·
                refine ⟨16633620814811168126934485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11089080543207445417956323 16633620814811168126934485)
                ·
                  refine ⟨389850487847136752975027, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16633620814811168126934485 389850487847136752975027)
                  ·
                    rfl

theorem cell23_6833080_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 1, 2, 6, 1, 1, 7].length) (baseStart_6833080 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833080 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833080 prefixEnd_6833080 := by exact prefixLift 6833080
  have htrace : WordTrace (prefixWord ++ tailWord_6833080) baseStart_6833080 baseEnd_6833080 := by
    simpa [prefixWord, tailWord_6833080, baseEnd_6833080] using wordTrace_append hprefix tailTrace_6833080
  have hstable : (prefixWord ++ tailWord_6833080).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833080).length < 2 ^ (prefixWord ++ tailWord_6833080).sum := by decide
  have hdescent : baseEnd_6833080 < baseStart_6833080 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833080) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833187 : List Nat := [1, 1, 1, 4, 3, 4, 1, 2, 6]
def baseStart_6833187 : Nat := 118140960795 + 6833187 * 2 ^ 59
def prefixEnd_6833187 : Nat := 4983230072969 + 3 ^ 40 * 6833187 * 2
def baseEnd_6833187 : Nat := 389856592561584650904139

theorem tailTrace_6833187 : CollatzResearch.WordTrace tailWord_6833187 prefixEnd_6833187 389856592561584650904139 := by
  unfold tailWord_6833187
  simp only [CollatzResearch.WordTrace]
  refine ⟨249226804695537989273865815, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166151203130358659515910543 249226804695537989273865815)
  ·
    refine ⟨373840207043306983910798723, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249226804695537989273865815 373840207043306983910798723)
    ·
      refine ⟨560760310564960475866198085, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373840207043306983910798723 560760310564960475866198085)
      ·
        refine ⟨105142558230930089224912141, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 560760310564960475866198085 105142558230930089224912141)
        ·
          refine ⟨39428459336598783459342053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105142558230930089224912141 39428459336598783459342053)
          ·
            refine ⟨7392836125612271898626635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39428459336598783459342053 7392836125612271898626635)
            ·
              refine ⟨11089254188418407847939953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7392836125612271898626635 11089254188418407847939953)
              ·
                refine ⟨8316940641313805885954965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11089254188418407847939953 8316940641313805885954965)
                ·
                  refine ⟨389856592561584650904139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8316940641313805885954965 389856592561584650904139)
                  ·
                    rfl

theorem cell23_6833187_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 3, 4, 1, 2, 6].length) (baseStart_6833187 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833187 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833187 prefixEnd_6833187 := by exact prefixLift 6833187
  have htrace : WordTrace (prefixWord ++ tailWord_6833187) baseStart_6833187 baseEnd_6833187 := by
    simpa [prefixWord, tailWord_6833187, baseEnd_6833187] using wordTrace_append hprefix tailTrace_6833187
  have hstable : (prefixWord ++ tailWord_6833187).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833187).length < 2 ^ (prefixWord ++ tailWord_6833187).sum := by decide
  have hdescent : baseEnd_6833187 < baseStart_6833187 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833187) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833191 : List Nat := [1, 1, 7, 1, 1, 1, 2, 4, 1, 4]
def baseStart_6833191 : Nat := 118140960795 + 6833191 * 2 ^ 59
def prefixEnd_6833191 : Nat := 4983230072969 + 3 ^ 40 * 6833191 * 2
def baseEnd_6833191 : Nat := 1169570462325626614162411

theorem tailTrace_6833191 : CollatzResearch.WordTrace tailWord_6833191 prefixEnd_6833191 1169570462325626614162411 := by
  unfold tailWord_6833191
  simp only [CollatzResearch.WordTrace]
  refine ⟨249226950587523497957011427, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166151300391682331971340951 249226950587523497957011427)
  ·
    refine ⟨373840425881285246935517141, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249226950587523497957011427 373840425881285246935517141)
    ·
      refine ⟨8761884981592622975051183, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 7 373840425881285246935517141 8761884981592622975051183)
      ·
        refine ⟨13142827472388934462576775, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8761884981592622975051183 13142827472388934462576775)
        ·
          refine ⟨19714241208583401693865163, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13142827472388934462576775 19714241208583401693865163)
          ·
            refine ⟨29571361812875102540797745, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19714241208583401693865163 29571361812875102540797745)
            ·
              refine ⟨22178521359656326905598309, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29571361812875102540797745 22178521359656326905598309)
              ·
                refine ⟨4158472754935561294799683, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22178521359656326905598309 4158472754935561294799683)
                ·
                  refine ⟨6237709132403341942199525, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4158472754935561294799683 6237709132403341942199525)
                  ·
                    refine ⟨1169570462325626614162411, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6237709132403341942199525 1169570462325626614162411)
                    ·
                      rfl

theorem cell23_6833191_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 7, 1, 1, 1, 2, 4, 1, 4].length) (baseStart_6833191 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833191 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833191 prefixEnd_6833191 := by exact prefixLift 6833191
  have htrace : WordTrace (prefixWord ++ tailWord_6833191) baseStart_6833191 baseEnd_6833191 := by
    simpa [prefixWord, tailWord_6833191, baseEnd_6833191] using wordTrace_append hprefix tailTrace_6833191
  have hstable : (prefixWord ++ tailWord_6833191).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833191).length < 2 ^ (prefixWord ++ tailWord_6833191).sum := by decide
  have hdescent : baseEnd_6833191 < baseStart_6833191 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833191) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833230 : List Nat := [4, 1, 1, 1, 1, 3, 2, 1, 3, 6]
def baseStart_6833230 : Nat := 118140960795 + 6833230 * 2 ^ 59
def prefixEnd_6833230 : Nat := 4983230072969 + 3 ^ 40 * 6833230 * 2
def baseEnd_6833230 : Nat := 1169577137574135063299851

theorem tailTrace_6833230 : CollatzResearch.WordTrace tailWord_6833230 prefixEnd_6833230 1169577137574135063299851 := by
  unfold tailWord_6833230
  simp only [CollatzResearch.WordTrace]
  refine ⟨31153546629297775952210143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166152248689588138411787429 31153546629297775952210143)
  ·
    refine ⟨46730319943946663928315215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31153546629297775952210143 46730319943946663928315215)
    ·
      refine ⟨70095479915919995892472823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46730319943946663928315215 70095479915919995892472823)
      ·
        refine ⟨105143219873879993838709235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70095479915919995892472823 105143219873879993838709235)
        ·
          refine ⟨157714829810819990758063853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105143219873879993838709235 157714829810819990758063853)
          ·
            refine ⟨59143061179057496534273945, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157714829810819990758063853 59143061179057496534273945)
            ·
              refine ⟨44357295884293122400705459, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59143061179057496534273945 44357295884293122400705459)
              ·
                refine ⟨66535943826439683601058189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44357295884293122400705459 66535943826439683601058189)
                ·
                  refine ⟨24950978934914881350396821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66535943826439683601058189 24950978934914881350396821)
                  ·
                    refine ⟨1169577137574135063299851, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24950978934914881350396821 1169577137574135063299851)
                    ·
                      rfl

theorem cell23_6833230_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 1, 1, 3, 2, 1, 3, 6].length) (baseStart_6833230 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833230 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833230 prefixEnd_6833230 := by exact prefixLift 6833230
  have htrace : WordTrace (prefixWord ++ tailWord_6833230) baseStart_6833230 baseEnd_6833230 := by
    simpa [prefixWord, tailWord_6833230, baseEnd_6833230] using wordTrace_append hprefix tailTrace_6833230
  have hstable : (prefixWord ++ tailWord_6833230).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833230).length < 2 ^ (prefixWord ++ tailWord_6833230).sum := by decide
  have hdescent : baseEnd_6833230 < baseStart_6833230 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833230) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833237 : List Nat := [1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 4]
def baseStart_6833237 : Nat := 118140960795 + 6833237 * 2 ^ 59
def prefixEnd_6833237 : Nat := 4983230072969 + 3 ^ 40 * 6833237 * 2
def baseEnd_6833237 : Nat := 3508735007086986662512021

theorem tailTrace_6833237 : CollatzResearch.WordTrace tailWord_6833237 prefixEnd_6833237 3508735007086986662512021 := by
  unfold tailWord_6833237
  simp only [CollatzResearch.WordTrace]
  refine ⟨249228628345356847813185965, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166152418896904565208790643 249228628345356847813185965)
  ·
    refine ⟨93460735629508817929944737, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249228628345356847813185965 93460735629508817929944737)
    ·
      refine ⟨70095551722131613447458553, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93460735629508817929944737 70095551722131613447458553)
      ·
        refine ⟨52571663791598710085593915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70095551722131613447458553 52571663791598710085593915)
        ·
          refine ⟨78857495687398065128390873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52571663791598710085593915 78857495687398065128390873)
          ·
            refine ⟨59143121765548548846293155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78857495687398065128390873 59143121765548548846293155)
            ·
              refine ⟨88714682648322823269439733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59143121765548548846293155 88714682648322823269439733)
              ·
                refine ⟨8317001498280264681509975, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88714682648322823269439733 8317001498280264681509975)
                ·
                  refine ⟨12475502247420397022264963, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317001498280264681509975 12475502247420397022264963)
                  ·
                    refine ⟨18713253371130595533397445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12475502247420397022264963 18713253371130595533397445)
                    ·
                      refine ⟨3508735007086986662512021, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18713253371130595533397445 3508735007086986662512021)
                      ·
                        rfl

theorem cell23_6833237_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 2, 1, 5, 1, 1, 4].length) (baseStart_6833237 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833237 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833237 prefixEnd_6833237 := by exact prefixLift 6833237
  have htrace : WordTrace (prefixWord ++ tailWord_6833237) baseStart_6833237 baseEnd_6833237 := by
    simpa [prefixWord, tailWord_6833237, baseEnd_6833237] using wordTrace_append hprefix tailTrace_6833237
  have hstable : (prefixWord ++ tailWord_6833237).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833237).length < 2 ^ (prefixWord ++ tailWord_6833237).sum := by decide
  have hdescent : baseEnd_6833237 < baseStart_6833237 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833237) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833247 : List Nat := [1, 1, 2, 3, 1, 1, 4, 4, 2, 4]
def baseStart_6833247 : Nat := 118140960795 + 6833247 * 2 ^ 59
def prefixEnd_6833247 : Nat := 4983230072969 + 3 ^ 40 * 6833247 * 2
def baseEnd_6833247 : Nat := 1169580047297843874462325

theorem tailTrace_6833247 : CollatzResearch.WordTrace tailWord_6833247 prefixEnd_6833247 1169580047297843874462325 := by
  unfold tailWord_6833247
  simp only [CollatzResearch.WordTrace]
  refine ⟨249228993075320619521049995, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166152662050213746347366663 249228993075320619521049995)
  ·
    refine ⟨373843489612980929281574993, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249228993075320619521049995 373843489612980929281574993)
    ·
      refine ⟨280382617209735696961181245, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373843489612980929281574993 280382617209735696961181245)
      ·
        refine ⟨105143481453650886360442967, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280382617209735696961181245 105143481453650886360442967)
        ·
          refine ⟨157715222180476329540664451, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105143481453650886360442967 157715222180476329540664451)
          ·
            refine ⟨236572833270714494310996677, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157715222180476329540664451 236572833270714494310996677)
            ·
              refine ⟨44357406238258967683311877, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 236572833270714494310996677 44357406238258967683311877)
              ·
                refine ⟨8317013669673556440620977, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44357406238258967683311877 8317013669673556440620977)
                ·
                  refine ⟨6237760252255167330465733, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8317013669673556440620977 6237760252255167330465733)
                  ·
                    refine ⟨1169580047297843874462325, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6237760252255167330465733 1169580047297843874462325)
                    ·
                      rfl

theorem cell23_6833247_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 3, 1, 1, 4, 4, 2, 4].length) (baseStart_6833247 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833247 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833247 prefixEnd_6833247 := by exact prefixLift 6833247
  have htrace : WordTrace (prefixWord ++ tailWord_6833247) baseStart_6833247 baseEnd_6833247 := by
    simpa [prefixWord, tailWord_6833247, baseEnd_6833247] using wordTrace_append hprefix tailTrace_6833247
  have hstable : (prefixWord ++ tailWord_6833247).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833247).length < 2 ^ (prefixWord ++ tailWord_6833247).sum := by decide
  have hdescent : baseEnd_6833247 < baseStart_6833247 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833247) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833260 : List Nat := [2, 2, 1, 1, 3, 2, 4, 8]
def baseStart_6833260 : Nat := 118140960795 + 6833260 * 2 ^ 59
def prefixEnd_6833260 : Nat := 4983230072969 + 3 ^ 40 * 6833260 * 2
def baseEnd_6833260 : Nat := 129953585820075558241645

theorem tailTrace_6833260 : CollatzResearch.WordTrace tailWord_6833260 prefixEnd_6833260 129953585820075558241645 := by
  unfold tailWord_6833260
  simp only [CollatzResearch.WordTrace]
  refine ⟨124614733612136761370636617, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166152978149515681827515489 124614733612136761370636617)
  ·
    refine ⟨93461050209102571027977463, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124614733612136761370636617 93461050209102571027977463)
    ·
      refine ⟨140191575313653856541966195, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93461050209102571027977463 140191575313653856541966195)
      ·
        refine ⟨210287362970480784812949293, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140191575313653856541966195 210287362970480784812949293)
        ·
          refine ⟨78857761113930294304855985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210287362970480784812949293 78857761113930294304855985)
          ·
            refine ⟨59143320835447720728641989, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78857761113930294304855985 59143320835447720728641989)
            ·
              refine ⟨11089372656646447636620373, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59143320835447720728641989 11089372656646447636620373)
              ·
                refine ⟨129953585820075558241645, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 8 11089372656646447636620373 129953585820075558241645)
                ·
                  rfl

theorem cell23_6833260_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 1, 3, 2, 4, 8].length) (baseStart_6833260 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833260 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833260 prefixEnd_6833260 := by exact prefixLift 6833260
  have htrace : WordTrace (prefixWord ++ tailWord_6833260) baseStart_6833260 baseEnd_6833260 := by
    simpa [prefixWord, tailWord_6833260, baseEnd_6833260] using wordTrace_append hprefix tailTrace_6833260
  have hstable : (prefixWord ++ tailWord_6833260).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833260).length < 2 ^ (prefixWord ++ tailWord_6833260).sum := by decide
  have hdescent : baseEnd_6833260 < baseStart_6833260 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833260) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833348 : List Nat := [2, 3, 3, 1, 3, 1, 1, 3, 1, 3, 2]
def baseStart_6833348 : Nat := 118140960795 + 6833348 * 2 ^ 59
def prefixEnd_6833348 : Nat := 4983230072969 + 3 ^ 40 * 6833348 * 2
def baseEnd_6833348 : Nat := 3508792003439635728224011

theorem tailTrace_6833348 : CollatzResearch.WordTrace tailWord_6833348 prefixEnd_6833348 3508792003439635728224011 := by
  unfold tailWord_6833348
  simp only [CollatzResearch.WordTrace]
  refine ⟨124616338423977356885238349, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166155117898636475846984465 124616338423977356885238349)
  ·
    refine ⟨46731126908991508831964381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124616338423977356885238349 46731126908991508831964381)
    ·
      refine ⟨17524172590871815811986643, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46731126908991508831964381 17524172590871815811986643)
      ·
        refine ⟨26286258886307723717979965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17524172590871815811986643 26286258886307723717979965)
        ·
          refine ⟨9857347082365396394242487, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26286258886307723717979965 9857347082365396394242487)
          ·
            refine ⟨14786020623548094591363731, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857347082365396394242487 14786020623548094591363731)
            ·
              refine ⟨22179030935322141887045597, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14786020623548094591363731 22179030935322141887045597)
              ·
                refine ⟨8317136600745803207642099, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22179030935322141887045597 8317136600745803207642099)
                ·
                  refine ⟨12475704901118704811463149, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317136600745803207642099 12475704901118704811463149)
                  ·
                    refine ⟨4678389337919514304298681, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12475704901118704811463149 4678389337919514304298681)
                    ·
                      refine ⟨3508792003439635728224011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678389337919514304298681 3508792003439635728224011)
                      ·
                        rfl

theorem cell23_6833348_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 3, 1, 3, 1, 1, 3, 1, 3, 2].length) (baseStart_6833348 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833348 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833348 prefixEnd_6833348 := by exact prefixLift 6833348
  have htrace : WordTrace (prefixWord ++ tailWord_6833348) baseStart_6833348 baseEnd_6833348 := by
    simpa [prefixWord, tailWord_6833348, baseEnd_6833348] using wordTrace_append hprefix tailTrace_6833348
  have hstable : (prefixWord ++ tailWord_6833348).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833348).length < 2 ^ (prefixWord ++ tailWord_6833348).sum := by decide
  have hdescent : baseEnd_6833348 < baseStart_6833348 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833348) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833444 : List Nat := [2, 3, 1, 3, 1, 1, 2, 1, 5, 4]
def baseStart_6833444 : Nat := 118140960795 + 6833444 * 2 ^ 59
def prefixEnd_6833444 : Nat := 4983230072969 + 3 ^ 40 * 6833444 * 2
def baseEnd_6833444 : Nat := 1169613765860822450874523

theorem tailTrace_6833444 : CollatzResearch.WordTrace tailWord_6833444 prefixEnd_6833444 1169613765860822450874523 := by
  unfold tailWord_6833444
  simp only [CollatzResearch.WordTrace]
  refine ⟨124618089127803461082985693, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166157452170404614777314257 124618089127803461082985693)
  ·
    refine ⟨46731783422926297906119635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124618089127803461082985693 46731783422926297906119635)
    ·
      refine ⟨70097675134389446859179453, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46731783422926297906119635 70097675134389446859179453)
      ·
        refine ⟨26286628175396042572192295, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70097675134389446859179453 26286628175396042572192295)
        ·
          refine ⟨39429942263094063858288443, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26286628175396042572192295 39429942263094063858288443)
          ·
            refine ⟨59144913394641095787432665, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39429942263094063858288443 59144913394641095787432665)
            ·
              refine ⟨44358685045980821840574499, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59144913394641095787432665 44358685045980821840574499)
              ·
                refine ⟨66538027568971232760861749, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44358685045980821840574499 66538027568971232760861749)
                ·
                  refine ⟨6237940084591053071330789, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66538027568971232760861749 6237940084591053071330789)
                  ·
                    refine ⟨1169613765860822450874523, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6237940084591053071330789 1169613765860822450874523)
                    ·
                      rfl

theorem cell23_6833444_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 3, 1, 1, 2, 1, 5, 4].length) (baseStart_6833444 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833444 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833444 prefixEnd_6833444 := by exact prefixLift 6833444
  have htrace : WordTrace (prefixWord ++ tailWord_6833444) baseStart_6833444 baseEnd_6833444 := by
    simpa [prefixWord, tailWord_6833444, baseEnd_6833444] using wordTrace_append hprefix tailTrace_6833444
  have hstable : (prefixWord ++ tailWord_6833444).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833444).length < 2 ^ (prefixWord ++ tailWord_6833444).sum := by decide
  have hdescent : baseEnd_6833444 < baseStart_6833444 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833444) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833467 : List Nat := [1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 3]
def baseStart_6833467 : Nat := 118140960795 + 6833467 * 2 ^ 59
def prefixEnd_6833467 : Nat := 4983230072969 + 3 ^ 40 * 6833467 * 2
def baseEnd_6833467 : Nat := 3508853107637520762635963

theorem tailTrace_6833467 : CollatzResearch.WordTrace tailWord_6833467 prefixEnd_6833467 3508853107637520762635963 := by
  unfold tailWord_6833467
  simp only [CollatzResearch.WordTrace]
  refine ⟨249237017134523597094058655, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166158011423015731396039103 249237017134523597094058655)
  ·
    refine ⟨373855525701785395641087983, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249237017134523597094058655 373855525701785395641087983)
    ·
      refine ⟨560783288552678093461631975, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373855525701785395641087983 560783288552678093461631975)
      ·
        refine ⟨841174932829017140192447963, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560783288552678093461631975 841174932829017140192447963)
        ·
          refine ⟨1261762399243525710288671945, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 841174932829017140192447963 1261762399243525710288671945)
          ·
            refine ⟨946321799432644282716503959, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 1261762399243525710288671945 946321799432644282716503959)
            ·
              refine ⟨1419482699148966424074755939, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 946321799432644282716503959 1419482699148966424074755939)
              ·
                refine ⟨2129224048723449636112133909, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 1419482699148966424074755939 2129224048723449636112133909)
                ·
                  refine ⟨99807377283911701692756277, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 2129224048723449636112133909 99807377283911701692756277)
                  ·
                    refine ⟨9356941620366722033695901, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99807377283911701692756277 9356941620366722033695901)
                    ·
                      refine ⟨3508853107637520762635963, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9356941620366722033695901 3508853107637520762635963)
                      ·
                        rfl

theorem cell23_6833467_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 1, 2, 1, 1, 6, 5, 3].length) (baseStart_6833467 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833467 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833467 prefixEnd_6833467 := by exact prefixLift 6833467
  have htrace : WordTrace (prefixWord ++ tailWord_6833467) baseStart_6833467 baseEnd_6833467 := by
    simpa [prefixWord, tailWord_6833467, baseEnd_6833467] using wordTrace_append hprefix tailTrace_6833467
  have hstable : (prefixWord ++ tailWord_6833467).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833467).length < 2 ^ (prefixWord ++ tailWord_6833467).sum := by decide
  have hdescent : baseEnd_6833467 < baseStart_6833467 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833467) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833485 : List Nat := [1, 6, 1, 3, 1, 1, 1, 1, 2, 4, 2]
def baseStart_6833485 : Nat := 118140960795 + 6833485 * 2 ^ 59
def prefixEnd_6833485 : Nat := 4983230072969 + 3 ^ 40 * 6833485 * 2
def baseEnd_6833485 : Nat := 3508862350289301692210881

theorem tailTrace_6833485 : CollatzResearch.WordTrace tailWord_6833485 prefixEnd_6833485 3508862350289301692210881 := by
  unfold tailWord_6833485
  simp only [CollatzResearch.WordTrace]
  refine ⟨249237673648458386168213909, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166158449098972257445475939 249237673648458386168213909)
  ·
    refine ⟨11683015952271486851635027, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 6 249237673648458386168213909 11683015952271486851635027)
    ·
      refine ⟨17524523928407230277452541, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11683015952271486851635027 17524523928407230277452541)
      ·
        refine ⟨6571696473152711354044703, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17524523928407230277452541 6571696473152711354044703)
        ·
          refine ⟨9857544709729067031067055, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6571696473152711354044703 9857544709729067031067055)
          ·
            refine ⟨14786317064593600546600583, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857544709729067031067055 14786317064593600546600583)
            ·
              refine ⟨22179475596890400819900875, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14786317064593600546600583 22179475596890400819900875)
              ·
                refine ⟨33269213395335601229851313, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22179475596890400819900875 33269213395335601229851313)
                ·
                  refine ⟨24951910046501700922388485, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33269213395335601229851313 24951910046501700922388485)
                  ·
                    refine ⟨4678483133719068922947841, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24951910046501700922388485 4678483133719068922947841)
                    ·
                      refine ⟨3508862350289301692210881, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678483133719068922947841 3508862350289301692210881)
                      ·
                        rfl

theorem cell23_6833485_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 6, 1, 3, 1, 1, 1, 1, 2, 4, 2].length) (baseStart_6833485 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833485 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833485 prefixEnd_6833485 := by exact prefixLift 6833485
  have htrace : WordTrace (prefixWord ++ tailWord_6833485) baseStart_6833485 baseEnd_6833485 := by
    simpa [prefixWord, tailWord_6833485, baseEnd_6833485] using wordTrace_append hprefix tailTrace_6833485
  have hstable : (prefixWord ++ tailWord_6833485).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833485).length < 2 ^ (prefixWord ++ tailWord_6833485).sum := by decide
  have hdescent : baseEnd_6833485 < baseStart_6833485 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833485) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833504 : List Nat := [2, 1, 1, 3, 4, 1, 2, 1, 3, 5]
def baseStart_6833504 : Nat := 118140960795 + 6833504 * 2 ^ 59
def prefixEnd_6833504 : Nat := 4983230072969 + 3 ^ 40 * 6833504 * 2
def baseEnd_6833504 : Nat := 1169624035473912372624431

theorem tailTrace_6833504 : CollatzResearch.WordTrace tailWord_6833504 prefixEnd_6833504 1169624035473912372624431 := by
  unfold tailWord_6833504
  simp only [CollatzResearch.WordTrace]
  refine ⟨124619183317694776206577783, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166158911090259701608770377 124619183317694776206577783)
  ·
    refine ⟨186928774976542164309866675, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124619183317694776206577783 186928774976542164309866675)
    ·
      refine ⟨280393162464813246464800013, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186928774976542164309866675 280393162464813246464800013)
      ·
        refine ⟨105147435924304967424300005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 280393162464813246464800013 105147435924304967424300005)
        ·
          refine ⟨19715144235807181392056251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105147435924304967424300005 19715144235807181392056251)
          ·
            refine ⟨29572716353710772088084377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19715144235807181392056251 29572716353710772088084377)
            ·
              refine ⟨22179537265283079066063283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29572716353710772088084377 22179537265283079066063283)
              ·
                refine ⟨33269305897924618599094925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22179537265283079066063283 33269305897924618599094925)
                ·
                  refine ⟨12475989711721731974660597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33269305897924618599094925 12475989711721731974660597)
                  ·
                    refine ⟨1169624035473912372624431, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12475989711721731974660597 1169624035473912372624431)
                    ·
                      rfl

theorem cell23_6833504_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 3, 4, 1, 2, 1, 3, 5].length) (baseStart_6833504 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833504 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833504 prefixEnd_6833504 := by exact prefixLift 6833504
  have htrace : WordTrace (prefixWord ++ tailWord_6833504) baseStart_6833504 baseEnd_6833504 := by
    simpa [prefixWord, tailWord_6833504, baseEnd_6833504] using wordTrace_append hprefix tailTrace_6833504
  have hstable : (prefixWord ++ tailWord_6833504).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833504).length < 2 ^ (prefixWord ++ tailWord_6833504).sum := by decide
  have hdescent : baseEnd_6833504 < baseStart_6833504 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833504) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833521 : List Nat := [1, 2, 2, 2, 1, 2, 6, 1, 1, 5]
def baseStart_6833521 : Nat := 118140960795 + 6833521 * 2 ^ 59
def prefixEnd_6833521 : Nat := 4983230072969 + 3 ^ 40 * 6833521 * 2
def baseEnd_6833521 : Nat := 1169626945197621183786905

theorem tailTrace_6833521 : CollatzResearch.WordTrace tailWord_6833521 prefixEnd_6833521 1169626945197621183786905 := by
  unfold tailWord_6833521
  simp only [CollatzResearch.WordTrace]
  refine ⟨249238986676327964316524417, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166159324450885309544349611 249238986676327964316524417)
  ·
    refine ⟨186929240007245973237393313, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249238986676327964316524417 186929240007245973237393313)
    ·
      refine ⟨140196930005434479928044985, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186929240007245973237393313 140196930005434479928044985)
      ·
        refine ⟨105147697504075859946033739, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140196930005434479928044985 105147697504075859946033739)
        ·
          refine ⟨157721546256113789919050609, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105147697504075859946033739 157721546256113789919050609)
          ·
            refine ⟨118291159692085342439287957, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157721546256113789919050609 118291159692085342439287957)
            ·
              refine ⟨5544898110566500426841623, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118291159692085342439287957 5544898110566500426841623)
              ·
                refine ⟨8317347165849750640262435, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5544898110566500426841623 8317347165849750640262435)
                ·
                  refine ⟨12476020748774625960393653, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317347165849750640262435 12476020748774625960393653)
                  ·
                    refine ⟨1169626945197621183786905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12476020748774625960393653 1169626945197621183786905)
                    ·
                      rfl

theorem cell23_6833521_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 2, 2, 1, 2, 6, 1, 1, 5].length) (baseStart_6833521 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833521 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833521 prefixEnd_6833521 := by exact prefixLift 6833521
  have htrace : WordTrace (prefixWord ++ tailWord_6833521) baseStart_6833521 baseEnd_6833521 := by
    simpa [prefixWord, tailWord_6833521, baseEnd_6833521] using wordTrace_append hprefix tailTrace_6833521
  have hstable : (prefixWord ++ tailWord_6833521).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833521).length < 2 ^ (prefixWord ++ tailWord_6833521).sum := by decide
  have hdescent : baseEnd_6833521 < baseStart_6833521 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833521) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833544 : List Nat := [2, 1, 3, 3, 1, 2, 1, 1, 3, 1, 5]
def baseStart_6833544 : Nat := 118140960795 + 6833544 * 2 ^ 59
def prefixEnd_6833544 : Nat := 4983230072969 + 3 ^ 40 * 6833544 * 2
def baseEnd_6833544 : Nat := 3508892645647916961373109

theorem tailTrace_6833544 : CollatzResearch.WordTrace tailWord_6833544 prefixEnd_6833544 3508892645647916961373109 := by
  unfold tailWord_6833544
  simp only [CollatzResearch.WordTrace]
  refine ⟨124619912777622319622305843, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166159883703496426163074457 124619912777622319622305843)
  ·
    refine ⟨186929869166433479433458765, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124619912777622319622305843 186929869166433479433458765)
    ·
      refine ⟨70098700937412554787547037, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186929869166433479433458765 70098700937412554787547037)
      ·
        refine ⟨26287012851529708045330139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70098700937412554787547037 26287012851529708045330139)
        ·
          refine ⟨39430519277294562067995209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26287012851529708045330139 39430519277294562067995209)
          ·
            refine ⟨29572889457970921550996407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39430519277294562067995209 29572889457970921550996407)
            ·
              refine ⟨44359334186956382326494611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29572889457970921550996407 44359334186956382326494611)
              ·
                refine ⟨66539001280434573489741917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44359334186956382326494611 66539001280434573489741917)
                ·
                  refine ⟨24952125480162965058653219, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66539001280434573489741917 24952125480162965058653219)
                  ·
                    refine ⟨37428188220244447587979829, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24952125480162965058653219 37428188220244447587979829)
                    ·
                      refine ⟨3508892645647916961373109, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37428188220244447587979829 3508892645647916961373109)
                      ·
                        rfl

theorem cell23_6833544_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 3, 1, 2, 1, 1, 3, 1, 5].length) (baseStart_6833544 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833544 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833544 prefixEnd_6833544 := by exact prefixLift 6833544
  have htrace : WordTrace (prefixWord ++ tailWord_6833544) baseStart_6833544 baseEnd_6833544 := by
    simpa [prefixWord, tailWord_6833544, baseEnd_6833544] using wordTrace_append hprefix tailTrace_6833544
  have hstable : (prefixWord ++ tailWord_6833544).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833544).length < 2 ^ (prefixWord ++ tailWord_6833544).sum := by decide
  have hdescent : baseEnd_6833544 < baseStart_6833544 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833544) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833547 : List Nat := [1, 1, 1, 1, 4, 3, 2, 10]
def baseStart_6833547 : Nat := 118140960795 + 6833547 * 2 ^ 59
def prefixEnd_6833547 : Nat := 4983230072969 + 3 ^ 40 * 6833547 * 2
def baseEnd_6833547 : Nat := 129959043929254831467985

theorem tailTrace_6833547 : CollatzResearch.WordTrace tailWord_6833547 prefixEnd_6833547 129959043929254831467985 := by
  unfold tailWord_6833547
  simp only [CollatzResearch.WordTrace]
  refine ⟨249239934974233770756970895, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166159956649489180504647263 249239934974233770756970895)
  ·
    refine ⟨373859902461350656135456343, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249239934974233770756970895 373859902461350656135456343)
    ·
      refine ⟨560789853692025984203184515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373859902461350656135456343 560789853692025984203184515)
      ·
        refine ⟨841184780538038976304776773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560789853692025984203184515 841184780538038976304776773)
        ·
          refine ⟨157722146350882308057145645, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 841184780538038976304776773 157722146350882308057145645)
          ·
            refine ⟨59145804881580865521429617, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157722146350882308057145645 59145804881580865521429617)
            ·
              refine ⟨44359353661185649141072213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59145804881580865521429617 44359353661185649141072213)
              ·
                refine ⟨129959043929254831467985, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 10 44359353661185649141072213 129959043929254831467985)
                ·
                  rfl

theorem cell23_6833547_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 2, 10].length) (baseStart_6833547 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833547 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833547 prefixEnd_6833547 := by exact prefixLift 6833547
  have htrace : WordTrace (prefixWord ++ tailWord_6833547) baseStart_6833547 baseEnd_6833547 := by
    simpa [prefixWord, tailWord_6833547, baseEnd_6833547] using wordTrace_append hprefix tailTrace_6833547
  have hstable : (prefixWord ++ tailWord_6833547).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833547).length < 2 ^ (prefixWord ++ tailWord_6833547).sum := by decide
  have hdescent : baseEnd_6833547 < baseStart_6833547 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833547) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833561 : List Nat := [1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 3]
def baseStart_6833561 : Nat := 118140960795 + 6833561 * 2 ^ 59
def prefixEnd_6833561 : Nat := 4983230072969 + 3 ^ 40 * 6833561 * 2
def baseEnd_6833561 : Nat := 3508901374819043394860531

theorem tailTrace_6833561 : CollatzResearch.WordTrace tailWord_6833561 prefixEnd_6833561 3508901374819043394860531 := by
  unfold tailWord_6833561
  simp only [CollatzResearch.WordTrace]
  refine ⟨249240445596183051147980537, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166160297064122034098653691 249240445596183051147980537)
  ·
    refine ⟨186930334197137288360985403, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249240445596183051147980537 186930334197137288360985403)
    ·
      refine ⟨280395501295705932541478105, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186930334197137288360985403 280395501295705932541478105)
      ·
        refine ⟨210296625971779449406108579, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280395501295705932541478105 210296625971779449406108579)
        ·
          refine ⟨315444938957669174109162869, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210296625971779449406108579 315444938957669174109162869)
          ·
            refine ⟨29572963027281485072734019, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 315444938957669174109162869 29572963027281485072734019)
            ·
              refine ⟨44359444540922227609101029, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29572963027281485072734019 44359444540922227609101029)
              ·
                refine ⟨8317395851422917676706443, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44359444540922227609101029 8317395851422917676706443)
                ·
                  refine ⟨12476093777134376515059665, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8317395851422917676706443 12476093777134376515059665)
                  ·
                    refine ⟨9357070332850782386294749, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12476093777134376515059665 9357070332850782386294749)
                    ·
                      refine ⟨3508901374819043394860531, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357070332850782386294749 3508901374819043394860531)
                      ·
                        rfl

theorem cell23_6833561_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 2, 1, 5, 1, 4, 1, 2, 3].length) (baseStart_6833561 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833561 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833561 prefixEnd_6833561 := by exact prefixLift 6833561
  have htrace : WordTrace (prefixWord ++ tailWord_6833561) baseStart_6833561 baseEnd_6833561 := by
    simpa [prefixWord, tailWord_6833561, baseEnd_6833561] using wordTrace_append hprefix tailTrace_6833561
  have hstable : (prefixWord ++ tailWord_6833561).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833561).length < 2 ^ (prefixWord ++ tailWord_6833561).sum := by decide
  have hdescent : baseEnd_6833561 < baseStart_6833561 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833561) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833577 : List Nat := [1, 2, 1, 1, 1, 1, 3, 1, 3, 9]
def baseStart_6833577 : Nat := 118140960795 + 6833577 * 2 ^ 59
def prefixEnd_6833577 : Nat := 4983230072969 + 3 ^ 40 * 6833577 * 2
def baseEnd_6833577 : Nat := 1169636530169838444086819

theorem tailTrace_6833577 : CollatzResearch.WordTrace tailWord_6833577 prefixEnd_6833577 1169636530169838444086819 := by
  unfold tailWord_6833577
  simp only [CollatzResearch.WordTrace]
  refine ⟨249241029164125085880562985, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166160686109416723920375323 249241029164125085880562985)
  ·
    refine ⟨186930771873093814410422239, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249241029164125085880562985 186930771873093814410422239)
    ·
      refine ⟨280396157809640721615633359, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186930771873093814410422239 280396157809640721615633359)
      ·
        refine ⟨420594236714461082423450039, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280396157809640721615633359 420594236714461082423450039)
        ·
          refine ⟨630891355071691623635175059, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420594236714461082423450039 630891355071691623635175059)
          ·
            refine ⟨946337032607537435452762589, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 630891355071691623635175059 946337032607537435452762589)
            ·
              refine ⟨354876387227826538294785971, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946337032607537435452762589 354876387227826538294785971)
              ·
                refine ⟨532314580841739807442178957, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354876387227826538294785971 532314580841739807442178957)
                ·
                  refine ⟨199617967815652427790817109, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 532314580841739807442178957 199617967815652427790817109)
                  ·
                    refine ⟨1169636530169838444086819, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 9 199617967815652427790817109 1169636530169838444086819)
                    ·
                      rfl

theorem cell23_6833577_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 1, 3, 1, 3, 9].length) (baseStart_6833577 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833577 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833577 prefixEnd_6833577 := by exact prefixLift 6833577
  have htrace : WordTrace (prefixWord ++ tailWord_6833577) baseStart_6833577 baseEnd_6833577 := by
    simpa [prefixWord, tailWord_6833577, baseEnd_6833577] using wordTrace_append hprefix tailTrace_6833577
  have hstable : (prefixWord ++ tailWord_6833577).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833577).length < 2 ^ (prefixWord ++ tailWord_6833577).sum := by decide
  have hdescent : baseEnd_6833577 < baseStart_6833577 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833577) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833581 : List Nat := [1, 5, 2, 2, 1, 3, 9]
def baseStart_6833581 : Nat := 118140960795 + 6833581 * 2 ^ 59
def prefixEnd_6833581 : Nat := 4983230072969 + 3 ^ 40 * 6833581 * 2
def baseEnd_6833581 : Nat := 43319896844841152056919

theorem tailTrace_6833581 : CollatzResearch.WordTrace tailWord_6833581 prefixEnd_6833581 43319896844841152056919 := by
  unfold tailWord_6833581
  simp only [CollatzResearch.WordTrace]
  refine ⟨249241175056110594563708597, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166160783370740396375805731 249241175056110594563708597)
  ·
    refine ⟨23366360161510368240347681, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249241175056110594563708597 23366360161510368240347681)
    ·
      refine ⟨17524770121132776180260761, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 23366360161510368240347681 17524770121132776180260761)
      ·
        refine ⟨13143577590849582135195571, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17524770121132776180260761 13143577590849582135195571)
        ·
          refine ⟨19715366386274373202793357, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13143577590849582135195571 19715366386274373202793357)
          ·
            refine ⟨7393262394852889951047509, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19715366386274373202793357 7393262394852889951047509)
            ·
              refine ⟨43319896844841152056919, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7393262394852889951047509 43319896844841152056919)
              ·
                rfl

theorem cell23_6833581_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 2, 2, 1, 3, 9].length) (baseStart_6833581 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833581 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833581 prefixEnd_6833581 := by exact prefixLift 6833581
  have htrace : WordTrace (prefixWord ++ tailWord_6833581) baseStart_6833581 baseEnd_6833581 := by
    simpa [prefixWord, tailWord_6833581, baseEnd_6833581] using wordTrace_append hprefix tailTrace_6833581
  have hstable : (prefixWord ++ tailWord_6833581).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833581).length < 2 ^ (prefixWord ++ tailWord_6833581).sum := by decide
  have hdescent : baseEnd_6833581 < baseStart_6833581 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833581) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833591 : List Nat := [1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 3]
def baseStart_6833591 : Nat := 118140960795 + 6833591 * 2 ^ 59
def prefixEnd_6833591 : Nat := 4983230072969 + 3 ^ 40 * 6833591 * 2
def baseEnd_6833591 : Nat := 3508916779238678277485393

theorem tailTrace_6833591 : CollatzResearch.WordTrace tailWord_6833591 prefixEnd_6833591 3508916779238678277485393 := by
  unfold tailWord_6833591
  simp only [CollatzResearch.WordTrace]
  refine ⟨249241539786074366271572627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166161026524049577514381751 249241539786074366271572627)
  ·
    refine ⟨373862309679111549407358941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249241539786074366271572627 373862309679111549407358941)
    ·
      refine ⟨140198366129666831027759603, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373862309679111549407358941 140198366129666831027759603)
      ·
        refine ⟨210297549194500246541639405, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140198366129666831027759603 210297549194500246541639405)
        ·
          refine ⟨78861580947937592453114777, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210297549194500246541639405 78861580947937592453114777)
          ·
            refine ⟨59146185710953194339836083, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78861580947937592453114777 59146185710953194339836083)
            ·
              refine ⟨88719278566429791509754125, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59146185710953194339836083 88719278566429791509754125)
              ·
                refine ⟨33269729462411171816157797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 88719278566429791509754125 33269729462411171816157797)
                ·
                  refine ⟨6238074274202094715529587, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 33269729462411171816157797 6238074274202094715529587)
                  ·
                    refine ⟨9357111411303142073294381, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238074274202094715529587 9357111411303142073294381)
                    ·
                      refine ⟨3508916779238678277485393, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357111411303142073294381 3508916779238678277485393)
                      ·
                        rfl

theorem cell23_6833591_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 3, 2, 1, 3, 4, 1, 3].length) (baseStart_6833591 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833591 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833591 prefixEnd_6833591 := by exact prefixLift 6833591
  have htrace : WordTrace (prefixWord ++ tailWord_6833591) baseStart_6833591 baseEnd_6833591 := by
    simpa [prefixWord, tailWord_6833591, baseEnd_6833591] using wordTrace_append hprefix tailTrace_6833591
  have hstable : (prefixWord ++ tailWord_6833591).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833591).length < 2 ^ (prefixWord ++ tailWord_6833591).sum := by decide
  have hdescent : baseEnd_6833591 < baseStart_6833591 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833591) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833608 : List Nat := [2, 1, 3, 1, 3, 1, 3, 3, 2, 1, 3]
def baseStart_6833608 : Nat := 118140960795 + 6833608 * 2 ^ 59
def prefixEnd_6833608 : Nat := 4983230072969 + 3 ^ 40 * 6833608 * 2
def baseEnd_6833608 : Nat := 3508925508409804710972815

theorem tailTrace_6833608 : CollatzResearch.WordTrace tailWord_6833608 prefixEnd_6833608 3508925508409804710972815 := by
  unfold tailWord_6833608
  simp only [CollatzResearch.WordTrace]
  refine ⟨124621079913506389087470739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166161439884675185449960985 124621079913506389087470739)
  ·
    refine ⟨186931619870259583631206109, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124621079913506389087470739 186931619870259583631206109)
    ·
      refine ⟨70099357451347343861702291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186931619870259583631206109 70099357451347343861702291)
      ·
        refine ⟨105149036177021015792553437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70099357451347343861702291 105149036177021015792553437)
        ·
          refine ⟨39430888566382880922207539, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105149036177021015792553437 39430888566382880922207539)
          ·
            refine ⟨59146332849574321383311309, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39430888566382880922207539 59146332849574321383311309)
            ·
              refine ⟨22179874818590370518741741, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59146332849574321383311309 22179874818590370518741741)
              ·
                refine ⟨8317453056971388944528153, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22179874818590370518741741 8317453056971388944528153)
                ·
                  refine ⟨6238089792728541708396115, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8317453056971388944528153 6238089792728541708396115)
                  ·
                    refine ⟨9357134689092812562594173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238089792728541708396115 9357134689092812562594173)
                    ·
                      refine ⟨3508925508409804710972815, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357134689092812562594173 3508925508409804710972815)
                      ·
                        rfl

theorem cell23_6833608_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 3, 1, 3, 3, 2, 1, 3].length) (baseStart_6833608 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833608 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833608 prefixEnd_6833608 := by exact prefixLift 6833608
  have htrace : WordTrace (prefixWord ++ tailWord_6833608) baseStart_6833608 baseEnd_6833608 := by
    simpa [prefixWord, tailWord_6833608, baseEnd_6833608] using wordTrace_append hprefix tailTrace_6833608
  have hstable : (prefixWord ++ tailWord_6833608).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833608).length < 2 ^ (prefixWord ++ tailWord_6833608).sum := by decide
  have hdescent : baseEnd_6833608 < baseStart_6833608 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833608) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833661 : List Nat := [1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 4]
def baseStart_6833661 : Nat := 118140960795 + 6833661 * 2 ^ 59
def prefixEnd_6833661 : Nat := 4983230072969 + 3 ^ 40 * 6833661 * 2
def baseEnd_6833661 : Nat := 3508952722884493003610071

theorem tailTrace_6833661 : CollatzResearch.WordTrace tailWord_6833661 prefixEnd_6833661 3508952722884493003610071 := by
  unfold tailWord_6833661
  simp only [CollatzResearch.WordTrace]
  refine ⟨249244092895820768226620837, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166162728597213845484413891 249244092895820768226620837)
  ·
    refine ⟨46733267417966394042491407, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249244092895820768226620837 46733267417966394042491407)
    ·
      refine ⟨70099901126949591063737111, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46733267417966394042491407 70099901126949591063737111)
      ·
        refine ⟨105149851690424386595605667, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70099901126949591063737111 105149851690424386595605667)
        ·
          refine ⟨157724777535636579893408501, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105149851690424386595605667 157724777535636579893408501)
          ·
            refine ⟨14786697893965929365007047, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157724777535636579893408501 14786697893965929365007047)
            ·
              refine ⟨22180046840948894047510571, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14786697893965929365007047 22180046840948894047510571)
              ·
                refine ⟨33270070261423341071265857, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22180046840948894047510571 33270070261423341071265857)
                ·
                  refine ⟨24952552696067505803449393, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33270070261423341071265857 24952552696067505803449393)
                  ·
                    refine ⟨18714414522050629352587045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24952552696067505803449393 18714414522050629352587045)
                    ·
                      refine ⟨3508952722884493003610071, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18714414522050629352587045 3508952722884493003610071)
                      ·
                        rfl

theorem cell23_6833661_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 1, 5, 1, 1, 2, 2, 4].length) (baseStart_6833661 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833661 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833661 prefixEnd_6833661 := by exact prefixLift 6833661
  have htrace : WordTrace (prefixWord ++ tailWord_6833661) baseStart_6833661 baseEnd_6833661 := by
    simpa [prefixWord, tailWord_6833661, baseEnd_6833661] using wordTrace_append hprefix tailTrace_6833661
  have hstable : (prefixWord ++ tailWord_6833661).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833661).length < 2 ^ (prefixWord ++ tailWord_6833661).sum := by decide
  have hdescent : baseEnd_6833661 < baseStart_6833661 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833661) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833665 : List Nat := [1, 2, 4, 1, 4, 1, 2, 1, 1, 4, 2]
def baseStart_6833665 : Nat := 118140960795 + 6833665 * 2 ^ 59
def prefixEnd_6833665 : Nat := 4983230072969 + 3 ^ 40 * 6833665 * 2
def baseEnd_6833665 : Nat := 3508954776807110987960053

theorem tailTrace_6833665 : CollatzResearch.WordTrace tailWord_6833665 prefixEnd_6833665 3508954776807110987960053 := by
  unfold tailWord_6833665
  simp only [CollatzResearch.WordTrace]
  refine ⟨249244238787806276909766449, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166162825858537517939844299 249244238787806276909766449)
  ·
    refine ⟨186933179090854707682324837, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249244238787806276909766449 186933179090854707682324837)
    ·
      refine ⟨35049971079535257690435907, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186933179090854707682324837 35049971079535257690435907)
      ·
        refine ⟨52574956619302886535653861, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35049971079535257690435907 52574956619302886535653861)
        ·
          refine ⟨9857804366119291225435099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52574956619302886535653861 9857804366119291225435099)
          ·
            refine ⟨14786706549178936838152649, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9857804366119291225435099 14786706549178936838152649)
            ·
              refine ⟨11090029911884202628614487, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14786706549178936838152649 11090029911884202628614487)
              ·
                refine ⟨16635044867826303942921731, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11090029911884202628614487 16635044867826303942921731)
                ·
                  refine ⟨24952567301739455914382597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16635044867826303942921731 24952567301739455914382597)
                  ·
                    refine ⟨4678606369076147983946737, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24952567301739455914382597 4678606369076147983946737)
                    ·
                      refine ⟨3508954776807110987960053, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678606369076147983946737 3508954776807110987960053)
                      ·
                        rfl

theorem cell23_6833665_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 1, 4, 1, 2, 1, 1, 4, 2].length) (baseStart_6833665 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833665 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833665 prefixEnd_6833665 := by exact prefixLift 6833665
  have htrace : WordTrace (prefixWord ++ tailWord_6833665) baseStart_6833665 baseEnd_6833665 := by
    simpa [prefixWord, tailWord_6833665, baseEnd_6833665] using wordTrace_append hprefix tailTrace_6833665
  have hstable : (prefixWord ++ tailWord_6833665).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833665).length < 2 ^ (prefixWord ++ tailWord_6833665).sum := by decide
  have hdescent : baseEnd_6833665 < baseStart_6833665 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833665) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833671 : List Nat := [1, 1, 4, 3, 2, 2, 1, 2, 7]
def baseStart_6833671 : Nat := 118140960795 + 6833671 * 2 ^ 59
def prefixEnd_6833671 : Nat := 4983230072969 + 3 ^ 40 * 6833671 * 2
def baseEnd_6833671 : Nat := 389884206410115329387225

theorem tailTrace_6833671 : CollatzResearch.WordTrace tailWord_6833671 prefixEnd_6833671 389884206410115329387225 := by
  unfold tailWord_6833671
  simp only [CollatzResearch.WordTrace]
  refine ⟨249244457625784539934484867, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166162971750523026622989911 249244457625784539934484867)
  ·
    refine ⟨373866686438676809901727301, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249244457625784539934484867 373866686438676809901727301)
    ·
      refine ⟨70100003707251901856573869, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373866686438676809901727301 70100003707251901856573869)
      ·
        refine ⟨26287501390219463196215201, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70100003707251901856573869 26287501390219463196215201)
        ·
          refine ⟨19715626042664597397161401, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26287501390219463196215201 19715626042664597397161401)
          ·
            refine ⟨14786719531998448047871051, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19715626042664597397161401 14786719531998448047871051)
            ·
              refine ⟨22180079297997672071806577, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14786719531998448047871051 22180079297997672071806577)
              ·
                refine ⟨16635059473498254053854933, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22180079297997672071806577 16635059473498254053854933)
                ·
                  refine ⟨389884206410115329387225, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 16635059473498254053854933 389884206410115329387225)
                  ·
                    rfl

theorem cell23_6833671_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 2, 2, 1, 2, 7].length) (baseStart_6833671 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833671 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833671 prefixEnd_6833671 := by exact prefixLift 6833671
  have htrace : WordTrace (prefixWord ++ tailWord_6833671) baseStart_6833671 baseEnd_6833671 := by
    simpa [prefixWord, tailWord_6833671, baseEnd_6833671] using wordTrace_append hprefix tailTrace_6833671
  have hstable : (prefixWord ++ tailWord_6833671).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833671).length < 2 ^ (prefixWord ++ tailWord_6833671).sum := by decide
  have hdescent : baseEnd_6833671 < baseStart_6833671 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833671) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833699 : List Nat := [1, 1, 1, 4, 6, 1, 1, 2, 2, 2, 2]
def baseStart_6833699 : Nat := 118140960795 + 6833699 * 2 ^ 59
def prefixEnd_6833699 : Nat := 4983230072969 + 3 ^ 40 * 6833699 * 2
def baseEnd_6833699 : Nat := 3508972235149363854934897

theorem tailTrace_6833699 : CollatzResearch.WordTrace tailWord_6833699 prefixEnd_6833699 3508972235149363854934897 := by
  unfold tailWord_6833699
  simp only [CollatzResearch.WordTrace]
  refine ⟨249245478869683100716504151, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166163652579788733811002767 249245478869683100716504151)
  ·
    refine ⟨373868218304524651074756227, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249245478869683100716504151 373868218304524651074756227)
    ·
      refine ⟨560802327456786976612134341, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373868218304524651074756227 560802327456786976612134341)
      ·
        refine ⟨105150436398147558114775189, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 560802327456786976612134341 105150436398147558114775189)
        ·
          refine ⟨4928926706163166786630087, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 6 105150436398147558114775189 4928926706163166786630087)
          ·
            refine ⟨7393390059244750179945131, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4928926706163166786630087 7393390059244750179945131)
            ·
              refine ⟨11090085088867125269917697, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393390059244750179945131 11090085088867125269917697)
              ·
                refine ⟨8317563816650343952438273, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11090085088867125269917697 8317563816650343952438273)
                ·
                  refine ⟨6238172862487757964328705, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8317563816650343952438273 6238172862487757964328705)
                  ·
                    refine ⟨4678629646865818473246529, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6238172862487757964328705 4678629646865818473246529)
                    ·
                      refine ⟨3508972235149363854934897, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678629646865818473246529 3508972235149363854934897)
                      ·
                        rfl

theorem cell23_6833699_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 4, 6, 1, 1, 2, 2, 2, 2].length) (baseStart_6833699 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833699 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833699 prefixEnd_6833699 := by exact prefixLift 6833699
  have htrace : WordTrace (prefixWord ++ tailWord_6833699) baseStart_6833699 baseEnd_6833699 := by
    simpa [prefixWord, tailWord_6833699, baseEnd_6833699] using wordTrace_append hprefix tailTrace_6833699
  have hstable : (prefixWord ++ tailWord_6833699).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833699).length < 2 ^ (prefixWord ++ tailWord_6833699).sum := by decide
  have hdescent : baseEnd_6833699 < baseStart_6833699 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833699) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833721 : List Nat := [1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 4]
def baseStart_6833721 : Nat := 118140960795 + 6833721 * 2 ^ 59
def prefixEnd_6833721 : Nat := 4983230072969 + 3 ^ 40 * 6833721 * 2
def baseEnd_6833721 : Nat := 3508983531723762768859795

theorem tailTrace_6833721 : CollatzResearch.WordTrace tailWord_6833721 prefixEnd_6833721 3508983531723762768859795 := by
  unfold tailWord_6833721
  simp only [CollatzResearch.WordTrace]
  refine ⟨249246281275603398473805017, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166164187517068932315870011 249246281275603398473805017)
  ·
    refine ⟨186934710956702548855353763, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249246281275603398473805017 186934710956702548855353763)
    ·
      refine ⟨280402066435053823283030645, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186934710956702548855353763 280402066435053823283030645)
      ·
        refine ⟨26287693728286295932784123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280402066435053823283030645 26287693728286295932784123)
        ·
          refine ⟨39431540592429443899176185, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26287693728286295932784123 39431540592429443899176185)
          ·
            refine ⟨29573655444322082924382139, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39431540592429443899176185 29573655444322082924382139)
            ·
              refine ⟨44360483166483124386573209, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29573655444322082924382139 44360483166483124386573209)
              ·
                refine ⟨33270362374862343289929907, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44360483166483124386573209 33270362374862343289929907)
                ·
                  refine ⟨49905543562293514934894861, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33270362374862343289929907 49905543562293514934894861)
                  ·
                    refine ⟨18714578835860068100585573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49905543562293514934894861 18714578835860068100585573)
                    ·
                      refine ⟨3508983531723762768859795, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18714578835860068100585573 3508983531723762768859795)
                      ·
                        rfl

theorem cell23_6833721_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 1, 2, 1, 2, 1, 3, 4].length) (baseStart_6833721 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833721 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833721 prefixEnd_6833721 := by exact prefixLift 6833721
  have htrace : WordTrace (prefixWord ++ tailWord_6833721) baseStart_6833721 baseEnd_6833721 := by
    simpa [prefixWord, tailWord_6833721, baseEnd_6833721] using wordTrace_append hprefix tailTrace_6833721
  have hstable : (prefixWord ++ tailWord_6833721).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833721).length < 2 ^ (prefixWord ++ tailWord_6833721).sum := by decide
  have hdescent : baseEnd_6833721 < baseStart_6833721 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833721) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833744 : List Nat := [2, 1, 1, 1, 1, 3, 3, 1, 10]
def baseStart_6833744 : Nat := 118140960795 + 6833744 * 2 ^ 59
def prefixEnd_6833744 : Nat := 4983230072969 + 3 ^ 40 * 6833744 * 2
def baseEnd_6833744 : Nat := 389888371308757353208021

theorem tailTrace_6833744 : CollatzResearch.WordTrace tailWord_6833744 prefixEnd_6833744 389888371308757353208021 := by
  unfold tailWord_6833744
  simp only [CollatzResearch.WordTrace]
  refine ⟨124623560077260036700946143, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166164746769680048934594857 124623560077260036700946143)
  ·
    refine ⟨186935340115890055051419215, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124623560077260036700946143 186935340115890055051419215)
    ·
      refine ⟨280403010173835082577128823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186935340115890055051419215 280403010173835082577128823)
      ·
        refine ⟨420604515260752623865693235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280403010173835082577128823 420604515260752623865693235)
        ·
          refine ⟨630906772891128935798539853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420604515260752623865693235 630906772891128935798539853)
          ·
            refine ⟨236590039834173350924452445, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 630906772891128935798539853 236590039834173350924452445)
            ·
              refine ⟨88721264937815006596669667, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236590039834173350924452445 88721264937815006596669667)
              ·
                refine ⟨133081897406722509895004501, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88721264937815006596669667 133081897406722509895004501)
                ·
                  refine ⟨389888371308757353208021, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 10 133081897406722509895004501 389888371308757353208021)
                  ·
                    rfl

theorem cell23_6833744_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 1, 3, 3, 1, 10].length) (baseStart_6833744 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833744 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833744 prefixEnd_6833744 := by exact prefixLift 6833744
  have htrace : WordTrace (prefixWord ++ tailWord_6833744) baseStart_6833744 baseEnd_6833744 := by
    simpa [prefixWord, tailWord_6833744, baseEnd_6833744] using wordTrace_append hprefix tailTrace_6833744
  have hstable : (prefixWord ++ tailWord_6833744).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833744).length < 2 ^ (prefixWord ++ tailWord_6833744).sum := by decide
  have hdescent : baseEnd_6833744 < baseStart_6833744 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833744) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833761 : List Nat := [1, 2, 3, 1, 1, 3, 2, 4, 6]
def baseStart_6833761 : Nat := 118140960795 + 6833761 * 2 ^ 59
def prefixEnd_6833761 : Nat := 4983230072969 + 3 ^ 40 * 6833761 * 2
def baseEnd_6833761 : Nat := 389889341216660290262179

theorem tailTrace_6833761 : CollatzResearch.WordTrace tailWord_6833761 prefixEnd_6833761 389889341216660290262179 := by
  unfold tailWord_6833761
  simp only [CollatzResearch.WordTrace]
  refine ⟨249247740195458485305261137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166165160130305656870174091 249247740195458485305261137)
  ·
    refine ⟨186935805146593863978945853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249247740195458485305261137 186935805146593863978945853)
    ·
      refine ⟨70100926929972698992104695, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186935805146593863978945853 70100926929972698992104695)
      ·
        refine ⟨105151390394959048488157043, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70100926929972698992104695 105151390394959048488157043)
        ·
          refine ⟨157727085592438572732235565, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105151390394959048488157043 157727085592438572732235565)
          ·
            refine ⟨59147657097164464774588337, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157727085592438572732235565 59147657097164464774588337)
            ·
              refine ⟨44360742822873348580941253, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59147657097164464774588337 44360742822873348580941253)
              ·
                refine ⟨8317639279288752858926485, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44360742822873348580941253 8317639279288752858926485)
                ·
                  refine ⟨389889341216660290262179, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8317639279288752858926485 389889341216660290262179)
                  ·
                    rfl

theorem cell23_6833761_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 1, 3, 2, 4, 6].length) (baseStart_6833761 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833761 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833761 prefixEnd_6833761 := by exact prefixLift 6833761
  have htrace : WordTrace (prefixWord ++ tailWord_6833761) baseStart_6833761 baseEnd_6833761 := by
    simpa [prefixWord, tailWord_6833761, baseEnd_6833761] using wordTrace_append hprefix tailTrace_6833761
  have hstable : (prefixWord ++ tailWord_6833761).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833761).length < 2 ^ (prefixWord ++ tailWord_6833761).sum := by decide
  have hdescent : baseEnd_6833761 < baseStart_6833761 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833761) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833765 : List Nat := [1, 3, 1, 3, 3, 3, 1, 1, 3, 4]
def baseStart_6833765 : Nat := 118140960795 + 6833765 * 2 ^ 59
def prefixEnd_6833765 : Nat := 4983230072969 + 3 ^ 40 * 6833765 * 2
def baseEnd_6833765 : Nat := 1169668708290853532236531

theorem tailTrace_6833765 : CollatzResearch.WordTrace tailWord_6833765 prefixEnd_6833765 1169668708290853532236531 := by
  unfold tailWord_6833765
  simp only [CollatzResearch.WordTrace]
  refine ⟨249247886087443993988406749, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166165257391629329325604499 249247886087443993988406749)
  ·
    refine ⟨93467957282791497745652531, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249247886087443993988406749 93467957282791497745652531)
    ·
      refine ⟨140201935924187246618478797, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93467957282791497745652531 140201935924187246618478797)
      ·
        refine ⟨52575725971570217481929549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140201935924187246618478797 52575725971570217481929549)
        ·
          refine ⟨19715897239338831555723581, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52575725971570217481929549 19715897239338831555723581)
          ·
            refine ⟨7393461464752061833396343, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19715897239338831555723581 7393461464752061833396343)
            ·
              refine ⟨11090192197128092750094515, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7393461464752061833396343 11090192197128092750094515)
              ·
                refine ⟨16635288295692139125141773, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11090192197128092750094515 16635288295692139125141773)
                ·
                  refine ⟨6238233110884552171928165, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16635288295692139125141773 6238233110884552171928165)
                  ·
                    refine ⟨1169668708290853532236531, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6238233110884552171928165 1169668708290853532236531)
                    ·
                      rfl

theorem cell23_6833765_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 3, 3, 1, 1, 3, 4].length) (baseStart_6833765 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833765 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833765 prefixEnd_6833765 := by exact prefixLift 6833765
  have htrace : WordTrace (prefixWord ++ tailWord_6833765) baseStart_6833765 baseEnd_6833765 := by
    simpa [prefixWord, tailWord_6833765, baseEnd_6833765] using wordTrace_append hprefix tailTrace_6833765
  have hstable : (prefixWord ++ tailWord_6833765).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833765).length < 2 ^ (prefixWord ++ tailWord_6833765).sum := by decide
  have hdescent : baseEnd_6833765 < baseStart_6833765 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833765) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833778 : List Nat := [3, 2, 1, 2, 3, 2, 1, 3, 6]
def baseStart_6833778 : Nat := 118140960795 + 6833778 * 2 ^ 59
def prefixEnd_6833778 : Nat := 4983230072969 + 3 ^ 40 * 6833778 * 2
def baseEnd_6833778 : Nat := 389890311124563227316337

theorem tailTrace_6833778 : CollatzResearch.WordTrace tailWord_6833778 prefixEnd_6833778 389890311124563227316337 := by
  unfold tailWord_6833778
  simp only [CollatzResearch.WordTrace]
  refine ⟨62312090059099224302157497, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166165573490931264805753325 62312090059099224302157497)
  ·
    refine ⟨46734067544324418226618123, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62312090059099224302157497 46734067544324418226618123)
    ·
      refine ⟨70101101316486627339927185, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46734067544324418226618123 70101101316486627339927185)
      ·
        refine ⟨52575825987364970504945389, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70101101316486627339927185 52575825987364970504945389)
        ·
          refine ⟨19715934745261863939354521, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52575825987364970504945389 19715934745261863939354521)
          ·
            refine ⟨14786951058946397954515891, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19715934745261863939354521 14786951058946397954515891)
            ·
              refine ⟨22180426588419596931773837, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14786951058946397954515891 22180426588419596931773837)
              ·
                refine ⟨8317659970657348849415189, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22180426588419596931773837 8317659970657348849415189)
                ·
                  refine ⟨389890311124563227316337, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8317659970657348849415189 389890311124563227316337)
                  ·
                    rfl

theorem cell23_6833778_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 3, 2, 1, 3, 6].length) (baseStart_6833778 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833778 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833778 prefixEnd_6833778 := by exact prefixLift 6833778
  have htrace : WordTrace (prefixWord ++ tailWord_6833778) baseStart_6833778 baseEnd_6833778 := by
    simpa [prefixWord, tailWord_6833778, baseEnd_6833778] using wordTrace_append hprefix tailTrace_6833778
  have hstable : (prefixWord ++ tailWord_6833778).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833778).length < 2 ^ (prefixWord ++ tailWord_6833778).sum := by decide
  have hdescent : baseEnd_6833778 < baseStart_6833778 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833778) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833788 : List Nat := [2, 2, 2, 1, 1, 2, 1, 3, 5, 1, 3]
def baseStart_6833788 : Nat := 118140960795 + 6833788 * 2 ^ 59
def prefixEnd_6833788 : Nat := 4983230072969 + 3 ^ 40 * 6833788 * 2
def baseEnd_6833788 : Nat := 3509017934927614006721987

theorem tailTrace_6833788 : CollatzResearch.WordTrace tailWord_6833788 prefixEnd_6833788 3509017934927614006721987 := by
  unfold tailWord_6833788
  simp only [CollatzResearch.WordTrace]
  refine ⟨124624362483180334458247009, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166165816644240445944329345 124624362483180334458247009)
  ·
    refine ⟨93468271862385250843685257, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124624362483180334458247009 93468271862385250843685257)
    ·
      refine ⟨70101203896788938132763943, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93468271862385250843685257 70101203896788938132763943)
      ·
        refine ⟨105151805845183407199145915, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70101203896788938132763943 105151805845183407199145915)
        ·
          refine ⟨157727708767775110798718873, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105151805845183407199145915 157727708767775110798718873)
          ·
            refine ⟨118295781575831333099039155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157727708767775110798718873 118295781575831333099039155)
            ·
              refine ⟨177443672363746999648558733, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118295781575831333099039155 177443672363746999648558733)
              ·
                refine ⟨66541377136405124868209525, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177443672363746999648558733 66541377136405124868209525)
                ·
                  refine ⟨6238254106537980456394643, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66541377136405124868209525 6238254106537980456394643)
                  ·
                    refine ⟨9357381159806970684591965, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238254106537980456394643 9357381159806970684591965)
                    ·
                      refine ⟨3509017934927614006721987, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357381159806970684591965 3509017934927614006721987)
                      ·
                        rfl

theorem cell23_6833788_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 1, 2, 1, 3, 5, 1, 3].length) (baseStart_6833788 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833788 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833788 prefixEnd_6833788 := by exact prefixLift 6833788
  have htrace : WordTrace (prefixWord ++ tailWord_6833788) baseStart_6833788 baseEnd_6833788 := by
    simpa [prefixWord, tailWord_6833788, baseEnd_6833788] using wordTrace_append hprefix tailTrace_6833788
  have hstable : (prefixWord ++ tailWord_6833788).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833788).length < 2 ^ (prefixWord ++ tailWord_6833788).sum := by decide
  have hdescent : baseEnd_6833788 < baseStart_6833788 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833788) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833811 : List Nat := [1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 4]
def baseStart_6833811 : Nat := 118140960795 + 6833811 * 2 ^ 59
def prefixEnd_6833811 : Nat := 4983230072969 + 3 ^ 40 * 6833811 * 2
def baseEnd_6833811 : Nat := 3509029744982667416734381

theorem tailTrace_6833811 : CollatzResearch.WordTrace tailWord_6833811 prefixEnd_6833811 3509029744982667416734381 := by
  unfold tailWord_6833811
  simp only [CollatzResearch.WordTrace]
  refine ⟨249249563845277343844581287, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166166375896851562563054191 249249563845277343844581287)
  ·
    refine ⟨373874345767916015766871931, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249249563845277343844581287 373874345767916015766871931)
    ·
      refine ⟨560811518651874023650307897, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373874345767916015766871931 560811518651874023650307897)
      ·
        refine ⟨420608638988905517737730923, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560811518651874023650307897 420608638988905517737730923)
        ·
          refine ⟨630912958483358276606596385, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420608638988905517737730923 630912958483358276606596385)
          ·
            refine ⟨473184718862518707454947289, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 630912958483358276606596385 473184718862518707454947289)
            ·
              refine ⟨354888539146889030591210467, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473184718862518707454947289 354888539146889030591210467)
              ·
                refine ⟨532332808720333545886815701, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354888539146889030591210467 532332808720333545886815701)
                ·
                  refine ⟨12476550204382817481722243, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 532332808720333545886815701 12476550204382817481722243)
                  ·
                    refine ⟨18714825306574226222583365, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12476550204382817481722243 18714825306574226222583365)
                    ·
                      refine ⟨3509029744982667416734381, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18714825306574226222583365 3509029744982667416734381)
                      ·
                        rfl

theorem cell23_6833811_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 2, 2, 1, 7, 1, 4].length) (baseStart_6833811 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833811 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833811 prefixEnd_6833811 := by exact prefixLift 6833811
  have htrace : WordTrace (prefixWord ++ tailWord_6833811) baseStart_6833811 baseEnd_6833811 := by
    simpa [prefixWord, tailWord_6833811, baseEnd_6833811] using wordTrace_append hprefix tailTrace_6833811
  have hstable : (prefixWord ++ tailWord_6833811).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833811).length < 2 ^ (prefixWord ++ tailWord_6833811).sum := by decide
  have hdescent : baseEnd_6833811 < baseStart_6833811 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833811) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833815 : List Nat := [1, 1, 3, 3, 2, 2, 2, 2, 2, 3, 2]
def baseStart_6833815 : Nat := 118140960795 + 6833815 * 2 ^ 59
def prefixEnd_6833815 : Nat := 4983230072969 + 3 ^ 40 * 6833815 * 2
def baseEnd_6833815 : Nat := 3509031798905285401084363

theorem tailTrace_6833815 : CollatzResearch.WordTrace tailWord_6833815 prefixEnd_6833815 3509031798905285401084363 := by
  unfold tailWord_6833815
  simp only [CollatzResearch.WordTrace]
  refine ⟨249249709737262852527726899, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166166473158175235018484599 249249709737262852527726899)
  ·
    refine ⟨373874564605894278791590349, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249249709737262852527726899 373874564605894278791590349)
    ·
      refine ⟨140202961727210354546846381, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373874564605894278791590349 140202961727210354546846381)
      ·
        refine ⟨52576110647703882955067393, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140202961727210354546846381 52576110647703882955067393)
        ·
          refine ⟨39432082985777912216300545, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52576110647703882955067393 39432082985777912216300545)
          ·
            refine ⟨29574062239333434162225409, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39432082985777912216300545 29574062239333434162225409)
            ·
              refine ⟨22180546679500075621669057, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29574062239333434162225409 22180546679500075621669057)
              ·
                refine ⟨16635410009625056716251793, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22180546679500075621669057 16635410009625056716251793)
                ·
                  refine ⟨12476557507218792537188845, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16635410009625056716251793 12476557507218792537188845)
                  ·
                    refine ⟨4678709065207047201445817, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12476557507218792537188845 4678709065207047201445817)
                    ·
                      refine ⟨3509031798905285401084363, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678709065207047201445817 3509031798905285401084363)
                      ·
                        rfl

theorem cell23_6833815_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 2, 2, 2, 2, 2, 3, 2].length) (baseStart_6833815 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833815 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833815 prefixEnd_6833815 := by exact prefixLift 6833815
  have htrace : WordTrace (prefixWord ++ tailWord_6833815) baseStart_6833815 baseEnd_6833815 := by
    simpa [prefixWord, tailWord_6833815, baseEnd_6833815] using wordTrace_append hprefix tailTrace_6833815
  have hstable : (prefixWord ++ tailWord_6833815).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833815).length < 2 ^ (prefixWord ++ tailWord_6833815).sum := by decide
  have hdescent : baseEnd_6833815 < baseStart_6833815 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833815) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833821 : List Nat := [1, 4, 2, 1, 1, 1, 1, 1, 5, 6]
def baseStart_6833821 : Nat := 118140960795 + 6833821 * 2 ^ 59
def prefixEnd_6833821 : Nat := 4983230072969 + 3 ^ 40 * 6833821 * 2
def baseEnd_6833821 : Nat := 1169678293263070792536445

theorem tailTrace_6833821 : CollatzResearch.WordTrace tailWord_6833821 prefixEnd_6833821 1169678293263070792536445 := by
  unfold tailWord_6833821
  simp only [CollatzResearch.WordTrace]
  refine ⟨249249928575241115552445317, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166166619050160743701630211 249249928575241115552445317)
  ·
    refine ⟨46734361607857709166083497, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249249928575241115552445317 46734361607857709166083497)
    ·
      refine ⟨35050771205893281874562623, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46734361607857709166083497 35050771205893281874562623)
      ·
        refine ⟨52576156808839922811843935, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35050771205893281874562623 52576156808839922811843935)
        ·
          refine ⟨78864235213259884217765903, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52576156808839922811843935 78864235213259884217765903)
          ·
            refine ⟨118296352819889826326648855, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78864235213259884217765903 118296352819889826326648855)
            ·
              refine ⟨177444529229834739489973283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118296352819889826326648855 177444529229834739489973283)
              ·
                refine ⟨266166793844752109234959925, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177444529229834739489973283 266166793844752109234959925)
                ·
                  refine ⟨24953136922945510240777493, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 266166793844752109234959925 24953136922945510240777493)
                  ·
                    refine ⟨1169678293263070792536445, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24953136922945510240777493 1169678293263070792536445)
                    ·
                      rfl

theorem cell23_6833821_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 1, 1, 1, 1, 1, 5, 6].length) (baseStart_6833821 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833821 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833821 prefixEnd_6833821 := by exact prefixLift 6833821
  have htrace : WordTrace (prefixWord ++ tailWord_6833821) baseStart_6833821 baseEnd_6833821 := by
    simpa [prefixWord, tailWord_6833821, baseEnd_6833821] using wordTrace_append hprefix tailTrace_6833821
  have hstable : (prefixWord ++ tailWord_6833821).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833821).length < 2 ^ (prefixWord ++ tailWord_6833821).sum := by decide
  have hdescent : baseEnd_6833821 < baseStart_6833821 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833821) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833828 : List Nat := [2, 3, 1, 2, 2, 2, 1, 2, 3, 1, 4]
def baseStart_6833828 : Nat := 118140960795 + 6833828 * 2 ^ 59
def prefixEnd_6833828 : Nat := 4983230072969 + 3 ^ 40 * 6833828 * 2
def baseEnd_6833828 : Nat := 3509038474153793850221803

theorem tailTrace_6833828 : CollatzResearch.WordTrace tailWord_6833828 prefixEnd_6833828 3509038474153793850221803 := by
  unfold tailWord_6833828
  simp only [CollatzResearch.WordTrace]
  refine ⟨124625091943107877873975069, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166166789257477170498633425 124625091943107877873975069)
  ·
    refine ⟨46734409478665454202740651, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124625091943107877873975069 46734409478665454202740651)
    ·
      refine ⟨70101614217998181304110977, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46734409478665454202740651 70101614217998181304110977)
      ·
        refine ⟨52576210663498635978083233, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70101614217998181304110977 52576210663498635978083233)
        ·
          refine ⟨39432157997623976983562425, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52576210663498635978083233 39432157997623976983562425)
          ·
            refine ⟨29574118498217982737671819, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39432157997623976983562425 29574118498217982737671819)
            ·
              refine ⟨44361177747326974106507729, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29574118498217982737671819 44361177747326974106507729)
              ·
                refine ⟨33270883310495230579880797, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44361177747326974106507729 33270883310495230579880797)
                ·
                  refine ⟨12476581241435711467455299, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33270883310495230579880797 12476581241435711467455299)
                  ·
                    refine ⟨18714871862153567201182949, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12476581241435711467455299 18714871862153567201182949)
                    ·
                      refine ⟨3509038474153793850221803, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18714871862153567201182949 3509038474153793850221803)
                      ·
                        rfl

theorem cell23_6833828_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 2, 2, 2, 1, 2, 3, 1, 4].length) (baseStart_6833828 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833828 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833828 prefixEnd_6833828 := by exact prefixLift 6833828
  have htrace : WordTrace (prefixWord ++ tailWord_6833828) baseStart_6833828 baseEnd_6833828 := by
    simpa [prefixWord, tailWord_6833828, baseEnd_6833828] using wordTrace_append hprefix tailTrace_6833828
  have hstable : (prefixWord ++ tailWord_6833828).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833828).length < 2 ^ (prefixWord ++ tailWord_6833828).sum := by decide
  have hdescent : baseEnd_6833828 < baseStart_6833828 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833828) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833868 : List Nat := [2, 2, 1, 5, 2, 1, 10]
def baseStart_6833868 : Nat := 118140960795 + 6833868 * 2 ^ 59
def prefixEnd_6833868 : Nat := 4983230072969 + 3 ^ 40 * 6833868 * 2
def baseEnd_6833868 : Nat := 43321716214567576465699

theorem tailTrace_6833868 : CollatzResearch.WordTrace tailWord_6833868 prefixEnd_6833868 43321716214567576465699 := by
  unfold tailWord_6833868
  simp only [CollatzResearch.WordTrace]
  refine ⟨124625821403035421289703129, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166167761870713895052937505 124625821403035421289703129)
  ·
    refine ⟨93469366052276565967277347, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124625821403035421289703129 93469366052276565967277347)
    ·
      refine ⟨140204049078414848950916021, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93469366052276565967277347 140204049078414848950916021)
      ·
        refine ⟨13144129601101392089148377, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140204049078414848950916021 13144129601101392089148377)
        ·
          refine ⟨9858097200826044066861283, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13144129601101392089148377 9858097200826044066861283)
          ·
            refine ⟨14787145801239066100291925, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858097200826044066861283 14787145801239066100291925)
            ·
              refine ⟨43321716214567576465699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 10 14787145801239066100291925 43321716214567576465699)
              ·
                rfl

theorem cell23_6833868_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 10].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 5, 2, 1, 10].length) (baseStart_6833868 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833868 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833868 prefixEnd_6833868 := by exact prefixLift 6833868
  have htrace : WordTrace (prefixWord ++ tailWord_6833868) baseStart_6833868 baseEnd_6833868 := by
    simpa [prefixWord, tailWord_6833868, baseEnd_6833868] using wordTrace_append hprefix tailTrace_6833868
  have hstable : (prefixWord ++ tailWord_6833868).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833868).length < 2 ^ (prefixWord ++ tailWord_6833868).sum := by decide
  have hdescent : baseEnd_6833868 < baseStart_6833868 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833868) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833911 : List Nat := [1, 1, 3, 1, 1, 1, 4, 2, 1, 8]
def baseStart_6833911 : Nat := 118140960795 + 6833911 * 2 ^ 59
def prefixEnd_6833911 : Nat := 4983230072969 + 3 ^ 40 * 6833911 * 2
def baseEnd_6833911 : Nat := 1169693697682705675161307

theorem tailTrace_6833911 : CollatzResearch.WordTrace tailWord_6833911 prefixEnd_6833911 1169693697682705675161307 := by
  unfold tailWord_6833911
  simp only [CollatzResearch.WordTrace]
  refine ⟨249253211144915060923221587, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166168807429943373948814391 249253211144915060923221587)
  ·
    refine ⟨373879816717372591384832381, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249253211144915060923221587 373879816717372591384832381)
    ·
      refine ⟨140204931269014721769312143, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373879816717372591384832381 140204931269014721769312143)
      ·
        refine ⟨210307396903522082653968215, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140204931269014721769312143 210307396903522082653968215)
        ·
          refine ⟨315461095355283123980952323, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210307396903522082653968215 315461095355283123980952323)
          ·
            refine ⟨473191643032924685971428485, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315461095355283123980952323 473191643032924685971428485)
            ·
              refine ⟨88723433068673378619642841, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 473191643032924685971428485 88723433068673378619642841)
              ·
                refine ⟨66542574801505033964732131, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88723433068673378619642841 66542574801505033964732131)
                ·
                  refine ⟨99813862202257550947098197, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66542574801505033964732131 99813862202257550947098197)
                  ·
                    refine ⟨1169693697682705675161307, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99813862202257550947098197 1169693697682705675161307)
                    ·
                      rfl

theorem cell23_6833911_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 1, 4, 2, 1, 8].length) (baseStart_6833911 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833911 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833911 prefixEnd_6833911 := by exact prefixLift 6833911
  have htrace : WordTrace (prefixWord ++ tailWord_6833911) baseStart_6833911 baseEnd_6833911 := by
    simpa [prefixWord, tailWord_6833911, baseEnd_6833911] using wordTrace_append hprefix tailTrace_6833911
  have hstable : (prefixWord ++ tailWord_6833911).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833911).length < 2 ^ (prefixWord ++ tailWord_6833911).sum := by decide
  have hdescent : baseEnd_6833911 < baseStart_6833911 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833911) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833940 : List Nat := [2, 4, 4, 1, 2, 1, 2, 1, 2, 4]
def baseStart_6833940 : Nat := 118140960795 + 6833940 * 2 ^ 59
def prefixEnd_6833940 : Nat := 4983230072969 + 3 ^ 40 * 6833940 * 2
def baseEnd_6833940 : Nat := 1169698661329032470673763

theorem tailTrace_6833940 : CollatzResearch.WordTrace tailWord_6833940 prefixEnd_6833940 1169698661329032470673763 := by
  unfold tailWord_6833940
  simp only [CollatzResearch.WordTrace]
  refine ⟨124627134430904999438013637, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166169512574539999250684849 124627134430904999438013637)
  ·
    refine ⟨23367587705794687394627557, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124627134430904999438013637 23367587705794687394627557)
    ·
      refine ⟨4381422694836503886492667, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 23367587705794687394627557 4381422694836503886492667)
      ·
        refine ⟨6572134042254755829739001, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 4381422694836503886492667 6572134042254755829739001)
        ·
          refine ⟨4929100531691066872304251, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 6572134042254755829739001 4929100531691066872304251)
          ·
            refine ⟨7393650797536600308456377, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929100531691066872304251 7393650797536600308456377)
            ·
              refine ⟨5545238098152450231342283, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7393650797536600308456377 5545238098152450231342283)
              ·
                refine ⟨8317857147228675347013425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545238098152450231342283 8317857147228675347013425)
                ·
                  refine ⟨6238392860421506510260069, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8317857147228675347013425 6238392860421506510260069)
                  ·
                    refine ⟨1169698661329032470673763, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6238392860421506510260069 1169698661329032470673763)
                    ·
                      rfl

theorem cell23_6833940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 4, 1, 2, 1, 2, 1, 2, 4].length) (baseStart_6833940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833940 prefixEnd_6833940 := by exact prefixLift 6833940
  have htrace : WordTrace (prefixWord ++ tailWord_6833940) baseStart_6833940 baseEnd_6833940 := by
    simpa [prefixWord, tailWord_6833940, baseEnd_6833940] using wordTrace_append hprefix tailTrace_6833940
  have hstable : (prefixWord ++ tailWord_6833940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833940).length < 2 ^ (prefixWord ++ tailWord_6833940).sum := by decide
  have hdescent : baseEnd_6833940 < baseStart_6833940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833948 : List Nat := [2, 2, 3, 1, 1, 2, 2, 1, 1, 4, 4]
def baseStart_6833948 : Nat := 118140960795 + 6833948 * 2 ^ 59
def prefixEnd_6833948 : Nat := 4983230072969 + 3 ^ 40 * 6833948 * 2
def baseEnd_6833948 : Nat := 3509100091832333380721251

theorem tailTrace_6833948 : CollatzResearch.WordTrace tailWord_6833948 prefixEnd_6833948 3509100091832333380721251 := by
  unfold tailWord_6833948
  simp only [CollatzResearch.WordTrace]
  refine ⟨124627280322890508121159249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166169707097187344161545665 124627280322890508121159249)
  ·
    refine ⟨93470460242167881090869437, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124627280322890508121159249 93470460242167881090869437)
    ·
      refine ⟨35051422590812955409076039, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93470460242167881090869437 35051422590812955409076039)
      ·
        refine ⟨52577133886219433113614059, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35051422590812955409076039 52577133886219433113614059)
        ·
          refine ⟨78865700829329149670421089, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52577133886219433113614059 78865700829329149670421089)
          ·
            refine ⟨59149275621996862252815817, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78865700829329149670421089 59149275621996862252815817)
            ·
              refine ⟨44361956716497646689611863, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59149275621996862252815817 44361956716497646689611863)
              ·
                refine ⟨66542935074746470034417795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44361956716497646689611863 66542935074746470034417795)
                ·
                  refine ⟨99814402612119705051626693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66542935074746470034417795 99814402612119705051626693)
                  ·
                    refine ⟨18715200489772444697180005, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 99814402612119705051626693 18715200489772444697180005)
                    ·
                      refine ⟨3509100091832333380721251, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18715200489772444697180005 3509100091832333380721251)
                      ·
                        rfl

theorem cell23_6833948_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 4, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 2, 2, 1, 1, 4, 4].length) (baseStart_6833948 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833948 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833948 prefixEnd_6833948 := by exact prefixLift 6833948
  have htrace : WordTrace (prefixWord ++ tailWord_6833948) baseStart_6833948 baseEnd_6833948 := by
    simpa [prefixWord, tailWord_6833948, baseEnd_6833948] using wordTrace_append hprefix tailTrace_6833948
  have hstable : (prefixWord ++ tailWord_6833948).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833948).length < 2 ^ (prefixWord ++ tailWord_6833948).sum := by decide
  have hdescent : baseEnd_6833948 < baseStart_6833948 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833948) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833968 : List Nat := [2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3]
def baseStart_6833968 : Nat := 118140960795 + 6833968 * 2 ^ 59
def prefixEnd_6833968 : Nat := 4983230072969 + 3 ^ 40 * 6833968 * 2
def baseEnd_6833968 : Nat := 3509110361445423302471159

theorem tailTrace_6833968 : CollatzResearch.WordTrace tailWord_6833968 prefixEnd_6833968 3509110361445423302471159 := by
  unfold tailWord_6833968
  simp only [CollatzResearch.WordTrace]
  refine ⟨124627645052854279829023279, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166170193403805706438697705 124627645052854279829023279)
  ·
    refine ⟨186941467579281419743534919, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124627645052854279829023279 186941467579281419743534919)
    ·
      refine ⟨280412201368922129615302379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186941467579281419743534919 280412201368922129615302379)
      ·
        refine ⟨420618302053383194422953569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280412201368922129615302379 420618302053383194422953569)
        ·
          refine ⟨315463726540037395817215177, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420618302053383194422953569 315463726540037395817215177)
          ·
            refine ⟨236597794905028046862911383, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315463726540037395817215177 236597794905028046862911383)
            ·
              refine ⟨354896692357542070294367075, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236597794905028046862911383 354896692357542070294367075)
              ·
                refine ⟨532345038536313105441550613, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354896692357542070294367075 532345038536313105441550613)
                ·
                  refine ⟨24953673681389676817572685, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 532345038536313105441550613 24953673681389676817572685)
                  ·
                    refine ⟨9357627630521128806589757, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24953673681389676817572685 9357627630521128806589757)
                    ·
                      refine ⟨3509110361445423302471159, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357627630521128806589757 3509110361445423302471159)
                      ·
                        rfl

theorem cell23_6833968_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 2, 1, 1, 6, 3, 3].length) (baseStart_6833968 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833968 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833968 prefixEnd_6833968 := by exact prefixLift 6833968
  have htrace : WordTrace (prefixWord ++ tailWord_6833968) baseStart_6833968 baseEnd_6833968 := by
    simpa [prefixWord, tailWord_6833968, baseEnd_6833968] using wordTrace_append hprefix tailTrace_6833968
  have hstable : (prefixWord ++ tailWord_6833968).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833968).length < 2 ^ (prefixWord ++ tailWord_6833968).sum := by decide
  have hdescent : baseEnd_6833968 < baseStart_6833968 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833968) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6833992 : List Nat := [2, 1, 3, 1, 1, 4, 4, 2, 5]
def baseStart_6833992 : Nat := 118140960795 + 6833992 * 2 ^ 59
def prefixEnd_6833992 : Nat := 4983230072969 + 3 ^ 40 * 6833992 * 2
def baseEnd_6833992 : Nat := 389902520553459023174561

theorem tailTrace_6833992 : CollatzResearch.WordTrace tailWord_6833992 prefixEnd_6833992 389902520553459023174561 := by
  unfold tailWord_6833992
  simp only [CollatzResearch.WordTrace]
  refine ⟨124628082728810805878460115, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166170776971747741171280153 124628082728810805878460115)
  ·
    refine ⟨186942124093216208817690173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124628082728810805878460115 186942124093216208817690173)
    ·
      refine ⟨70103296534956078306633815, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186942124093216208817690173 70103296534956078306633815)
      ·
        refine ⟨105154944802434117459950723, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70103296534956078306633815 105154944802434117459950723)
        ·
          refine ⟨157732417203651176189926085, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105154944802434117459950723 157732417203651176189926085)
          ·
            refine ⟨29574828225684595535611141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 157732417203651176189926085 29574828225684595535611141)
            ·
              refine ⟨5545280292315861662927089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29574828225684595535611141 5545280292315861662927089)
              ·
                refine ⟨4158960219236896247195317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5545280292315861662927089 4158960219236896247195317)
                ·
                  refine ⟨389902520553459023174561, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4158960219236896247195317 389902520553459023174561)
                  ·
                    rfl

theorem cell23_6833992_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 3, 1, 1, 4, 4, 2, 5].length) (baseStart_6833992 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6833992 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6833992 prefixEnd_6833992 := by exact prefixLift 6833992
  have htrace : WordTrace (prefixWord ++ tailWord_6833992) baseStart_6833992 baseEnd_6833992 := by
    simpa [prefixWord, tailWord_6833992, baseEnd_6833992] using wordTrace_append hprefix tailTrace_6833992
  have hstable : (prefixWord ++ tailWord_6833992).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6833992).length < 2 ^ (prefixWord ++ tailWord_6833992).sum := by decide
  have hdescent : baseEnd_6833992 < baseStart_6833992 := by decide
  rcases family_descends (prefixWord ++ tailWord_6833992) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834045 : List Nat := [1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 3]
def baseStart_6834045 : Nat := 118140960795 + 6834045 * 2 ^ 59
def prefixEnd_6834045 : Nat := 4983230072969 + 3 ^ 40 * 6834045 * 2
def baseEnd_6834045 : Nat := 3509149899455819501208305

theorem tailTrace_6834045 : CollatzResearch.WordTrace tailWord_6834045 prefixEnd_6834045 3509149899455819501208305 := by
  unfold tailWord_6834045
  simp only [CollatzResearch.WordTrace]
  refine ⟨249258098526429601808599589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166172065684286401205733059 249258098526429601808599589)
  ·
    refine ⟨46735893473705550339112423, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249258098526429601808599589 46735893473705550339112423)
    ·
      refine ⟨70103840210558325508668635, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46735893473705550339112423 70103840210558325508668635)
      ·
        refine ⟨105155760315837488263002953, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70103840210558325508668635 105155760315837488263002953)
        ·
          refine ⟨78866820236878116197252215, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105155760315837488263002953 78866820236878116197252215)
          ·
            refine ⟨118300230355317174295878323, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78866820236878116197252215 118300230355317174295878323)
            ·
              refine ⟨177450345532975761443817485, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118300230355317174295878323 177450345532975761443817485)
              ·
                refine ⟨66543879574865910541431557, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 177450345532975761443817485 66543879574865910541431557)
                ·
                  refine ⟨12476977420287358226518417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66543879574865910541431557 12476977420287358226518417)
                  ·
                    refine ⟨9357733065215518669888813, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12476977420287358226518417 9357733065215518669888813)
                    ·
                      refine ⟨3509149899455819501208305, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357733065215518669888813 3509149899455819501208305)
                      ·
                        rfl

theorem cell23_6834045_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 1, 2, 1, 1, 3, 4, 2, 3].length) (baseStart_6834045 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834045 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834045 prefixEnd_6834045 := by exact prefixLift 6834045
  have htrace : WordTrace (prefixWord ++ tailWord_6834045) baseStart_6834045 baseEnd_6834045 := by
    simpa [prefixWord, tailWord_6834045, baseEnd_6834045] using wordTrace_append hprefix tailTrace_6834045
  have hstable : (prefixWord ++ tailWord_6834045).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834045).length < 2 ^ (prefixWord ++ tailWord_6834045).sum := by decide
  have hdescent : baseEnd_6834045 < baseStart_6834045 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834045) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834048 : List Nat := [2, 1, 1, 2, 1, 2, 5, 1, 8]
def baseStart_6834048 : Nat := 118140960795 + 6834048 * 2 ^ 59
def prefixEnd_6834048 : Nat := 4983230072969 + 3 ^ 40 * 6834048 * 2
def baseEnd_6834048 : Nat := 389905715544198109941199

theorem tailTrace_6834048 : CollatzResearch.WordTrace tailWord_6834048 prefixEnd_6834048 389905715544198109941199 := by
  unfold tailWord_6834048
  simp only [CollatzResearch.WordTrace]
  refine ⟨124629103972709366660479399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166172138630279155547305865 124629103972709366660479399)
  ·
    refine ⟨186943655959064049990719099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124629103972709366660479399 186943655959064049990719099)
    ·
      refine ⟨280415483938596074986078649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186943655959064049990719099 280415483938596074986078649)
      ·
        refine ⟨210311612953947056239558987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280415483938596074986078649 210311612953947056239558987)
        ·
          refine ⟨315467419430920584359338481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210311612953947056239558987 315467419430920584359338481)
          ·
            refine ⟨236600564573190438269503861, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315467419430920584359338481 236600564573190438269503861)
            ·
              refine ⟨22181302928736603587765987, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 236600564573190438269503861 22181302928736603587765987)
              ·
                refine ⟨33271954393104905381648981, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22181302928736603587765987 33271954393104905381648981)
                ·
                  refine ⟨389905715544198109941199, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 8 33271954393104905381648981 389905715544198109941199)
                  ·
                    rfl

theorem cell23_6834048_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 1, 2, 5, 1, 8].length) (baseStart_6834048 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834048 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834048 prefixEnd_6834048 := by exact prefixLift 6834048
  have htrace : WordTrace (prefixWord ++ tailWord_6834048) baseStart_6834048 baseEnd_6834048 := by
    simpa [prefixWord, tailWord_6834048, baseEnd_6834048] using wordTrace_append hprefix tailTrace_6834048
  have hstable : (prefixWord ++ tailWord_6834048).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834048).length < 2 ^ (prefixWord ++ tailWord_6834048).sum := by decide
  have hdescent : baseEnd_6834048 < baseStart_6834048 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834048) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834095 : List Nat := [1, 1, 2, 1, 2, 2, 3, 5, 1, 5]
def baseStart_6834095 : Nat := 118140960795 + 6834095 * 2 ^ 59
def prefixEnd_6834095 : Nat := 4983230072969 + 3 ^ 40 * 6834095 * 2
def baseEnd_6834095 : Nat := 1169725191162848101861025

theorem tailTrace_6834095 : CollatzResearch.WordTrace tailWord_6834095 prefixEnd_6834095 1169725191162848101861025 := by
  unfold tailWord_6834095
  simp only [CollatzResearch.WordTrace]
  refine ⟨249259922176248460347919739, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166173281450832306898613159 249259922176248460347919739)
  ·
    refine ⟨373889883264372690521879609, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249259922176248460347919739 373889883264372690521879609)
    ·
      refine ⟨280417412448279517891409707, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373889883264372690521879609 280417412448279517891409707)
      ·
        refine ⟨420626118672419276837114561, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280417412448279517891409707 420626118672419276837114561)
        ·
          refine ⟨315469589004314457627835921, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420626118672419276837114561 315469589004314457627835921)
          ·
            refine ⟨236602191753235843220876941, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315469589004314457627835921 236602191753235843220876941)
            ·
              refine ⟨88725821907463441207828853, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236602191753235843220876941 88725821907463441207828853)
              ·
                refine ⟨8318045803824697613233955, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 88725821907463441207828853 8318045803824697613233955)
                ·
                  refine ⟨12477068705737046419850933, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8318045803824697613233955 12477068705737046419850933)
                  ·
                    refine ⟨1169725191162848101861025, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12477068705737046419850933 1169725191162848101861025)
                    ·
                      rfl

theorem cell23_6834095_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 2, 3, 5, 1, 5].length) (baseStart_6834095 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834095 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834095 prefixEnd_6834095 := by exact prefixLift 6834095
  have htrace : WordTrace (prefixWord ++ tailWord_6834095) baseStart_6834095 baseEnd_6834095 := by
    simpa [prefixWord, tailWord_6834095, baseEnd_6834095] using wordTrace_append hprefix tailTrace_6834095
  have hstable : (prefixWord ++ tailWord_6834095).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834095).length < 2 ^ (prefixWord ++ tailWord_6834095).sum := by decide
  have hdescent : baseEnd_6834095 < baseStart_6834095 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834095) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834109 : List Nat := [1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 3]
def baseStart_6834109 : Nat := 118140960795 + 6834109 * 2 ^ 59
def prefixEnd_6834109 : Nat := 4983230072969 + 3 ^ 40 * 6834109 * 2
def baseEnd_6834109 : Nat := 3509182762217707250808011

theorem tailTrace_6834109 : CollatzResearch.WordTrace tailWord_6834109 prefixEnd_6834109 3509182762217707250808011 := by
  unfold tailWord_6834109
  simp only [CollatzResearch.WordTrace]
  refine ⟨249260432798197740738929381, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166173621865465160492619587 249260432798197740738929381)
  ·
    refine ⟨46736331149662076388549259, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249260432798197740738929381 46736331149662076388549259)
    ·
      refine ⟨70104496724493114582823889, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46736331149662076388549259 70104496724493114582823889)
      ·
        refine ⟨52578372543369835937117917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70104496724493114582823889 52578372543369835937117917)
        ·
          refine ⟨19716889703763688476419219, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52578372543369835937117917 19716889703763688476419219)
          ·
            refine ⟨29575334555645532714628829, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19716889703763688476419219 29575334555645532714628829)
            ·
              refine ⟨11090750458367074767985811, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29575334555645532714628829 11090750458367074767985811)
              ·
                refine ⟨16636125687550612151978717, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11090750458367074767985811 16636125687550612151978717)
                ·
                  refine ⟨6238547132831479556992019, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16636125687550612151978717 6238547132831479556992019)
                  ·
                    refine ⟨9357820699247219335488029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238547132831479556992019 9357820699247219335488029)
                    ·
                      refine ⟨3509182762217707250808011, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357820699247219335488029 3509182762217707250808011)
                      ·
                        rfl

theorem cell23_6834109_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 1, 2, 3, 1, 3, 1, 3, 1, 3].length) (baseStart_6834109 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834109 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834109 prefixEnd_6834109 := by exact prefixLift 6834109
  have htrace : WordTrace (prefixWord ++ tailWord_6834109) baseStart_6834109 baseEnd_6834109 := by
    simpa [prefixWord, tailWord_6834109, baseEnd_6834109] using wordTrace_append hprefix tailTrace_6834109
  have hstable : (prefixWord ++ tailWord_6834109).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834109).length < 2 ^ (prefixWord ++ tailWord_6834109).sum := by decide
  have hdescent : baseEnd_6834109 < baseStart_6834109 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834109) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834132 : List Nat := [2, 4, 1, 2, 1, 1, 3, 1, 3, 1, 4]
def baseStart_6834132 : Nat := 118140960795 + 6834132 * 2 ^ 59
def prefixEnd_6834132 : Nat := 4983230072969 + 3 ^ 40 * 6834132 * 2
def baseEnd_6834132 : Nat := 3509194572272760660820405

theorem tailTrace_6834132 : CollatzResearch.WordTrace tailWord_6834132 prefixEnd_6834132 3509194572272760660820405 := by
  unfold tailWord_6834132
  simp only [CollatzResearch.WordTrace]
  refine ⟨124630635838557207833508325, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166174181118076277111344433 124630635838557207833508325)
  ·
    refine ⟨23368244219729476468782811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 124630635838557207833508325 23368244219729476468782811)
    ·
      refine ⟨35052366329594214703174217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23368244219729476468782811 35052366329594214703174217)
      ·
        refine ⟨26289274747195661027380663, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35052366329594214703174217 26289274747195661027380663)
        ·
          refine ⟨39433912120793491541070995, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26289274747195661027380663 39433912120793491541070995)
          ·
            refine ⟨59150868181190237311606493, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39433912120793491541070995 59150868181190237311606493)
            ·
              refine ⟨22181575567946338991852435, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59150868181190237311606493 22181575567946338991852435)
              ·
                refine ⟨33272363351919508487778653, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22181575567946338991852435 33272363351919508487778653)
                ·
                  refine ⟨12477136256969815682916995, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33272363351919508487778653 12477136256969815682916995)
                  ·
                    refine ⟨18715704385454723524375493, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12477136256969815682916995 18715704385454723524375493)
                    ·
                      refine ⟨3509194572272760660820405, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18715704385454723524375493 3509194572272760660820405)
                      ·
                        rfl

theorem cell23_6834132_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 4, 1, 2, 1, 1, 3, 1, 3, 1, 4].length) (baseStart_6834132 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834132 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834132 prefixEnd_6834132 := by exact prefixLift 6834132
  have htrace : WordTrace (prefixWord ++ tailWord_6834132) baseStart_6834132 baseEnd_6834132 := by
    simpa [prefixWord, tailWord_6834132, baseEnd_6834132] using wordTrace_append hprefix tailTrace_6834132
  have hstable : (prefixWord ++ tailWord_6834132).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834132).length < 2 ^ (prefixWord ++ tailWord_6834132).sum := by decide
  have hdescent : baseEnd_6834132 < baseStart_6834132 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834132) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834145 : List Nat := [1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 4]
def baseStart_6834145 : Nat := 118140960795 + 6834145 * 2 ^ 59
def prefixEnd_6834145 : Nat := 4983230072969 + 3 ^ 40 * 6834145 * 2
def baseEnd_6834145 : Nat := 3509201247521269109957845

theorem tailTrace_6834145 : CollatzResearch.WordTrace tailWord_6834145 prefixEnd_6834145 3509201247521269109957845 := by
  unfold tailWord_6834145
  simp only [CollatzResearch.WordTrace]
  refine ⟨249261745826067318887239889, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166174497217378212591493259 249261745826067318887239889)
  ·
    refine ⟨186946309369550489165429917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249261745826067318887239889 186946309369550489165429917)
    ·
      refine ⟨70104866013581433437036219, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 186946309369550489165429917 70104866013581433437036219)
      ·
        refine ⟨105157299020372150155554329, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70104866013581433437036219 105157299020372150155554329)
        ·
          refine ⟨78867974265279112616665747, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105157299020372150155554329 78867974265279112616665747)
          ·
            refine ⟨118301961397918668924998621, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78867974265279112616665747 118301961397918668924998621)
            ·
              refine ⟨44363235524219500846874483, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118301961397918668924998621 44363235524219500846874483)
              ·
                refine ⟨66544853286329251270311725, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44363235524219500846874483 66544853286329251270311725)
                ·
                  refine ⟨24954319982373469226366897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66544853286329251270311725 24954319982373469226366897)
                  ·
                    refine ⟨18715739986780101919775173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24954319982373469226366897 18715739986780101919775173)
                    ·
                      refine ⟨3509201247521269109957845, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18715739986780101919775173 3509201247521269109957845)
                      ·
                        rfl

theorem cell23_6834145_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 3, 1, 2, 1, 3, 1, 3, 2, 4].length) (baseStart_6834145 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834145 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834145 prefixEnd_6834145 := by exact prefixLift 6834145
  have htrace : WordTrace (prefixWord ++ tailWord_6834145) baseStart_6834145 baseEnd_6834145 := by
    simpa [prefixWord, tailWord_6834145, baseEnd_6834145] using wordTrace_append hprefix tailTrace_6834145
  have hstable : (prefixWord ++ tailWord_6834145).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834145).length < 2 ^ (prefixWord ++ tailWord_6834145).sum := by decide
  have hdescent : baseEnd_6834145 < baseStart_6834145 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834145) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834233 : List Nat := [1, 2, 1, 5, 3, 1, 3, 1, 2, 1, 3]
def baseStart_6834233 : Nat := 118140960795 + 6834233 * 2 ^ 59
def prefixEnd_6834233 : Nat := 4983230072969 + 3 ^ 40 * 6834233 * 2
def baseEnd_6834233 : Nat := 3509246433818864765657441

theorem tailTrace_6834233 : CollatzResearch.WordTrace tailWord_6834233 prefixEnd_6834233 3509246433818864765657441 := by
  unfold tailWord_6834233
  simp only [CollatzResearch.WordTrace]
  refine ⟨249264955449748509916443353, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166176636966499006610962235 249264955449748509916443353)
  ·
    refine ⟨186948716587311382437332515, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249264955449748509916443353 186948716587311382437332515)
    ·
      refine ⟨280423074880967073655998773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186948716587311382437332515 280423074880967073655998773)
      ·
        refine ⟨26289663270090663155249885, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 280423074880967073655998773 26289663270090663155249885)
        ·
          refine ⟨9858623726283998683218707, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26289663270090663155249885 9858623726283998683218707)
          ·
            refine ⟨14787935589425998024828061, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858623726283998683218707 14787935589425998024828061)
            ·
              refine ⟨5545475846034749259310523, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14787935589425998024828061 5545475846034749259310523)
              ·
                refine ⟨8318213769052123888965785, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545475846034749259310523 8318213769052123888965785)
                ·
                  refine ⟨6238660326789092916724339, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8318213769052123888965785 6238660326789092916724339)
                  ·
                    refine ⟨9357990490183639375086509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238660326789092916724339 9357990490183639375086509)
                    ·
                      refine ⟨3509246433818864765657441, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9357990490183639375086509 3509246433818864765657441)
                      ·
                        rfl

theorem cell23_6834233_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 5, 3, 1, 3, 1, 2, 1, 3].length) (baseStart_6834233 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834233 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834233 prefixEnd_6834233 := by exact prefixLift 6834233
  have htrace : WordTrace (prefixWord ++ tailWord_6834233) baseStart_6834233 baseEnd_6834233 := by
    simpa [prefixWord, tailWord_6834233, baseEnd_6834233] using wordTrace_append hprefix tailTrace_6834233
  have hstable : (prefixWord ++ tailWord_6834233).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834233).length < 2 ^ (prefixWord ++ tailWord_6834233).sum := by decide
  have hdescent : baseEnd_6834233 < baseStart_6834233 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834233) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834239 : List Nat := [1, 1, 2, 2, 3, 1, 5, 1, 1, 4, 2]
def baseStart_6834239 : Nat := 118140960795 + 6834239 * 2 ^ 59
def prefixEnd_6834239 : Nat := 4983230072969 + 3 ^ 40 * 6834239 * 2
def baseEnd_6834239 : Nat := 3509249514702791742182413

theorem tailTrace_6834239 : CollatzResearch.WordTrace tailWord_6834239 prefixEnd_6834239 3509249514702791742182413 := by
  unfold tailWord_6834239
  simp only [CollatzResearch.WordTrace]
  refine ⟨249265174287726772941161771, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166176782858484515294107847 249265174287726772941161771)
  ·
    refine ⟨373897761431590159411742657, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249265174287726772941161771 373897761431590159411742657)
    ·
      refine ⟨280423321073692619558806993, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373897761431590159411742657 280423321073692619558806993)
      ·
        refine ⟨210317490805269464669105245, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280423321073692619558806993 210317490805269464669105245)
        ·
          refine ⟨78869059051976049250914467, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210317490805269464669105245 78869059051976049250914467)
          ·
            refine ⟨118303588577964073876371701, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78869059051976049250914467 118303588577964073876371701)
            ·
              refine ⟨11090961429184131925909847, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118303588577964073876371701 11090961429184131925909847)
              ·
                refine ⟨16636442143776197888864771, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11090961429184131925909847 16636442143776197888864771)
                ·
                  refine ⟨24954663215664296833297157, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16636442143776197888864771 24954663215664296833297157)
                  ·
                    refine ⟨4678999352937055656243217, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24954663215664296833297157 4678999352937055656243217)
                    ·
                      refine ⟨3509249514702791742182413, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4678999352937055656243217 3509249514702791742182413)
                      ·
                        rfl

theorem cell23_6834239_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 3, 1, 5, 1, 1, 4, 2].length) (baseStart_6834239 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834239 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834239 prefixEnd_6834239 := by exact prefixLift 6834239
  have htrace : WordTrace (prefixWord ++ tailWord_6834239) baseStart_6834239 baseEnd_6834239 := by
    simpa [prefixWord, tailWord_6834239, baseEnd_6834239] using wordTrace_append hprefix tailTrace_6834239
  have hstable : (prefixWord ++ tailWord_6834239).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834239).length < 2 ^ (prefixWord ++ tailWord_6834239).sum := by decide
  have hdescent : baseEnd_6834239 < baseStart_6834239 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834239) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834290 : List Nat := [3, 2, 1, 2, 2, 4, 2, 1, 2, 2, 2]
def baseStart_6834290 : Nat := 118140960795 + 6834290 * 2 ^ 59
def prefixEnd_6834290 : Nat := 4983230072969 + 3 ^ 40 * 6834290 * 2
def baseEnd_6834290 : Nat := 3509275702216171042644679

theorem tailTrace_6834290 : CollatzResearch.WordTrace tailWord_6834290 prefixEnd_6834290 3509275702216171042644679 := by
  unfold tailWord_6834290
  simp only [CollatzResearch.WordTrace]
  refine ⟨62316758602635502162817081, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166178022940361339100845549 62316758602635502162817081)
  ·
    refine ⟨46737568951976626622112811, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62316758602635502162817081 46737568951976626622112811)
    ·
      refine ⟨70106353427964939933169217, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46737568951976626622112811 70106353427964939933169217)
      ·
        refine ⟨52579765070973704949876913, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70106353427964939933169217 52579765070973704949876913)
        ·
          refine ⟨39434823803230278712407685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52579765070973704949876913 39434823803230278712407685)
          ·
            refine ⟨7394029463105677258576441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39434823803230278712407685 7394029463105677258576441)
            ·
              refine ⟨5545522097329257943932331, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394029463105677258576441 5545522097329257943932331)
              ·
                refine ⟨8318283145993886915898497, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545522097329257943932331 8318283145993886915898497)
                ·
                  refine ⟨6238712359495415186923873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8318283145993886915898497 6238712359495415186923873)
                  ·
                    refine ⟨4679034269621561390192905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6238712359495415186923873 4679034269621561390192905)
                    ·
                      refine ⟨3509275702216171042644679, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679034269621561390192905 3509275702216171042644679)
                      ·
                        rfl

theorem cell23_6834290_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 4, 2, 1, 2, 2, 2].length) (baseStart_6834290 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834290 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834290 prefixEnd_6834290 := by exact prefixLift 6834290
  have htrace : WordTrace (prefixWord ++ tailWord_6834290) baseStart_6834290 baseEnd_6834290 := by
    simpa [prefixWord, tailWord_6834290, baseEnd_6834290] using wordTrace_append hprefix tailTrace_6834290
  have hstable : (prefixWord ++ tailWord_6834290).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834290).length < 2 ^ (prefixWord ++ tailWord_6834290).sum := by decide
  have hdescent : baseEnd_6834290 < baseStart_6834290 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834290) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834309 : List Nat := [1, 3, 1, 1, 5, 2, 2, 1, 2, 5]
def baseStart_6834309 : Nat := 118140960795 + 6834309 * 2 ^ 59
def prefixEnd_6834309 : Nat := 4983230072969 + 3 ^ 40 * 6834309 * 2
def baseEnd_6834309 : Nat := 1169761819449535489435697

theorem tailTrace_6834309 : CollatzResearch.WordTrace tailWord_6834309 prefixEnd_6834309 1169761819449535489435697 := by
  unfold tailWord_6834309
  simp only [CollatzResearch.WordTrace]
  refine ⟨249267727397473174896209981, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166178484931648783264139987 249267727397473174896209981)
  ·
    refine ⟨93475397774052440586078743, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249267727397473174896209981 93475397774052440586078743)
    ·
      refine ⟨140213096661078660879118115, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93475397774052440586078743 140213096661078660879118115)
      ·
        refine ⟨210319644991617991318677173, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140213096661078660879118115 210319644991617991318677173)
        ·
          refine ⟨19717466717964186686125985, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 5 210319644991617991318677173 19717466717964186686125985)
          ·
            refine ⟨14788100038473140014594489, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19717466717964186686125985 14788100038473140014594489)
            ·
              refine ⟨11091075028854855010945867, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 14788100038473140014594489 11091075028854855010945867)
              ·
                refine ⟨16636612543282282516418801, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11091075028854855010945867 16636612543282282516418801)
                ·
                  refine ⟨12477459407461711887314101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16636612543282282516418801 12477459407461711887314101)
                  ·
                    refine ⟨1169761819449535489435697, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12477459407461711887314101 1169761819449535489435697)
                    ·
                      rfl

theorem cell23_6834309_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 5, 2, 2, 1, 2, 5].length) (baseStart_6834309 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834309 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834309 prefixEnd_6834309 := by exact prefixLift 6834309
  have htrace : WordTrace (prefixWord ++ tailWord_6834309) baseStart_6834309 baseEnd_6834309 := by
    simpa [prefixWord, tailWord_6834309, baseEnd_6834309] using wordTrace_append hprefix tailTrace_6834309
  have hstable : (prefixWord ++ tailWord_6834309).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834309).length < 2 ^ (prefixWord ++ tailWord_6834309).sum := by decide
  have hdescent : baseEnd_6834309 < baseStart_6834309 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834309) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834315 : List Nat := [1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9]
def baseStart_6834315 : Nat := 118140960795 + 6834315 * 2 ^ 59
def prefixEnd_6834315 : Nat := 4983230072969 + 3 ^ 40 * 6834315 * 2
def baseEnd_6834315 : Nat := 3509288539232533444832063

theorem tailTrace_6834315 : CollatzResearch.WordTrace tailWord_6834315 prefixEnd_6834315 3509288539232533444832063 := by
  unfold tailWord_6834315
  simp only [CollatzResearch.WordTrace]
  refine ⟨249267946235451437920928399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166178630823634291947285599 249267946235451437920928399)
  ·
    refine ⟨373901919353177156881392599, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249267946235451437920928399 373901919353177156881392599)
    ·
      refine ⟨560852879029765735322088899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373901919353177156881392599 560852879029765735322088899)
      ·
        refine ⟨841279318544648602983133349, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560852879029765735322088899 841279318544648602983133349)
        ·
          refine ⟨157739872227121613059337503, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 841279318544648602983133349 157739872227121613059337503)
          ·
            refine ⟨236609808340682419589006255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157739872227121613059337503 236609808340682419589006255)
            ·
              refine ⟨354914712511023629383509383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236609808340682419589006255 354914712511023629383509383)
              ·
                refine ⟨532372068766535444075264075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354914712511023629383509383 532372068766535444075264075)
                ·
                  refine ⟨798558103149803166112896113, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 532372068766535444075264075 798558103149803166112896113)
                  ·
                    refine ⟨598918577362352374584672085, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 798558103149803166112896113 598918577362352374584672085)
                    ·
                      refine ⟨3509288539232533444832063, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 9 598918577362352374584672085 3509288539232533444832063)
                      ·
                        rfl

theorem cell23_6834315_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 1, 1, 1, 1, 2, 9].length) (baseStart_6834315 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834315 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834315 prefixEnd_6834315 := by exact prefixLift 6834315
  have htrace : WordTrace (prefixWord ++ tailWord_6834315) baseStart_6834315 baseEnd_6834315 := by
    simpa [prefixWord, tailWord_6834315, baseEnd_6834315] using wordTrace_append hprefix tailTrace_6834315
  have hstable : (prefixWord ++ tailWord_6834315).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834315).length < 2 ^ (prefixWord ++ tailWord_6834315).sum := by decide
  have hdescent : baseEnd_6834315 < baseStart_6834315 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834315) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834330 : List Nat := [3, 1, 1, 5, 3, 1, 2, 2, 5]
def baseStart_6834330 : Nat := 118140960795 + 6834330 * 2 ^ 59
def prefixEnd_6834330 : Nat := 4983230072969 + 3 ^ 40 * 6834330 * 2
def baseEnd_6834330 : Nat := 389921804604705654016055

theorem tailTrace_6834330 : CollatzResearch.WordTrace tailWord_6834330 prefixEnd_6834330 389921804604705654016055 := by
  unfold tailWord_6834330
  simp only [CollatzResearch.WordTrace]
  refine ⟨62317123332599273870681111, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166178995553598063655149629 62317123332599273870681111)
  ·
    refine ⟨93475684998898910806021667, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62317123332599273870681111 93475684998898910806021667)
    ·
      refine ⟨140213527498348366209032501, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93475684998898910806021667 140213527498348366209032501)
      ·
        refine ⟨13145018202970159332096797, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 5 140213527498348366209032501 13145018202970159332096797)
        ·
          refine ⟨4929381826113809749536299, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13145018202970159332096797 4929381826113809749536299)
          ·
            refine ⟨7394072739170714624304449, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929381826113809749536299 7394072739170714624304449)
            ·
              refine ⟨5545554554378035968228337, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394072739170714624304449 5545554554378035968228337)
              ·
                refine ⟨4159165915783526976171253, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5545554554378035968228337 4159165915783526976171253)
                ·
                  refine ⟨389921804604705654016055, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4159165915783526976171253 389921804604705654016055)
                  ·
                    rfl

theorem cell23_6834330_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 1, 5, 3, 1, 2, 2, 5].length) (baseStart_6834330 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834330 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834330 prefixEnd_6834330 := by exact prefixLift 6834330
  have htrace : WordTrace (prefixWord ++ tailWord_6834330) baseStart_6834330 baseEnd_6834330 := by
    simpa [prefixWord, tailWord_6834330, baseEnd_6834330] using wordTrace_append hprefix tailTrace_6834330
  have hstable : (prefixWord ++ tailWord_6834330).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834330).length < 2 ^ (prefixWord ++ tailWord_6834330).sum := by decide
  have hdescent : baseEnd_6834330 < baseStart_6834330 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834330) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834332 : List Nat := [2, 2, 3, 2, 1, 1, 1, 1, 2, 3, 5]
def baseStart_6834332 : Nat := 118140960795 + 6834332 * 2 ^ 59
def prefixEnd_6834332 : Nat := 4983230072969 + 3 ^ 40 * 6834332 * 2
def baseEnd_6834332 : Nat := 3509297268403659878319485

theorem tailTrace_6834332 : CollatzResearch.WordTrace tailWord_6834332 prefixEnd_6834332 3509297268403659878319485 := by
  unfold tailWord_6834332
  simp only [CollatzResearch.WordTrace]
  refine ⟨124634283138194924912148625, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166179044184259899882864833 124634283138194924912148625)
  ·
    refine ⟨93475712353646193684111469, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124634283138194924912148625 93475712353646193684111469)
    ·
      refine ⟨35053392132617322631541801, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93475712353646193684111469 35053392132617322631541801)
      ·
        refine ⟨26290044099462991973656351, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35053392132617322631541801 26290044099462991973656351)
        ·
          refine ⟨39435066149194487960484527, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26290044099462991973656351 39435066149194487960484527)
          ·
            refine ⟨59152599223791731940726791, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39435066149194487960484527 59152599223791731940726791)
            ·
              refine ⟨88728898835687597911090187, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59152599223791731940726791 88728898835687597911090187)
              ·
                refine ⟨133093348253531396866635281, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88728898835687597911090187 133093348253531396866635281)
                ·
                  refine ⟨99820011190148547649976461, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133093348253531396866635281 99820011190148547649976461)
                  ·
                    refine ⟨37432504196305705368741173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 99820011190148547649976461 37432504196305705368741173)
                    ·
                      refine ⟨3509297268403659878319485, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37432504196305705368741173 3509297268403659878319485)
                      ·
                        rfl

theorem cell23_6834332_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 2, 1, 1, 1, 1, 2, 3, 5].length) (baseStart_6834332 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834332 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834332 prefixEnd_6834332 := by exact prefixLift 6834332
  have htrace : WordTrace (prefixWord ++ tailWord_6834332) baseStart_6834332 baseEnd_6834332 := by
    simpa [prefixWord, tailWord_6834332, baseEnd_6834332] using wordTrace_append hprefix tailTrace_6834332
  have hstable : (prefixWord ++ tailWord_6834332).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834332).length < 2 ^ (prefixWord ++ tailWord_6834332).sum := by decide
  have hdescent : baseEnd_6834332 < baseStart_6834332 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834332) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834366 : List Nat := [4, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3]
def baseStart_6834366 : Nat := 118140960795 + 6834366 * 2 ^ 59
def prefixEnd_6834366 : Nat := 4983230072969 + 3 ^ 40 * 6834366 * 2
def baseEnd_6834366 : Nat := 3509314726745912745294329

theorem tailTrace_6834366 : CollatzResearch.WordTrace tailWord_6834366 prefixEnd_6834366 3509314726745912745294329 := by
  unfold tailWord_6834366
  simp only [CollatzResearch.WordTrace]
  refine ⟨31158725794783334203879369, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166179870905511115754023301 31158725794783334203879369)
  ·
    refine ⟨23369044346087500652909527, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 31158725794783334203879369 23369044346087500652909527)
    ·
      refine ⟨35053566519131250979364291, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23369044346087500652909527 35053566519131250979364291)
      ·
        refine ⟨52580349778696876469046437, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35053566519131250979364291 52580349778696876469046437)
        ·
          refine ⟨9858815583505664337946207, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 52580349778696876469046437 9858815583505664337946207)
          ·
            refine ⟨14788223375258496506919311, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858815583505664337946207 14788223375258496506919311)
            ·
              refine ⟨22182335062887744760378967, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788223375258496506919311 22182335062887744760378967)
              ·
                refine ⟨33273502594331617140568451, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22182335062887744760378967 33273502594331617140568451)
                ·
                  refine ⟨49910253891497425710852677, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33273502594331617140568451 49910253891497425710852677)
                  ·
                    refine ⟨9358172604655767320784877, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49910253891497425710852677 9358172604655767320784877)
                    ·
                      refine ⟨3509314726745912745294329, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358172604655767320784877 3509314726745912745294329)
                      ·
                        rfl

theorem cell23_6834366_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 2, 1, 1, 4, 1, 1, 1, 1, 4, 3].length) (baseStart_6834366 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834366 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834366 prefixEnd_6834366 := by exact prefixLift 6834366
  have htrace : WordTrace (prefixWord ++ tailWord_6834366) baseStart_6834366 baseEnd_6834366 := by
    simpa [prefixWord, tailWord_6834366, baseEnd_6834366] using wordTrace_append hprefix tailTrace_6834366
  have hstable : (prefixWord ++ tailWord_6834366).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834366).length < 2 ^ (prefixWord ++ tailWord_6834366).sum := by decide
  have hdescent : baseEnd_6834366 < baseStart_6834366 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834366) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834379 : List Nat := [1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 3]
def baseStart_6834379 : Nat := 118140960795 + 6834379 * 2 ^ 59
def prefixEnd_6834379 : Nat := 4983230072969 + 3 ^ 40 * 6834379 * 2
def baseEnd_6834379 : Nat := 3509321401994421194431769

theorem tailTrace_6834379 : CollatzResearch.WordTrace tailWord_6834379 prefixEnd_6834379 3509321401994421194431769 := by
  unfold tailWord_6834379
  simp only [CollatzResearch.WordTrace]
  refine ⟨249270280507219576851258191, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166180187004813051234172127 249270280507219576851258191)
  ·
    refine ⟨373905420760829365276887287, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249270280507219576851258191 373905420760829365276887287)
    ·
      refine ⟨560858131141244047915330931, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373905420760829365276887287 560858131141244047915330931)
      ·
        refine ⟨841287196711866071872996397, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560858131141244047915330931 841287196711866071872996397)
        ·
          refine ⟨315482698766949776952373649, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 841287196711866071872996397 315482698766949776952373649)
          ·
            refine ⟨236612024075212332714280237, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 315482698766949776952373649 236612024075212332714280237)
            ·
              refine ⟨88729509028204624767855089, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 236612024075212332714280237 88729509028204624767855089)
              ·
                refine ⟨66547131771153468575891317, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88729509028204624767855089 66547131771153468575891317)
                ·
                  refine ⟨6238793603545637678989811, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66547131771153468575891317 6238793603545637678989811)
                  ·
                    refine ⟨9358190405318456518484717, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238793603545637678989811 9358190405318456518484717)
                    ·
                      refine ⟨3509321401994421194431769, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358190405318456518484717 3509321401994421194431769)
                      ·
                        rfl

theorem cell23_6834379_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 3, 2, 3, 2, 5, 1, 3].length) (baseStart_6834379 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834379 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834379 prefixEnd_6834379 := by exact prefixLift 6834379
  have htrace : WordTrace (prefixWord ++ tailWord_6834379) baseStart_6834379 baseEnd_6834379 := by
    simpa [prefixWord, tailWord_6834379, baseEnd_6834379] using wordTrace_append hprefix tailTrace_6834379
  have hstable : (prefixWord ++ tailWord_6834379).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834379).length < 2 ^ (prefixWord ++ tailWord_6834379).sum := by decide
  have hdescent : baseEnd_6834379 < baseStart_6834379 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834379) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834386 : List Nat := [3, 2, 2, 2, 1, 4, 1, 2, 6]
def baseStart_6834386 : Nat := 118140960795 + 6834386 * 2 ^ 59
def prefixEnd_6834386 : Nat := 4983230072969 + 3 ^ 40 * 6834386 * 2
def baseEnd_6834386 : Nat := 389924999595444740782693

theorem tailTrace_6834386 : CollatzResearch.WordTrace tailWord_6834386 prefixEnd_6834386 389924999595444740782693 := by
  unfold tailWord_6834386
  simp only [CollatzResearch.WordTrace]
  refine ⟨62317633954548554261690753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166180357212129478031175341 62317633954548554261690753)
  ·
    refine ⟨46738225465911415696268065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62317633954548554261690753 46738225465911415696268065)
    ·
      refine ⟨35053669099433561772201049, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46738225465911415696268065 35053669099433561772201049)
      ·
        refine ⟨26290251824575171329150787, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35053669099433561772201049 26290251824575171329150787)
        ·
          refine ⟨39435377736862756993726181, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26290251824575171329150787 39435377736862756993726181)
          ·
            refine ⟨7394133325661766936323659, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39435377736862756993726181 7394133325661766936323659)
            ·
              refine ⟨11091199988492650404485489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394133325661766936323659 11091199988492650404485489)
              ·
                refine ⟨8318399991369487803364117, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11091199988492650404485489 8318399991369487803364117)
                ·
                  refine ⟨389924999595444740782693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8318399991369487803364117 389924999595444740782693)
                  ·
                    rfl

theorem cell23_6834386_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 1, 4, 1, 2, 6].length) (baseStart_6834386 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834386 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834386 prefixEnd_6834386 := by exact prefixLift 6834386
  have htrace : WordTrace (prefixWord ++ tailWord_6834386) baseStart_6834386 baseEnd_6834386 := by
    simpa [prefixWord, tailWord_6834386, baseEnd_6834386] using wordTrace_append hprefix tailTrace_6834386
  have hstable : (prefixWord ++ tailWord_6834386).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834386).length < 2 ^ (prefixWord ++ tailWord_6834386).sum := by decide
  have hdescent : baseEnd_6834386 < baseStart_6834386 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834386) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834390 : List Nat := [5, 2, 1, 2, 1, 1, 2, 4, 1, 4]
def baseStart_6834390 : Nat := 118140960795 + 6834390 * 2 ^ 59
def prefixEnd_6834390 : Nat := 4983230072969 + 3 ^ 40 * 6834390 * 2
def baseEnd_6834390 : Nat := 1169775683427206883798073

theorem tailTrace_6834390 : CollatzResearch.WordTrace tailWord_6834390 prefixEnd_6834390 1169775683427206883798073 := by
  unfold tailWord_6834390
  simp only [CollatzResearch.WordTrace]
  refine ⟨15579417606886232858119289, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 5 166180454473453150486605749 15579417606886232858119289)
  ·
    refine ⟨11684563205164674643589467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 15579417606886232858119289 11684563205164674643589467)
    ·
      refine ⟨17526844807747011965384201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11684563205164674643589467 17526844807747011965384201)
      ·
        refine ⟨13145133605810258974038151, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 17526844807747011965384201 13145133605810258974038151)
        ·
          refine ⟨19717700408715388461057227, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13145133605810258974038151 19717700408715388461057227)
          ·
            refine ⟨29576550613073082691585841, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19717700408715388461057227 29576550613073082691585841)
            ·
              refine ⟨22182412959804812018689381, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29576550613073082691585841 22182412959804812018689381)
              ·
                refine ⟨4159202429963402253504259, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22182412959804812018689381 4159202429963402253504259)
                ·
                  refine ⟨6238803644945103380256389, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159202429963402253504259 6238803644945103380256389)
                  ·
                    refine ⟨1169775683427206883798073, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6238803644945103380256389 1169775683427206883798073)
                    ·
                      rfl

theorem cell23_6834390_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 5, 2, 1, 2, 1, 1, 2, 4, 1, 4].length) (baseStart_6834390 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834390 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834390 prefixEnd_6834390 := by exact prefixLift 6834390
  have htrace : WordTrace (prefixWord ++ tailWord_6834390) baseStart_6834390 baseEnd_6834390 := by
    simpa [prefixWord, tailWord_6834390, baseEnd_6834390] using wordTrace_append hprefix tailTrace_6834390
  have hstable : (prefixWord ++ tailWord_6834390).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834390).length < 2 ^ (prefixWord ++ tailWord_6834390).sum := by decide
  have hdescent : baseEnd_6834390 < baseStart_6834390 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834390) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834403 : List Nat := [1, 1, 1, 8, 1, 1, 3, 1, 6]
def baseStart_6834403 : Nat := 118140960795 + 6834403 * 2 ^ 59
def prefixEnd_6834403 : Nat := 4983230072969 + 3 ^ 40 * 6834403 * 2
def baseEnd_6834403 : Nat := 389925969503347677836851

theorem tailTrace_6834403 : CollatzResearch.WordTrace tailWord_6834403 prefixEnd_6834403 389925969503347677836851 := by
  unfold tailWord_6834403
  simp only [CollatzResearch.WordTrace]
  refine ⟨249271155859132628950131863, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166180770572755085966754575 249271155859132628950131863)
  ·
    refine ⟨373906733788698943425197795, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249271155859132628950131863 373906733788698943425197795)
    ·
      refine ⟨560860100683048415137796693, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373906733788698943425197795 560860100683048415137796693)
      ·
        refine ⟨6572579304879473614896055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 8 560860100683048415137796693 6572579304879473614896055)
        ·
          refine ⟨9858868957319210422344083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6572579304879473614896055 9858868957319210422344083)
          ·
            refine ⟨14788303435978815633516125, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9858868957319210422344083 14788303435978815633516125)
            ·
              refine ⟨5545613788492055862568547, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14788303435978815633516125 5545613788492055862568547)
              ·
                refine ⟨8318420682738083793852821, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545613788492055862568547 8318420682738083793852821)
                ·
                  refine ⟨389925969503347677836851, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8318420682738083793852821 389925969503347677836851)
                  ·
                    rfl

theorem cell23_6834403_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 8, 1, 1, 3, 1, 6].length) (baseStart_6834403 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834403 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834403 prefixEnd_6834403 := by exact prefixLift 6834403
  have htrace : WordTrace (prefixWord ++ tailWord_6834403) baseStart_6834403 baseEnd_6834403 := by
    simpa [prefixWord, tailWord_6834403, baseEnd_6834403] using wordTrace_append hprefix tailTrace_6834403
  have hstable : (prefixWord ++ tailWord_6834403).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834403).length < 2 ^ (prefixWord ++ tailWord_6834403).sum := by decide
  have hdescent : baseEnd_6834403 < baseStart_6834403 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834403) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834419 : List Nat := [1, 1, 1, 2, 2, 4, 1, 1, 2, 6, 2]
def baseStart_6834419 : Nat := 118140960795 + 6834419 * 2 ^ 59
def prefixEnd_6834419 : Nat := 4983230072969 + 3 ^ 40 * 6834419 * 2
def baseEnd_6834419 : Nat := 3509341941220601037931585

theorem tailTrace_6834419 : CollatzResearch.WordTrace tailWord_6834419 prefixEnd_6834419 3509341941220601037931585 := by
  unfold tailWord_6834419
  simp only [CollatzResearch.WordTrace]
  refine ⟨249271739427074663682714311, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166181159618049775788476207 249271739427074663682714311)
  ·
    refine ⟨373907609140611995524071467, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249271739427074663682714311 373907609140611995524071467)
    ·
      refine ⟨560861413710917993286107201, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373907609140611995524071467 560861413710917993286107201)
      ·
        refine ⟨420646060283188494964580401, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560861413710917993286107201 420646060283188494964580401)
        ·
          refine ⟨315484545212391371223435301, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420646060283188494964580401 315484545212391371223435301)
          ·
            refine ⟨59153352227323382104394119, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 315484545212391371223435301 59153352227323382104394119)
            ·
              refine ⟨88730028340985073156591179, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59153352227323382104394119 88730028340985073156591179)
              ·
                refine ⟨133095042511477609734886769, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 88730028340985073156591179 133095042511477609734886769)
                ·
                  refine ⟨99821281883608207301165077, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 133095042511477609734886769 99821281883608207301165077)
                  ·
                    refine ⟨4679122588294134717242113, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 99821281883608207301165077 4679122588294134717242113)
                    ·
                      refine ⟨3509341941220601037931585, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679122588294134717242113 3509341941220601037931585)
                      ·
                        rfl

theorem cell23_6834419_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 2, 4, 1, 1, 2, 6, 2].length) (baseStart_6834419 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834419 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834419 prefixEnd_6834419 := by exact prefixLift 6834419
  have htrace : WordTrace (prefixWord ++ tailWord_6834419) baseStart_6834419 baseEnd_6834419 := by
    simpa [prefixWord, tailWord_6834419, baseEnd_6834419] using wordTrace_append hprefix tailTrace_6834419
  have hstable : (prefixWord ++ tailWord_6834419).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834419).length < 2 ^ (prefixWord ++ tailWord_6834419).sum := by decide
  have hdescent : baseEnd_6834419 < baseStart_6834419 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834419) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834442 : List Nat := [3, 1, 2, 2, 1, 1, 13]
def baseStart_6834442 : Nat := 118140960795 + 6834442 * 2 ^ 59
def prefixEnd_6834442 : Nat := 4983230072969 + 3 ^ 40 * 6834442 * 2
def baseEnd_6834442 : Nat := 43325354954020425283259

theorem tailTrace_6834442 : CollatzResearch.WordTrace tailWord_6834442 prefixEnd_6834442 43325354954020425283259 := by
  unfold tailWord_6834442
  simp only [CollatzResearch.WordTrace]
  refine ⟨62318144576497834652700395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166181718870660892407201053 62318144576497834652700395)
  ·
    refine ⟨93477216864746751979050593, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62318144576497834652700395 93477216864746751979050593)
    ·
      refine ⟨70107912648560063984287945, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93477216864746751979050593 70107912648560063984287945)
      ·
        refine ⟨52580934486420047988215959, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70107912648560063984287945 52580934486420047988215959)
        ·
          refine ⟨78871401729630071982323939, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52580934486420047988215959 78871401729630071982323939)
          ·
            refine ⟨118307102594445107973485909, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78871401729630071982323939 118307102594445107973485909)
            ·
              refine ⟨43325354954020425283259, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 13 118307102594445107973485909 43325354954020425283259)
              ·
                rfl

theorem cell23_6834442_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 13].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 2, 2, 1, 1, 13].length) (baseStart_6834442 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834442 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834442 prefixEnd_6834442 := by exact prefixLift 6834442
  have htrace : WordTrace (prefixWord ++ tailWord_6834442) baseStart_6834442 baseEnd_6834442 := by
    simpa [prefixWord, tailWord_6834442, baseEnd_6834442] using wordTrace_append hprefix tailTrace_6834442
  have hstable : (prefixWord ++ tailWord_6834442).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834442).length < 2 ^ (prefixWord ++ tailWord_6834442).sum := by decide
  have hdescent : baseEnd_6834442 < baseStart_6834442 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834442) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834446 : List Nat := [4, 1, 1, 2, 1, 2, 2, 4, 2, 4]
def baseStart_6834446 : Nat := 118140960795 + 6834446 * 2 ^ 59
def prefixEnd_6834446 : Nat := 4983230072969 + 3 ^ 40 * 6834446 * 2
def baseEnd_6834446 : Nat := 1169785268399424144097987

theorem tailTrace_6834446 : CollatzResearch.WordTrace tailWord_6834446 prefixEnd_6834446 1169785268399424144097987 := by
  unfold tailWord_6834446
  simp only [CollatzResearch.WordTrace]
  refine ⟨31159090524747105911743399, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166181816131984564862631461 31159090524747105911743399)
  ·
    refine ⟨46738635787120658867615099, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31159090524747105911743399 46738635787120658867615099)
    ·
      refine ⟨70107953680680988301422649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46738635787120658867615099 70107953680680988301422649)
      ·
        refine ⟨52580965260510741226066987, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70107953680680988301422649 52580965260510741226066987)
        ·
          refine ⟨78871447890766111839100481, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52580965260510741226066987 78871447890766111839100481)
          ·
            refine ⟨59153585918074583879325361, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78871447890766111839100481 59153585918074583879325361)
            ·
              refine ⟨44365189438555937909494021, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59153585918074583879325361 44365189438555937909494021)
              ·
                refine ⟨8318473019729238358030129, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44365189438555937909494021 8318473019729238358030129)
                ·
                  refine ⟨6238854764796928768522597, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8318473019729238358030129 6238854764796928768522597)
                  ·
                    refine ⟨1169785268399424144097987, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6238854764796928768522597 1169785268399424144097987)
                    ·
                      rfl

theorem cell23_6834446_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 1, 2, 1, 2, 2, 4, 2, 4].length) (baseStart_6834446 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834446 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834446 prefixEnd_6834446 := by exact prefixLift 6834446
  have htrace : WordTrace (prefixWord ++ tailWord_6834446) baseStart_6834446 baseEnd_6834446 := by
    simpa [prefixWord, tailWord_6834446, baseEnd_6834446] using wordTrace_append hprefix tailTrace_6834446
  have hstable : (prefixWord ++ tailWord_6834446).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834446).length < 2 ^ (prefixWord ++ tailWord_6834446).sum := by decide
  have hdescent : baseEnd_6834446 < baseStart_6834446 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834446) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834453 : List Nat := [1, 3, 2, 1, 2, 1, 5, 1, 3, 2, 2]
def baseStart_6834453 : Nat := 118140960795 + 6834453 * 2 ^ 59
def prefixEnd_6834453 : Nat := 4983230072969 + 3 ^ 40 * 6834453 * 2
def baseEnd_6834453 : Nat := 3509359399562853904906429

theorem tailTrace_6834453 : CollatzResearch.WordTrace tailWord_6834453 prefixEnd_6834453 3509359399562853904906429 := by
  unfold tailWord_6834453
  simp only [CollatzResearch.WordTrace]
  refine ⟨249272979508951487489452013, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166181986339300991659634675 249272979508951487489452013)
  ·
    refine ⟨93477367315856807808544505, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249272979508951487489452013 93477367315856807808544505)
    ·
      refine ⟨70108025486892605856408379, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93477367315856807808544505 70108025486892605856408379)
      ·
        refine ⟨105162038230338908784612569, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70108025486892605856408379 105162038230338908784612569)
        ·
          refine ⟨78871528672754181588459427, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105162038230338908784612569 78871528672754181588459427)
          ·
            refine ⟨118307293009131272382689141, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78871528672754181588459427 118307293009131272382689141)
            ·
              refine ⟨11091308719606056785877107, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118307293009131272382689141 11091308719606056785877107)
              ·
                refine ⟨16636963079409085178815661, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11091308719606056785877107 16636963079409085178815661)
                ·
                  refine ⟨6238861154778406942055873, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16636963079409085178815661 6238861154778406942055873)
                  ·
                    refine ⟨4679145866083805206541905, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6238861154778406942055873 4679145866083805206541905)
                    ·
                      refine ⟨3509359399562853904906429, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679145866083805206541905 3509359399562853904906429)
                      ·
                        rfl

theorem cell23_6834453_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 1, 2, 1, 5, 1, 3, 2, 2].length) (baseStart_6834453 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834453 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834453 prefixEnd_6834453 := by exact prefixLift 6834453
  have htrace : WordTrace (prefixWord ++ tailWord_6834453) baseStart_6834453 baseEnd_6834453 := by
    simpa [prefixWord, tailWord_6834453, baseEnd_6834453] using wordTrace_append hprefix tailTrace_6834453
  have hstable : (prefixWord ++ tailWord_6834453).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834453).length < 2 ^ (prefixWord ++ tailWord_6834453).sum := by decide
  have hdescent : baseEnd_6834453 < baseStart_6834453 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834453) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834463 : List Nat := [1, 1, 2, 4, 3, 1, 4, 1, 2, 4]
def baseStart_6834463 : Nat := 118140960795 + 6834463 * 2 ^ 59
def prefixEnd_6834463 : Nat := 4983230072969 + 3 ^ 40 * 6834463 * 2
def baseEnd_6834463 : Nat := 1169788178123132955260461

theorem tailTrace_6834463 : CollatzResearch.WordTrace tailWord_6834463 prefixEnd_6834463 1169788178123132955260461 := by
  unfold tailWord_6834463
  simp only [CollatzResearch.WordTrace]
  refine ⟨249273344238915259197316043, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166182229492610172798210695 249273344238915259197316043)
  ·
    refine ⟨373910016358372888795974065, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249273344238915259197316043 373910016358372888795974065)
    ·
      refine ⟨280432512268779666596980549, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373910016358372888795974065 280432512268779666596980549)
      ·
        refine ⟨52581096050396187486933853, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280432512268779666596980549 52581096050396187486933853)
        ·
          refine ⟨19717911018898570307600195, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52581096050396187486933853 19717911018898570307600195)
          ·
            refine ⟨29576866528347855461400293, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19717911018898570307600195 29576866528347855461400293)
            ·
              refine ⟨5545662474065222899012555, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 29576866528347855461400293 5545662474065222899012555)
              ·
                refine ⟨8318493711097834348518833, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545662474065222899012555 8318493711097834348518833)
                ·
                  refine ⟨6238870283323375761389125, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8318493711097834348518833 6238870283323375761389125)
                  ·
                    refine ⟨1169788178123132955260461, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6238870283323375761389125 1169788178123132955260461)
                    ·
                      rfl

theorem cell23_6834463_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 4, 3, 1, 4, 1, 2, 4].length) (baseStart_6834463 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834463 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834463 prefixEnd_6834463 := by exact prefixLift 6834463
  have htrace : WordTrace (prefixWord ++ tailWord_6834463) baseStart_6834463 baseEnd_6834463 := by
    simpa [prefixWord, tailWord_6834463, baseEnd_6834463] using wordTrace_append hprefix tailTrace_6834463
  have hstable : (prefixWord ++ tailWord_6834463).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834463).length < 2 ^ (prefixWord ++ tailWord_6834463).sum := by decide
  have hdescent : baseEnd_6834463 < baseStart_6834463 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834463) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834503 : List Nat := [1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 3]
def baseStart_6834503 : Nat := 118140960795 + 6834503 * 2 ^ 59
def prefixEnd_6834503 : Nat := 4983230072969 + 3 ^ 40 * 6834503 * 2
def baseEnd_6834503 : Nat := 3509385073595578709281199

theorem tailTrace_6834503 : CollatzResearch.WordTrace tailWord_6834503 prefixEnd_6834503 3509385073595578709281199 := by
  unfold tailWord_6834503
  simp only [CollatzResearch.WordTrace]
  refine ⟨249274803158770346028772163, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166183202105846897352514775 249274803158770346028772163)
  ·
    refine ⟨373912204738155519043158245, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249274803158770346028772163 373912204738155519043158245)
    ·
      refine ⟨70108538388404159820592171, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373912204738155519043158245 70108538388404159820592171)
      ·
        refine ⟨105162807582606239730888257, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70108538388404159820592171 105162807582606239730888257)
        ·
          refine ⟨78872105686954679798166193, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 105162807582606239730888257 78872105686954679798166193)
          ·
            refine ⟨59154079265216009848624645, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78872105686954679798166193 59154079265216009848624645)
            ·
              refine ⟨11091389862228001846617121, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59154079265216009848624645 11091389862228001846617121)
              ·
                refine ⟨8318542396671001384962841, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11091389862228001846617121 8318542396671001384962841)
                ·
                  refine ⟨6238906797503251038722131, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8318542396671001384962841 6238906797503251038722131)
                  ·
                    refine ⟨9358360196254876558083197, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6238906797503251038722131 9358360196254876558083197)
                    ·
                      refine ⟨3509385073595578709281199, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358360196254876558083197 3509385073595578709281199)
                      ·
                        rfl

theorem cell23_6834503_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 1, 2, 2, 4, 2, 2, 1, 3].length) (baseStart_6834503 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834503 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834503 prefixEnd_6834503 := by exact prefixLift 6834503
  have htrace : WordTrace (prefixWord ++ tailWord_6834503) baseStart_6834503 baseEnd_6834503 := by
    simpa [prefixWord, tailWord_6834503, baseEnd_6834503] using wordTrace_append hprefix tailTrace_6834503
  have hstable : (prefixWord ++ tailWord_6834503).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834503).length < 2 ^ (prefixWord ++ tailWord_6834503).sum := by decide
  have hdescent : baseEnd_6834503 < baseStart_6834503 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834503) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834519 : List Nat := [1, 1, 3, 2, 3, 1, 3, 1, 2, 6]
def baseStart_6834519 : Nat := 118140960795 + 6834519 * 2 ^ 59
def prefixEnd_6834519 : Nat := 4983230072969 + 3 ^ 40 * 6834519 * 2
def baseEnd_6834519 : Nat := 1169797763095350215560375

theorem tailTrace_6834519 : CollatzResearch.WordTrace tailWord_6834519 prefixEnd_6834519 1169797763095350215560375 := by
  unfold tailWord_6834519
  simp only [CollatzResearch.WordTrace]
  refine ⟨249275386726712380761354611, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166183591151141587174236407 249275386726712380761354611)
  ·
    refine ⟨373913080090068571142031917, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249275386726712380761354611 373913080090068571142031917)
    ·
      refine ⟨140217405033775714178261969, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373913080090068571142031917 140217405033775714178261969)
      ·
        refine ⟨105163053775331785633696477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140217405033775714178261969 105163053775331785633696477)
        ·
          refine ⟨39436145165749419612636179, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105163053775331785633696477 39436145165749419612636179)
          ·
            refine ⟨59154217748624129418954269, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39436145165749419612636179 59154217748624129418954269)
            ·
              refine ⟨22182831655734048532107851, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59154217748624129418954269 22182831655734048532107851)
              ·
                refine ⟨33274247483601072798161777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22182831655734048532107851 33274247483601072798161777)
                ·
                  refine ⟨24955685612700804598621333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33274247483601072798161777 24955685612700804598621333)
                  ·
                    refine ⟨1169797763095350215560375, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 6 24955685612700804598621333 1169797763095350215560375)
                    ·
                      rfl

theorem cell23_6834519_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 2, 3, 1, 3, 1, 2, 6].length) (baseStart_6834519 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834519 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834519 prefixEnd_6834519 := by exact prefixLift 6834519
  have htrace : WordTrace (prefixWord ++ tailWord_6834519) baseStart_6834519 baseEnd_6834519 := by
    simpa [prefixWord, tailWord_6834519, baseEnd_6834519] using wordTrace_append hprefix tailTrace_6834519
  have hstable : (prefixWord ++ tailWord_6834519).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834519).length < 2 ^ (prefixWord ++ tailWord_6834519).sum := by decide
  have hdescent : baseEnd_6834519 < baseStart_6834519 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834519) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834559 : List Nat := [1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 3]
def baseStart_6834559 : Nat := 118140960795 + 6834559 * 2 ^ 59
def prefixEnd_6834559 : Nat := 4983230072969 + 3 ^ 40 * 6834559 * 2
def baseEnd_6834559 : Nat := 3509413828512230490180941

theorem tailTrace_6834559 : CollatzResearch.WordTrace tailWord_6834559 prefixEnd_6834559 3509413828512230490180941 := by
  unfold tailWord_6834559
  simp only [CollatzResearch.WordTrace]
  refine ⟨249276845646567467592810731, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166184563764378311728540487 249276845646567467592810731)
  ·
    refine ⟨373915268469851201389216097, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249276845646567467592810731 373915268469851201389216097)
    ·
      refine ⟨280436451352388401041912073, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373915268469851201389216097 280436451352388401041912073)
      ·
        refine ⟨210327338514291300781434055, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280436451352388401041912073 210327338514291300781434055)
        ·
          refine ⟨315491007771436951172151083, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210327338514291300781434055 315491007771436951172151083)
          ·
            refine ⟨473236511657155426758226625, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315491007771436951172151083 473236511657155426758226625)
            ·
              refine ⟨354927383742866570068669969, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 473236511657155426758226625 354927383742866570068669969)
              ·
                refine ⟨266195537807149927551502477, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354927383742866570068669969 266195537807149927551502477)
                ·
                  refine ⟨99823326677681222831813429, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266195537807149927551502477 99823326677681222831813429)
                  ·
                    refine ⟨9358436876032614640482509, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99823326677681222831813429 9358436876032614640482509)
                    ·
                      refine ⟨3509413828512230490180941, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358436876032614640482509 3509413828512230490180941)
                      ·
                        rfl

theorem cell23_6834559_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 2, 2, 3, 5, 3].length) (baseStart_6834559 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834559 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834559 prefixEnd_6834559 := by exact prefixLift 6834559
  have htrace : WordTrace (prefixWord ++ tailWord_6834559) baseStart_6834559 baseEnd_6834559 := by
    simpa [prefixWord, tailWord_6834559, baseEnd_6834559] using wordTrace_append hprefix tailTrace_6834559
  have hstable : (prefixWord ++ tailWord_6834559).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834559).length < 2 ^ (prefixWord ++ tailWord_6834559).sum := by decide
  have hdescent : baseEnd_6834559 < baseStart_6834559 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834559) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834600 : List Nat := [2, 1, 6, 1, 1, 1, 3, 3, 5]
def baseStart_6834600 : Nat := 118140960795 + 6834600 * 2 ^ 59
def prefixEnd_6834600 : Nat := 4983230072969 + 3 ^ 40 * 6834600 * 2
def baseEnd_6834600 : Nat := 389937209024340536640917

theorem tailTrace_6834600 : CollatzResearch.WordTrace tailWord_6834600 prefixEnd_6834600 389937209024340536640917 := by
  unfold tailWord_6834600
  simp only [CollatzResearch.WordTrace]
  refine ⟨124639170519709465797526627, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166185560692945954396702169 124639170519709465797526627)
  ·
    refine ⟨186958755779564198696289941, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124639170519709465797526627 186958755779564198696289941)
    ·
      refine ⟨8763691677167071813888591, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 6 186958755779564198696289941 8763691677167071813888591)
      ·
        refine ⟨13145537515750607720832887, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8763691677167071813888591 13145537515750607720832887)
        ·
          refine ⟨19718306273625911581249331, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13145537515750607720832887 19718306273625911581249331)
          ·
            refine ⟨29577459410438867371873997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19718306273625911581249331 29577459410438867371873997)
            ·
              refine ⟨11091547278914575264452749, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29577459410438867371873997 11091547278914575264452749)
              ·
                refine ⟨4159330229592965724169781, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 11091547278914575264452749 4159330229592965724169781)
                ·
                  refine ⟨389937209024340536640917, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 4159330229592965724169781 389937209024340536640917)
                  ·
                    rfl

theorem cell23_6834600_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 6, 1, 1, 1, 3, 3, 5].length) (baseStart_6834600 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834600 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834600 prefixEnd_6834600 := by exact prefixLift 6834600
  have htrace : WordTrace (prefixWord ++ tailWord_6834600) baseStart_6834600 baseEnd_6834600 := by
    simpa [prefixWord, tailWord_6834600, baseEnd_6834600] using wordTrace_append hprefix tailTrace_6834600
  have hstable : (prefixWord ++ tailWord_6834600).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834600).length < 2 ^ (prefixWord ++ tailWord_6834600).sum := by decide
  have hdescent : baseEnd_6834600 < baseStart_6834600 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834600) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834613 : List Nat := [1, 3, 3, 2, 3, 1, 1, 2, 2, 5]
def baseStart_6834613 : Nat := 118140960795 + 6834613 * 2 ^ 59
def prefixEnd_6834613 : Nat := 4983230072969 + 3 ^ 40 * 6834613 * 2
def baseEnd_6834613 : Nat := 1169813852155857759635231

theorem tailTrace_6834613 : CollatzResearch.WordTrace tailWord_6834613 prefixEnd_6834613 1169813852155857759635231 := by
  unfold tailWord_6834613
  simp only [CollatzResearch.WordTrace]
  refine ⟨249278815188371834815276493, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166185876792247889876850995 249278815188371834815276493)
  ·
    refine ⟨93479555695639438055728685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249278815188371834815276493 93479555695639438055728685)
    ·
      refine ⟨35054833385864789270898257, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93479555695639438055728685 35054833385864789270898257)
      ·
        refine ⟨26291125039398591953173693, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35054833385864789270898257 26291125039398591953173693)
        ·
          refine ⟨9859171889774471982440135, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26291125039398591953173693 9859171889774471982440135)
          ·
            refine ⟨14788757834661707973660203, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9859171889774471982440135 14788757834661707973660203)
            ·
              refine ⟨22183136751992561960490305, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788757834661707973660203 22183136751992561960490305)
              ·
                refine ⟨16637352563994421470367729, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22183136751992561960490305 16637352563994421470367729)
                ·
                  refine ⟨12478014422995816102775797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16637352563994421470367729 12478014422995816102775797)
                  ·
                    refine ⟨1169813852155857759635231, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12478014422995816102775797 1169813852155857759635231)
                    ·
                      rfl

theorem cell23_6834613_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 3, 2, 3, 1, 1, 2, 2, 5].length) (baseStart_6834613 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834613 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834613 prefixEnd_6834613 := by exact prefixLift 6834613
  have htrace : WordTrace (prefixWord ++ tailWord_6834613) baseStart_6834613 baseEnd_6834613 := by
    simpa [prefixWord, tailWord_6834613, baseEnd_6834613] using wordTrace_append hprefix tailTrace_6834613
  have hstable : (prefixWord ++ tailWord_6834613).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834613).length < 2 ^ (prefixWord ++ tailWord_6834613).sum := by decide
  have hdescent : baseEnd_6834613 < baseStart_6834613 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834613) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834693 : List Nat := [1, 3, 1, 1, 2, 2, 2, 2, 4, 3, 2]
def baseStart_6834693 : Nat := 118140960795 + 6834693 * 2 ^ 59
def prefixEnd_6834693 : Nat := 4983230072969 + 3 ^ 40 * 6834693 * 2
def baseEnd_6834693 : Nat := 3509482634919932965905325

theorem tailTrace_6834693 : CollatzResearch.WordTrace tailWord_6834693 prefixEnd_6834693 3509482634919932965905325 := by
  unfold tailWord_6834693
  simp only [CollatzResearch.WordTrace]
  refine ⟨249281733028082008478188733, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166187822018721338985459155 249281733028082008478188733)
  ·
    refine ⟨93480649885530753179320775, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249281733028082008478188733 93480649885530753179320775)
    ·
      refine ⟨140220974828296129768981163, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93480649885530753179320775 140220974828296129768981163)
      ·
        refine ⟨210331462242444194653471745, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140220974828296129768981163 210331462242444194653471745)
        ·
          refine ⟨157748596681833145990103809, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210331462242444194653471745 157748596681833145990103809)
          ·
            refine ⟨118311447511374859492577857, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157748596681833145990103809 118311447511374859492577857)
            ·
              refine ⟨88733585633531144619433393, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118311447511374859492577857 88733585633531144619433393)
              ·
                refine ⟨66550189225148358464575045, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88733585633531144619433393 66550189225148358464575045)
                ·
                  refine ⟨12478160479715317212107821, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 4 66550189225148358464575045 12478160479715317212107821)
                  ·
                    refine ⟨4679310179893243954540433, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12478160479715317212107821 4679310179893243954540433)
                    ·
                      refine ⟨3509482634919932965905325, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679310179893243954540433 3509482634919932965905325)
                      ·
                        rfl

theorem cell23_6834693_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 2, 2, 2, 2, 4, 3, 2].length) (baseStart_6834693 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834693 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834693 prefixEnd_6834693 := by exact prefixLift 6834693
  have htrace : WordTrace (prefixWord ++ tailWord_6834693) baseStart_6834693 baseEnd_6834693 := by
    simpa [prefixWord, tailWord_6834693, baseEnd_6834693] using wordTrace_append hprefix tailTrace_6834693
  have hstable : (prefixWord ++ tailWord_6834693).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834693).length < 2 ^ (prefixWord ++ tailWord_6834693).sum := by decide
  have hdescent : baseEnd_6834693 < baseStart_6834693 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834693) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834694 : List Nat := [6, 2, 1, 1, 1, 2, 1, 2, 3, 4]
def baseStart_6834694 : Nat := 118140960795 + 6834694 * 2 ^ 59
def prefixEnd_6834694 : Nat := 4983230072969 + 3 ^ 40 * 6834694 * 2
def baseEnd_6834694 : Nat := 1169827716133529153997607

theorem tailTrace_6834694 : CollatzResearch.WordTrace tailWord_6834694 prefixEnd_6834694 1169827716133529153997607 := by
  unfold tailWord_6834694
  simp only [CollatzResearch.WordTrace]
  refine ⟨7790055296908699551530473, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 6 166187846334052257099316757 7790055296908699551530473)
  ·
    refine ⟨5842541472681524663647855, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 7790055296908699551530473 5842541472681524663647855)
    ·
      refine ⟨8763812209022286995471783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 5842541472681524663647855 8763812209022286995471783)
      ·
        refine ⟨13145718313533430493207675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 8763812209022286995471783 13145718313533430493207675)
        ·
          refine ⟨19718577470300145739811513, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 13145718313533430493207675 19718577470300145739811513)
          ·
            refine ⟨14788933102725109304858635, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19718577470300145739811513 14788933102725109304858635)
            ·
              refine ⟨22183399654087663957287953, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788933102725109304858635 22183399654087663957287953)
              ·
                refine ⟨16637549740565747967965965, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22183399654087663957287953 16637549740565747967965965)
                ·
                  refine ⟨6239081152712155487987237, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16637549740565747967965965 6239081152712155487987237)
                  ·
                    refine ⟨1169827716133529153997607, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6239081152712155487987237 1169827716133529153997607)
                    ·
                      rfl

theorem cell23_6834694_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 6, 2, 1, 1, 1, 2, 1, 2, 3, 4].length) (baseStart_6834694 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834694 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834694 prefixEnd_6834694 := by exact prefixLift 6834694
  have htrace : WordTrace (prefixWord ++ tailWord_6834694) baseStart_6834694 baseEnd_6834694 := by
    simpa [prefixWord, tailWord_6834694, baseEnd_6834694] using wordTrace_append hprefix tailTrace_6834694
  have hstable : (prefixWord ++ tailWord_6834694).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834694).length < 2 ^ (prefixWord ++ tailWord_6834694).sum := by decide
  have hdescent : baseEnd_6834694 < baseStart_6834694 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834694) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834700 : List Nat := [2, 2, 1, 2, 4, 2, 1, 2, 3, 1, 3]
def baseStart_6834700 : Nat := 118140960795 + 6834700 * 2 ^ 59
def prefixEnd_6834700 : Nat := 4983230072969 + 3 ^ 40 * 6834700 * 2
def baseEnd_6834700 : Nat := 3509486229284514438517793

theorem tailTrace_6834700 : CollatzResearch.WordTrace tailWord_6834700 prefixEnd_6834700 3509486229284514438517793 := by
  unfold tailWord_6834700
  simp only [CollatzResearch.WordTrace]
  refine ⟨124640994169528324336846777, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166187992226037765782462369 124640994169528324336846777)
  ·
    refine ⟨93480745627146243252635083, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124640994169528324336846777 93480745627146243252635083)
    ·
      refine ⟨140221118440719364878952625, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93480745627146243252635083 140221118440719364878952625)
      ·
        refine ⟨105165838830539523659214469, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140221118440719364878952625 105165838830539523659214469)
        ·
          refine ⟨19718594780726160686102713, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105165838830539523659214469 19718594780726160686102713)
          ·
            refine ⟨14788946085544620514577035, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 19718594780726160686102713 14788946085544620514577035)
            ·
              refine ⟨22183419128316930771865553, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788946085544620514577035 22183419128316930771865553)
              ·
                refine ⟨16637564346237698078899165, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22183419128316930771865553 16637564346237698078899165)
                ·
                  refine ⟨6239086629839136779587187, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 16637564346237698078899165 6239086629839136779587187)
                  ·
                    refine ⟨9358629944758705169380781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6239086629839136779587187 9358629944758705169380781)
                    ·
                      refine ⟨3509486229284514438517793, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358629944758705169380781 3509486229284514438517793)
                      ·
                        rfl

theorem cell23_6834700_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 1, 2, 4, 2, 1, 2, 3, 1, 3].length) (baseStart_6834700 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834700 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834700 prefixEnd_6834700 := by exact prefixLift 6834700
  have htrace : WordTrace (prefixWord ++ tailWord_6834700) baseStart_6834700 baseEnd_6834700 := by
    simpa [prefixWord, tailWord_6834700, baseEnd_6834700] using wordTrace_append hprefix tailTrace_6834700
  have hstable : (prefixWord ++ tailWord_6834700).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834700).length < 2 ^ (prefixWord ++ tailWord_6834700).sum := by decide
  have hdescent : baseEnd_6834700 < baseStart_6834700 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834700) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834717 : List Nat := [1, 4, 2, 2, 1, 2, 1, 5, 1, 1, 3]
def baseStart_6834717 : Nat := 118140960795 + 6834717 * 2 ^ 59
def prefixEnd_6834717 : Nat := 4983230072969 + 3 ^ 40 * 6834717 * 2
def baseEnd_6834717 : Nat := 3509494958455640872005215

theorem tailTrace_6834717 : CollatzResearch.WordTrace tailWord_6834717 prefixEnd_6834717 3509494958455640872005215 := by
  unfold tailWord_6834717
  simp only [CollatzResearch.WordTrace]
  refine ⟨249282608379995060577062405, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166188405586663373718041603 249282608379995060577062405)
  ·
    refine ⟨46740489071249073858199201, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 249282608379995060577062405 46740489071249073858199201)
    ·
      refine ⟨35055366803436805393649401, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46740489071249073858199201 35055366803436805393649401)
      ·
        refine ⟨26291525102577604045237051, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35055366803436805393649401 26291525102577604045237051)
        ·
          refine ⟨39437287653866406067855577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26291525102577604045237051 39437287653866406067855577)
          ·
            refine ⟨29577965740399804550891683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39437287653866406067855577 29577965740399804550891683)
            ·
              refine ⟨44366948610599706826337525, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29577965740399804550891683 44366948610599706826337525)
              ·
                refine ⟨4159401432243722514969143, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 5 44366948610599706826337525 4159401432243722514969143)
                ·
                  refine ⟨6239102148365583772453715, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159401432243722514969143 6239102148365583772453715)
                  ·
                    refine ⟨9358653222548375658680573, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6239102148365583772453715 9358653222548375658680573)
                    ·
                      refine ⟨3509494958455640872005215, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358653222548375658680573 3509494958455640872005215)
                      ·
                        rfl

theorem cell23_6834717_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 4, 2, 2, 1, 2, 1, 5, 1, 1, 3].length) (baseStart_6834717 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834717 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834717 prefixEnd_6834717 := by exact prefixLift 6834717
  have htrace : WordTrace (prefixWord ++ tailWord_6834717) baseStart_6834717 baseEnd_6834717 := by
    simpa [prefixWord, tailWord_6834717, baseEnd_6834717] using wordTrace_append hprefix tailTrace_6834717
  have hstable : (prefixWord ++ tailWord_6834717).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834717).length < 2 ^ (prefixWord ++ tailWord_6834717).sum := by decide
  have hdescent : baseEnd_6834717 < baseStart_6834717 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834717) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834720 : List Nat := [2, 1, 1, 6, 2, 1, 1, 3, 1, 5]
def baseStart_6834720 : Nat := 118140960795 + 6834720 * 2 ^ 59
def prefixEnd_6834720 : Nat := 4983230072969 + 3 ^ 40 * 6834720 * 2
def baseEnd_6834720 : Nat := 1169832166299201453422567

theorem tailTrace_6834720 : CollatzResearch.WordTrace tailWord_6834720 prefixEnd_6834720 1169832166299201453422567 := by
  unfold tailWord_6834720
  simp only [CollatzResearch.WordTrace]
  refine ⟨124641358899492096044710807, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166188478532656128059614409 124641358899492096044710807)
  ·
    refine ⟨186962038349238144067066211, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124641358899492096044710807 186962038349238144067066211)
    ·
      refine ⟨280443057523857216100599317, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186962038349238144067066211 280443057523857216100599317)
      ·
        refine ⟨13145768321430807004715593, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280443057523857216100599317 13145768321430807004715593)
        ·
          refine ⟨9859326241073105253536695, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13145768321430807004715593 9859326241073105253536695)
          ·
            refine ⟨14788989361609657880305043, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9859326241073105253536695 14788989361609657880305043)
            ·
              refine ⟨22183484042414486820457565, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14788989361609657880305043 22183484042414486820457565)
              ·
                refine ⟨8318806515905432557671587, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22183484042414486820457565 8318806515905432557671587)
                ·
                  refine ⟨12478209773858148836507381, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8318806515905432557671587 12478209773858148836507381)
                  ·
                    refine ⟨1169832166299201453422567, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12478209773858148836507381 1169832166299201453422567)
                    ·
                      rfl

theorem cell23_6834720_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 6, 2, 1, 1, 3, 1, 5].length) (baseStart_6834720 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834720 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834720 prefixEnd_6834720 := by exact prefixLift 6834720
  have htrace : WordTrace (prefixWord ++ tailWord_6834720) baseStart_6834720 baseEnd_6834720 := by
    simpa [prefixWord, tailWord_6834720, baseEnd_6834720] using wordTrace_append hprefix tailTrace_6834720
  have hstable : (prefixWord ++ tailWord_6834720).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834720).length < 2 ^ (prefixWord ++ tailWord_6834720).sum := by decide
  have hdescent : baseEnd_6834720 < baseStart_6834720 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834720) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834736 : List Nat := [2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4]
def baseStart_6834736 : Nat := 118140960795 + 6834736 * 2 ^ 59
def prefixEnd_6834736 : Nat := 4983230072969 + 3 ^ 40 * 6834736 * 2
def baseEnd_6834736 : Nat := 3509504714588076297667627

theorem tailTrace_6834736 : CollatzResearch.WordTrace tailWord_6834736 prefixEnd_6834736 3509504714588076297667627 := by
  unfold tailWord_6834736
  simp only [CollatzResearch.WordTrace]
  refine ⟨124641650683463113411002031, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166188867577950817881336041 124641650683463113411002031)
  ·
    refine ⟨186962476025194670116503047, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124641650683463113411002031 186962476025194670116503047)
    ·
      refine ⟨280443714037792005174754571, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186962476025194670116503047 280443714037792005174754571)
      ·
        refine ⟨420665571056688007762131857, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280443714037792005174754571 420665571056688007762131857)
        ·
          refine ⟨315499178292516005821598893, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420665571056688007762131857 315499178292516005821598893)
          ·
            refine ⟨118312191859693502183099585, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315499178292516005821598893 118312191859693502183099585)
            ·
              refine ⟨88734143894770126637324689, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118312191859693502183099585 88734143894770126637324689)
              ·
                refine ⟨66550607921077594977993517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 88734143894770126637324689 66550607921077594977993517)
                ·
                  refine ⟨24956477970404098116747569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 66550607921077594977993517 24956477970404098116747569)
                  ·
                    refine ⟨18717358477803073587560677, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24956477970404098116747569 18717358477803073587560677)
                    ·
                      refine ⟨3509504714588076297667627, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18717358477803073587560677 3509504714588076297667627)
                      ·
                        rfl

theorem cell23_6834736_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 1, 2, 3, 2, 2, 3, 2, 4].length) (baseStart_6834736 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834736 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834736 prefixEnd_6834736 := by exact prefixLift 6834736
  have htrace : WordTrace (prefixWord ++ tailWord_6834736) baseStart_6834736 baseEnd_6834736 := by
    simpa [prefixWord, tailWord_6834736, baseEnd_6834736] using wordTrace_append hprefix tailTrace_6834736
  have hstable : (prefixWord ++ tailWord_6834736).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834736).length < 2 ^ (prefixWord ++ tailWord_6834736).sum := by decide
  have hdescent : baseEnd_6834736 < baseStart_6834736 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834736) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834753 : List Nat := [1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 6]
def baseStart_6834753 : Nat := 118140960795 + 6834753 * 2 ^ 59
def prefixEnd_6834753 : Nat := 4983230072969 + 3 ^ 40 * 6834753 * 2
def baseEnd_6834753 : Nat := 3509513443759202731155049

theorem tailTrace_6834753 : CollatzResearch.WordTrace tailWord_6834753 prefixEnd_6834753 3509513443759202731155049 := by
  unfold tailWord_6834753
  simp only [CollatzResearch.WordTrace]
  refine ⟨249283921407864638725372913, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166189280938576425816915275 249283921407864638725372913)
  ·
    refine ⟨186962941055898479044029685, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249283921407864638725372913 186962941055898479044029685)
    ·
      refine ⟨17527775723990482410377783, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 186962941055898479044029685 17527775723990482410377783)
      ·
        refine ⟨26291663585985723615566675, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17527775723990482410377783 26291663585985723615566675)
        ·
          refine ⟨39437495378978585423350013, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26291663585985723615566675 39437495378978585423350013)
          ·
            refine ⟨14789060767116969533756255, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 39437495378978585423350013 14789060767116969533756255)
            ·
              refine ⟨22183591150675454300634383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14789060767116969533756255 22183591150675454300634383)
              ·
                refine ⟨33275386726013181450951575, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22183591150675454300634383 33275386726013181450951575)
                ·
                  refine ⟨49913080089019772176427363, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33275386726013181450951575 49913080089019772176427363)
                  ·
                    refine ⟨74869620133529658264641045, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 49913080089019772176427363 74869620133529658264641045)
                    ·
                      refine ⟨3509513443759202731155049, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 6 74869620133529658264641045 3509513443759202731155049)
                      ·
                        rfl

theorem cell23_6834753_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 5, 1, 1, 3, 1, 1, 1, 1, 6].length) (baseStart_6834753 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834753 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834753 prefixEnd_6834753 := by exact prefixLift 6834753
  have htrace : WordTrace (prefixWord ++ tailWord_6834753) baseStart_6834753 baseEnd_6834753 := by
    simpa [prefixWord, tailWord_6834753, baseEnd_6834753] using wordTrace_append hprefix tailTrace_6834753
  have hstable : (prefixWord ++ tailWord_6834753).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834753).length < 2 ^ (prefixWord ++ tailWord_6834753).sum := by decide
  have hdescent : baseEnd_6834753 < baseStart_6834753 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834753) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834773 : List Nat := [1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 3]
def baseStart_6834773 : Nat := 118140960795 + 6834773 * 2 ^ 59
def prefixEnd_6834773 : Nat := 4983230072969 + 3 ^ 40 * 6834773 * 2
def baseEnd_6834773 : Nat := 3509523713372292652904957

theorem tailTrace_6834773 : CollatzResearch.WordTrace tailWord_6834773 prefixEnd_6834773 3509523713372292652904957 := by
  unfold tailWord_6834773
  simp only [CollatzResearch.WordTrace]
  refine ⟨249284650867792182141100973, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166189767245194788094067315 249284650867792182141100973)
  ·
    refine ⟨93481744075422068302912865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249284650867792182141100973 93481744075422068302912865)
    ·
      refine ⟨70111308056566551227184649, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93481744075422068302912865 70111308056566551227184649)
      ·
        refine ⟨52583481042424913420388487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70111308056566551227184649 52583481042424913420388487)
        ·
          refine ⟨78875221563637370130582731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52583481042424913420388487 78875221563637370130582731)
          ·
            refine ⟨118312832345456055195874097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78875221563637370130582731 118312832345456055195874097)
            ·
              refine ⟨88734624259092041396905573, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 118312832345456055195874097 88734624259092041396905573)
              ·
                refine ⟨16637742048579757761919795, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 88734624259092041396905573 16637742048579757761919795)
                ·
                  refine ⟨24956613072869636642879693, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16637742048579757761919795 24956613072869636642879693)
                  ·
                    refine ⟨9358729902326113741079885, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 24956613072869636642879693 9358729902326113741079885)
                    ·
                      refine ⟨3509523713372292652904957, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358729902326113741079885 3509523713372292652904957)
                      ·
                        rfl

theorem cell23_6834773_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 2, 2, 1, 1, 2, 4, 1, 3, 3].length) (baseStart_6834773 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834773 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834773 prefixEnd_6834773 := by exact prefixLift 6834773
  have htrace : WordTrace (prefixWord ++ tailWord_6834773) baseStart_6834773 baseEnd_6834773 := by
    simpa [prefixWord, tailWord_6834773, baseEnd_6834773] using wordTrace_append hprefix tailTrace_6834773
  have hstable : (prefixWord ++ tailWord_6834773).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834773).length < 2 ^ (prefixWord ++ tailWord_6834773).sum := by decide
  have hdescent : baseEnd_6834773 < baseStart_6834773 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834773) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834780 : List Nat := [2, 2, 4, 1, 4, 1, 9]
def baseStart_6834780 : Nat := 118140960795 + 6834780 * 2 ^ 59
def prefixEnd_6834780 : Nat := 4983230072969 + 3 ^ 40 * 6834780 * 2
def baseEnd_6834780 : Nat := 43327497626381162043425

theorem tailTrace_6834780 : CollatzResearch.WordTrace tailWord_6834780 prefixEnd_6834780 43327497626381162043425 := by
  unfold tailWord_6834780
  simp only [CollatzResearch.WordTrace]
  refine ⟨124642453089383411168302897, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166189937452511214891070529 124642453089383411168302897)
  ·
    refine ⟨93481839817037558376227173, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124642453089383411168302897 93481839817037558376227173)
    ·
      refine ⟨17527844965694542195542595, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93481839817037558376227173 17527844965694542195542595)
      ·
        refine ⟨26291767448541813293313893, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17527844965694542195542595 26291767448541813293313893)
        ·
          refine ⟨4929706396601589992496355, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26291767448541813293313893 4929706396601589992496355)
          ·
            refine ⟨7394559594902384988744533, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929706396601589992496355 7394559594902384988744533)
            ·
              refine ⟨43327497626381162043425, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 9 7394559594902384988744533 43327497626381162043425)
              ·
                rfl

theorem cell23_6834780_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 4, 1, 4, 1, 9].length) (baseStart_6834780 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834780 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834780 prefixEnd_6834780 := by exact prefixLift 6834780
  have htrace : WordTrace (prefixWord ++ tailWord_6834780) baseStart_6834780 baseEnd_6834780 := by
    simpa [prefixWord, tailWord_6834780, baseEnd_6834780] using wordTrace_append hprefix tailTrace_6834780
  have hstable : (prefixWord ++ tailWord_6834780).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834780).length < 2 ^ (prefixWord ++ tailWord_6834780).sum := by decide
  have hdescent : baseEnd_6834780 < baseStart_6834780 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834780) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834807 : List Nat := [1, 1, 3, 1, 1, 3, 6, 1, 2, 1, 3]
def baseStart_6834807 : Nat := 118140960795 + 6834807 * 2 ^ 59
def prefixEnd_6834807 : Nat := 4983230072969 + 3 ^ 40 * 6834807 * 2
def baseEnd_6834807 : Nat := 3509541171714545519879801

theorem tailTrace_6834807 : CollatzResearch.WordTrace tailWord_6834807 prefixEnd_6834807 3509541171714545519879801 := by
  unfold tailWord_6834807
  simp only [CollatzResearch.WordTrace]
  refine ⟨249285890949669005947838675, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166190593966446003965225783 249285890949669005947838675)
  ·
    refine ⟨373928836424503508921758013, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249285890949669005947838675 373928836424503508921758013)
    ·
      refine ⟨140223313659188815845659255, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373928836424503508921758013 140223313659188815845659255)
      ·
        refine ⟨210334970488783223768488883, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140223313659188815845659255 210334970488783223768488883)
        ·
          refine ⟨315502455733174835652733325, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210334970488783223768488883 315502455733174835652733325)
          ·
            refine ⟨118313420899940563369774997, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 315502455733174835652733325 118313420899940563369774997)
            ·
              refine ⟨5545941604684713907958203, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 6 118313420899940563369774997 5545941604684713907958203)
              ·
                refine ⟨8318912407027070861937305, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5545941604684713907958203 8318912407027070861937305)
                ·
                  refine ⟨6239184305270303146452979, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8318912407027070861937305 6239184305270303146452979)
                  ·
                    refine ⟨9358776457905454719679469, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6239184305270303146452979 9358776457905454719679469)
                    ·
                      refine ⟨3509541171714545519879801, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358776457905454719679469 3509541171714545519879801)
                      ·
                        rfl

theorem cell23_6834807_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 1, 3, 6, 1, 2, 1, 3].length) (baseStart_6834807 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834807 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834807 prefixEnd_6834807 := by exact prefixLift 6834807
  have htrace : WordTrace (prefixWord ++ tailWord_6834807) baseStart_6834807 baseEnd_6834807 := by
    simpa [prefixWord, tailWord_6834807, baseEnd_6834807] using wordTrace_append hprefix tailTrace_6834807
  have hstable : (prefixWord ++ tailWord_6834807).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834807).length < 2 ^ (prefixWord ++ tailWord_6834807).sum := by decide
  have hdescent : baseEnd_6834807 < baseStart_6834807 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834807) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834863 : List Nat := [1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 3]
def baseStart_6834863 : Nat := 118140960795 + 6834863 * 2 ^ 59
def prefixEnd_6834863 : Nat := 4983230072969 + 3 ^ 40 * 6834863 * 2
def baseEnd_6834863 : Nat := 3509569926631197300779543

theorem tailTrace_6834863 : CollatzResearch.WordTrace tailWord_6834863 prefixEnd_6834863 3509569926631197300779543 := by
  unfold tailWord_6834863
  simp only [CollatzResearch.WordTrace]
  refine ⟨249287933437466127511877243, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166191955624977418341251495 249287933437466127511877243)
  ·
    refine ⟨373931900156199191267815865, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249287933437466127511877243 373931900156199191267815865)
    ·
      refine ⟨280448925117149393450861899, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373931900156199191267815865 280448925117149393450861899)
      ·
        refine ⟨420673387675724090176292849, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280448925117149393450861899 420673387675724090176292849)
        ·
          refine ⟨315505040756793067632219637, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 420673387675724090176292849 315505040756793067632219637)
          ·
            refine ⟨29578597570949350090520591, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 315505040756793067632219637 29578597570949350090520591)
            ·
              refine ⟨44367896356424025135780887, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29578597570949350090520591 44367896356424025135780887)
              ·
                refine ⟨66551844534636037703671331, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44367896356424025135780887 66551844534636037703671331)
                ·
                  refine ⟨99827766801954056555506997, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66551844534636037703671331 99827766801954056555506997)
                  ·
                    refine ⟨9358853137683192802078781, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 99827766801954056555506997 9358853137683192802078781)
                    ·
                      refine ⟨3509569926631197300779543, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358853137683192802078781 3509569926631197300779543)
                      ·
                        rfl

theorem cell23_6834863_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 2, 5, 1, 1, 1, 5, 3].length) (baseStart_6834863 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834863 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834863 prefixEnd_6834863 := by exact prefixLift 6834863
  have htrace : WordTrace (prefixWord ++ tailWord_6834863) baseStart_6834863 baseEnd_6834863 := by
    simpa [prefixWord, tailWord_6834863, baseEnd_6834863] using wordTrace_append hprefix tailTrace_6834863
  have hstable : (prefixWord ++ tailWord_6834863).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834863).length < 2 ^ (prefixWord ++ tailWord_6834863).sum := by decide
  have hdescent : baseEnd_6834863 < baseStart_6834863 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834863) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834898 : List Nat := [3, 2, 2, 2, 4, 1, 1, 2, 2, 2, 2]
def baseStart_6834898 : Nat := 118140960795 + 6834898 * 2 ^ 59
def prefixEnd_6834898 : Nat := 4983230072969 + 3 ^ 40 * 6834898 * 2
def baseEnd_6834898 : Nat := 3509587898454104663841883

theorem tailTrace_6834898 : CollatzResearch.WordTrace tailWord_6834898 prefixEnd_6834898 3509587898454104663841883 := by
  unfold tailWord_6834898
  simp only [CollatzResearch.WordTrace]
  refine ⟨62322302498084832122350337, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166192806661559552326267565 62322302498084832122350337)
  ·
    refine ⟨46741726873563624091762753, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62322302498084832122350337 46741726873563624091762753)
    ·
      refine ⟨35056295155172718068822065, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46741726873563624091762753 35056295155172718068822065)
      ·
        refine ⟨26292221366379538551616549, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 35056295155172718068822065 26292221366379538551616549)
        ·
          refine ⟨4929791506196163478428103, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 26292221366379538551616549 4929791506196163478428103)
          ·
            refine ⟨7394687259294245217642155, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4929791506196163478428103 7394687259294245217642155)
            ·
              refine ⟨11092030888941367826463233, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7394687259294245217642155 11092030888941367826463233)
              ·
                refine ⟨8319023166706025869847425, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11092030888941367826463233 8319023166706025869847425)
                ·
                  refine ⟨6239267375029519402385569, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8319023166706025869847425 6239267375029519402385569)
                  ·
                    refine ⟨4679450531272139551789177, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6239267375029519402385569 4679450531272139551789177)
                    ·
                      refine ⟨3509587898454104663841883, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679450531272139551789177 3509587898454104663841883)
                      ·
                        rfl

theorem cell23_6834898_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 2, 2, 4, 1, 1, 2, 2, 2, 2].length) (baseStart_6834898 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834898 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834898 prefixEnd_6834898 := by exact prefixLift 6834898
  have htrace : WordTrace (prefixWord ++ tailWord_6834898) baseStart_6834898 baseEnd_6834898 := by
    simpa [prefixWord, tailWord_6834898, baseEnd_6834898] using wordTrace_append hprefix tailTrace_6834898
  have hstable : (prefixWord ++ tailWord_6834898).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834898).length < 2 ^ (prefixWord ++ tailWord_6834898).sum := by decide
  have hdescent : baseEnd_6834898 < baseStart_6834898 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834898) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6834940 : List Nat := [2, 2, 2, 1, 3, 2, 2, 1, 1, 4, 3]
def baseStart_6834940 : Nat := 118140960795 + 6834940 * 2 ^ 59
def prefixEnd_6834940 : Nat := 4983230072969 + 3 ^ 40 * 6834940 * 2
def baseEnd_6834940 : Nat := 3509609464641593499516689

theorem tailTrace_6834940 : CollatzResearch.WordTrace tailWord_6834940 prefixEnd_6834940 3509609464641593499516689 := by
  unfold tailWord_6834940
  simp only [CollatzResearch.WordTrace]
  refine ⟨124645370929093584831215137, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166193827905458113108286849 124645370929093584831215137)
  ·
    refine ⟨93484028196820188623411353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124645370929093584831215137 93484028196820188623411353)
    ·
      refine ⟨70113021147615141467558515, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93484028196820188623411353 70113021147615141467558515)
      ·
        refine ⟨105169531721422712201337773, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70113021147615141467558515 105169531721422712201337773)
        ·
          refine ⟨39438574395533517075501665, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 105169531721422712201337773 39438574395533517075501665)
          ·
            refine ⟨29578930796650137806626249, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39438574395533517075501665 29578930796650137806626249)
            ·
              refine ⟨22184198097487603354969687, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29578930796650137806626249 22184198097487603354969687)
              ·
                refine ⟨33276297146231405032454531, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22184198097487603354969687 33276297146231405032454531)
                ·
                  refine ⟨49914445719347107548681797, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33276297146231405032454531 49914445719347107548681797)
                  ·
                    refine ⟨9358958572377582665377837, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 49914445719347107548681797 9358958572377582665377837)
                    ·
                      refine ⟨3509609464641593499516689, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9358958572377582665377837 3509609464641593499516689)
                      ·
                        rfl

theorem cell23_6834940_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 4, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 1, 3, 2, 2, 1, 1, 4, 3].length) (baseStart_6834940 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6834940 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6834940 prefixEnd_6834940 := by exact prefixLift 6834940
  have htrace : WordTrace (prefixWord ++ tailWord_6834940) baseStart_6834940 baseEnd_6834940 := by
    simpa [prefixWord, tailWord_6834940, baseEnd_6834940] using wordTrace_append hprefix tailTrace_6834940
  have hstable : (prefixWord ++ tailWord_6834940).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6834940).length < 2 ^ (prefixWord ++ tailWord_6834940).sum := by decide
  have hdescent : baseEnd_6834940 < baseStart_6834940 := by decide
  rcases family_descends (prefixWord ++ tailWord_6834940) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835004 : List Nat := [2, 2, 2, 2, 1, 1, 1, 7, 1, 1, 3]
def baseStart_6835004 : Nat := 118140960795 + 6835004 * 2 ^ 59
def prefixEnd_6835004 : Nat := 4983230072969 + 3 ^ 40 * 6835004 * 2
def baseEnd_6835004 : Nat := 3509642327403481249116395

theorem tailTrace_6835004 : CollatzResearch.WordTrace tailWord_6835004 prefixEnd_6835004 3509642327403481249116395 := by
  unfold tailWord_6835004
  simp only [CollatzResearch.WordTrace]
  refine ⟨124646538064977654296380033, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166195384086636872395173377 124646538064977654296380033)
  ·
    refine ⟨93484903548733240722285025, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124646538064977654296380033 93484903548733240722285025)
    ·
      refine ⟨70113677661549930541713769, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 93484903548733240722285025 70113677661549930541713769)
      ·
        refine ⟨52585258246162447906285327, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70113677661549930541713769 52585258246162447906285327)
        ·
          refine ⟨78877887369243671859427991, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52585258246162447906285327 78877887369243671859427991)
          ·
            refine ⟨118316831053865507789141987, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78877887369243671859427991 118316831053865507789141987)
            ·
              refine ⟨177475246580798261683712981, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 118316831053865507789141987 177475246580798261683712981)
              ·
                refine ⟨4159576091737459258212023, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 7 177475246580798261683712981 4159576091737459258212023)
                ·
                  refine ⟨6239364137606188887318035, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159576091737459258212023 6239364137606188887318035)
                  ·
                    refine ⟨9359046206409283330977053, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6239364137606188887318035 9359046206409283330977053)
                    ·
                      refine ⟨3509642327403481249116395, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9359046206409283330977053 3509642327403481249116395)
                      ·
                        rfl

theorem cell23_6835004_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 2, 2, 1, 1, 1, 7, 1, 1, 3].length) (baseStart_6835004 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835004 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835004 prefixEnd_6835004 := by exact prefixLift 6835004
  have htrace : WordTrace (prefixWord ++ tailWord_6835004) baseStart_6835004 baseEnd_6835004 := by
    simpa [prefixWord, tailWord_6835004, baseEnd_6835004] using wordTrace_append hprefix tailTrace_6835004
  have hstable : (prefixWord ++ tailWord_6835004).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835004).length < 2 ^ (prefixWord ++ tailWord_6835004).sum := by decide
  have hdescent : baseEnd_6835004 < baseStart_6835004 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835004) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835027 : List Nat := [1, 1, 1, 2, 1, 1, 3, 2, 7, 2, 2]
def baseStart_6835027 : Nat := 118140960795 + 6835027 * 2 ^ 59
def prefixEnd_6835027 : Nat := 4983230072969 + 3 ^ 40 * 6835027 * 2
def baseEnd_6835027 : Nat := 3509654137458534659128789

theorem tailTrace_6835027 : CollatzResearch.WordTrace tailWord_6835027 prefixEnd_6835027 3509654137458534659128789 := by
  unfold tailWord_6835027
  simp only [CollatzResearch.WordTrace]
  refine ⟨249293915008871983520847335, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166195943339247989013898223 249293915008871983520847335)
  ·
    refine ⟨373940872513307975281271003, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249293915008871983520847335 373940872513307975281271003)
    ·
      refine ⟨560911308769961962921906505, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373940872513307975281271003 560911308769961962921906505)
      ·
        refine ⟨420683481577471472191429879, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 560911308769961962921906505 420683481577471472191429879)
        ·
          refine ⟨631025222366207208287144819, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420683481577471472191429879 631025222366207208287144819)
          ·
            refine ⟨946537833549310812430717229, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 631025222366207208287144819 946537833549310812430717229)
            ·
              refine ⟨354951687580991554661518961, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 946537833549310812430717229 354951687580991554661518961)
              ·
                refine ⟨266213765685743665996139221, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 354951687580991554661518961 266213765685743665996139221)
                ·
                  refine ⟨6239385133259617171784513, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 266213765685743665996139221 6239385133259617171784513)
                  ·
                    refine ⟨4679538849944712878838385, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6239385133259617171784513 4679538849944712878838385)
                    ·
                      refine ⟨3509654137458534659128789, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679538849944712878838385 3509654137458534659128789)
                      ·
                        rfl

theorem cell23_6835027_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 2, 1, 1, 3, 2, 7, 2, 2].length) (baseStart_6835027 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835027 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835027 prefixEnd_6835027 := by exact prefixLift 6835027
  have htrace : WordTrace (prefixWord ++ tailWord_6835027) baseStart_6835027 baseEnd_6835027 := by
    simpa [prefixWord, tailWord_6835027, baseEnd_6835027] using wordTrace_append hprefix tailTrace_6835027
  have hstable : (prefixWord ++ tailWord_6835027).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835027).length < 2 ^ (prefixWord ++ tailWord_6835027).sum := by decide
  have hdescent : baseEnd_6835027 < baseStart_6835027 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835027) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835044 : List Nat := [2, 3, 1, 1, 4, 1, 1, 1, 5, 2, 2]
def baseStart_6835044 : Nat := 118140960795 + 6835044 * 2 ^ 59
def prefixEnd_6835044 : Nat := 4983230072969 + 3 ^ 40 * 6835044 * 2
def baseEnd_6835044 : Nat := 3509662866629661092616211

theorem tailTrace_6835044 : CollatzResearch.WordTrace tailWord_6835044 prefixEnd_6835044 3509662866629661092616211 := by
  unfold tailWord_6835044
  simp only [CollatzResearch.WordTrace]
  refine ⟨124647267524905197712108093, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166196356699873596949477457 124647267524905197712108093)
  ·
    refine ⟨46742725321839449142040535, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 124647267524905197712108093 46742725321839449142040535)
    ·
      refine ⟨70114087982759173713060803, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46742725321839449142040535 70114087982759173713060803)
      ·
        refine ⟨105171131974138760569591205, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 70114087982759173713060803 105171131974138760569591205)
        ·
          refine ⟨19719587245151017606798351, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 105171131974138760569591205 19719587245151017606798351)
          ·
            refine ⟨29579380867726526410197527, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19719587245151017606798351 29579380867726526410197527)
            ·
              refine ⟨44369071301589789615296291, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29579380867726526410197527 44369071301589789615296291)
              ·
                refine ⟨66553606952384684422944437, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44369071301589789615296291 66553606952384684422944437)
                ·
                  refine ⟨6239400651786064164651041, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66553606952384684422944437 6239400651786064164651041)
                  ·
                    refine ⟨4679550488839548123488281, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6239400651786064164651041 4679550488839548123488281)
                    ·
                      refine ⟨3509662866629661092616211, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679550488839548123488281 3509662866629661092616211)
                      ·
                        rfl

theorem cell23_6835044_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 3, 1, 1, 4, 1, 1, 1, 5, 2, 2].length) (baseStart_6835044 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835044 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835044 prefixEnd_6835044 := by exact prefixLift 6835044
  have htrace : WordTrace (prefixWord ++ tailWord_6835044) baseStart_6835044 baseEnd_6835044 := by
    simpa [prefixWord, tailWord_6835044, baseEnd_6835044] using wordTrace_append hprefix tailTrace_6835044
  have hstable : (prefixWord ++ tailWord_6835044).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835044).length < 2 ^ (prefixWord ++ tailWord_6835044).sum := by decide
  have hdescent : baseEnd_6835044 < baseStart_6835044 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835044) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835047 : List Nat := [1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 3]
def baseStart_6835047 : Nat := 118140960795 + 6835047 * 2 ^ 59
def prefixEnd_6835047 : Nat := 4983230072969 + 3 ^ 40 * 6835047 * 2
def baseEnd_6835047 : Nat := 3509664407071624580878697

theorem tailTrace_6835047 : CollatzResearch.WordTrace tailWord_6835047 prefixEnd_6835047 3509664407071624580878697 := by
  unfold tailWord_6835047
  simp only [CollatzResearch.WordTrace]
  refine ⟨249294644468799526936575395, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166196429645866351291050263 249294644468799526936575395)
  ·
    refine ⟨373941966703199290404863093, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249294644468799526936575395 373941966703199290404863093)
    ·
      refine ⟨35057059378424933475455915, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 5 373941966703199290404863093 35057059378424933475455915)
      ·
        refine ⟨52585589067637400213183873, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35057059378424933475455915 52585589067637400213183873)
        ·
          refine ⟨39439191800728050159887905, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52585589067637400213183873 39439191800728050159887905)
          ·
            refine ⟨29579393850546037619915929, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39439191800728050159887905 29579393850546037619915929)
            ·
              refine ⟨22184545387909528214936947, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29579393850546037619915929 22184545387909528214936947)
              ·
                refine ⟨33276818081864292322405421, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22184545387909528214936947 33276818081864292322405421)
                ·
                  refine ⟨12478806780699109620902033, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33276818081864292322405421 12478806780699109620902033)
                  ·
                    refine ⟨9359105085524332215676525, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12478806780699109620902033 9359105085524332215676525)
                    ·
                      refine ⟨3509664407071624580878697, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9359105085524332215676525 3509664407071624580878697)
                      ·
                        rfl

theorem cell23_6835047_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 5, 1, 2, 2, 2, 1, 3, 2, 3].length) (baseStart_6835047 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835047 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835047 prefixEnd_6835047 := by exact prefixLift 6835047
  have htrace : WordTrace (prefixWord ++ tailWord_6835047) baseStart_6835047 baseEnd_6835047 := by
    simpa [prefixWord, tailWord_6835047, baseEnd_6835047] using wordTrace_append hprefix tailTrace_6835047
  have hstable : (prefixWord ++ tailWord_6835047).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835047).length < 2 ^ (prefixWord ++ tailWord_6835047).sum := by decide
  have hdescent : baseEnd_6835047 < baseStart_6835047 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835047) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835061 : List Nat := [1, 3, 4, 1, 1, 4, 2, 1, 1, 1, 4]
def baseStart_6835061 : Nat := 118140960795 + 6835061 * 2 ^ 59
def prefixEnd_6835061 : Nat := 4983230072969 + 3 ^ 40 * 6835061 * 2
def baseEnd_6835061 : Nat := 3509671595800787526103633

theorem tailTrace_6835061 : CollatzResearch.WordTrace tailWord_6835061 prefixEnd_6835061 3509671595800787526103633 := by
  unfold tailWord_6835061
  simp only [CollatzResearch.WordTrace]
  refine ⟨249295155090748807327585037, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166196770060499204885056691 249295155090748807327585037)
  ·
    refine ⟨93485683159030802747844389, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249295155090748807327585037 93485683159030802747844389)
    ·
      refine ⟨17528565592318275515220823, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 93485683159030802747844389 17528565592318275515220823)
      ·
        refine ⟨26292848388477413272831235, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17528565592318275515220823 26292848388477413272831235)
        ·
          refine ⟨39439272582716119909246853, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26292848388477413272831235 39439272582716119909246853)
          ·
            refine ⟨7394863609259272482983785, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 4 39439272582716119909246853 7394863609259272482983785)
            ·
              refine ⟨5546147706944454362237839, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7394863609259272482983785 5546147706944454362237839)
              ·
                refine ⟨8319221560416681543356759, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546147706944454362237839 8319221560416681543356759)
                ·
                  refine ⟨12478832340625022315035139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8319221560416681543356759 12478832340625022315035139)
                  ·
                    refine ⟨18718248510937533472552709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12478832340625022315035139 18718248510937533472552709)
                    ·
                      refine ⟨3509671595800787526103633, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18718248510937533472552709 3509671595800787526103633)
                      ·
                        rfl

theorem cell23_6835061_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 4, 1, 1, 4, 2, 1, 1, 1, 4].length) (baseStart_6835061 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835061 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835061 prefixEnd_6835061 := by exact prefixLift 6835061
  have htrace : WordTrace (prefixWord ++ tailWord_6835061) baseStart_6835061 baseEnd_6835061 := by
    simpa [prefixWord, tailWord_6835061, baseEnd_6835061] using wordTrace_append hprefix tailTrace_6835061
  have hstable : (prefixWord ++ tailWord_6835061).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835061).length < 2 ^ (prefixWord ++ tailWord_6835061).sum := by decide
  have hdescent : baseEnd_6835061 < baseStart_6835061 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835061) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835104 : List Nat := [2, 1, 1, 4, 1, 1, 3, 4, 1, 3, 2]
def baseStart_6835104 : Nat := 118140960795 + 6835104 * 2 ^ 59
def prefixEnd_6835104 : Nat := 4983230072969 + 3 ^ 40 * 6835104 * 2
def baseEnd_6835104 : Nat := 3509693675468930857865935

theorem tailTrace_6835104 : CollatzResearch.WordTrace tailWord_6835104 prefixEnd_6835104 3509693675468930857865935 := by
  unfold tailWord_6835104
  simp only [CollatzResearch.WordTrace]
  refine ⟨124648361714796512835700183, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166197815619728683780933577 124648361714796512835700183)
  ·
    refine ⟨186972542572194769253550275, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124648361714796512835700183 186972542572194769253550275)
    ·
      refine ⟨280458813858292153880325413, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186972542572194769253550275 280458813858292153880325413)
      ·
        refine ⟨52586027598429778852561015, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 4 280458813858292153880325413 52586027598429778852561015)
        ·
          refine ⟨78879041397644668278841523, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52586027598429778852561015 78879041397644668278841523)
          ·
            refine ⟨118318562096467002418262285, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78879041397644668278841523 118318562096467002418262285)
            ·
              refine ⟨44369460786175125906848357, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118318562096467002418262285 44369460786175125906848357)
              ·
                refine ⟨8319273897407836107534067, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44369460786175125906848357 8319273897407836107534067)
                ·
                  refine ⟨12478910846111754161301101, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 8319273897407836107534067 12478910846111754161301101)
                  ·
                    refine ⟨4679591567291907810487913, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12478910846111754161301101 4679591567291907810487913)
                    ·
                      refine ⟨3509693675468930857865935, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679591567291907810487913 3509693675468930857865935)
                      ·
                        rfl

theorem cell23_6835104_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 4, 1, 1, 3, 4, 1, 3, 2].length) (baseStart_6835104 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835104 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835104 prefixEnd_6835104 := by exact prefixLift 6835104
  have htrace : WordTrace (prefixWord ++ tailWord_6835104) baseStart_6835104 baseEnd_6835104 := by
    simpa [prefixWord, tailWord_6835104, baseEnd_6835104] using wordTrace_append hprefix tailTrace_6835104
  have hstable : (prefixWord ++ tailWord_6835104).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835104).length < 2 ^ (prefixWord ++ tailWord_6835104).sum := by decide
  have hdescent : baseEnd_6835104 < baseStart_6835104 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835104) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835151 : List Nat := [1, 1, 2, 1, 1, 7, 1, 3, 2, 2, 2]
def baseStart_6835151 : Nat := 118140960795 + 6835151 * 2 ^ 59
def prefixEnd_6835151 : Nat := 4983230072969 + 3 ^ 40 * 6835151 * 2
def baseEnd_6835151 : Nat := 3509717809059692173978219

theorem tailTrace_6835151 : CollatzResearch.WordTrace tailWord_6835151 prefixEnd_6835151 3509717809059692173978219 := by
  unfold tailWord_6835151
  simp only [CollatzResearch.WordTrace]
  refine ⟨249298437660422752698361307, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166198958440281835132240871 249298437660422752698361307)
  ·
    refine ⟨373947656490634129047541961, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249298437660422752698361307 373947656490634129047541961)
    ·
      refine ⟨280460742367975596785656471, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373947656490634129047541961 280460742367975596785656471)
      ·
        refine ⟨420691113551963395178484707, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280460742367975596785656471 420691113551963395178484707)
        ·
          refine ⟨631036670327945092767727061, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420691113551963395178484707 631036670327945092767727061)
          ·
            refine ⟨14789921960811213111743603, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 7 631036670327945092767727061 14789921960811213111743603)
            ·
              refine ⟨22184882941216819667615405, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14789921960811213111743603 22184882941216819667615405)
              ·
                refine ⟨8319331102956307375355777, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 3 22184882941216819667615405 8319331102956307375355777)
                ·
                  refine ⟨6239498327217230531516833, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8319331102956307375355777 6239498327217230531516833)
                  ·
                    refine ⟨4679623745412922898637625, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6239498327217230531516833 4679623745412922898637625)
                    ·
                      refine ⟨3509717809059692173978219, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679623745412922898637625 3509717809059692173978219)
                      ·
                        rfl

theorem cell23_6835151_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 1, 1, 7, 1, 3, 2, 2, 2].length) (baseStart_6835151 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835151 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835151 prefixEnd_6835151 := by exact prefixLift 6835151
  have htrace : WordTrace (prefixWord ++ tailWord_6835151) baseStart_6835151 baseEnd_6835151 := by
    simpa [prefixWord, tailWord_6835151, baseEnd_6835151] using wordTrace_append hprefix tailTrace_6835151
  have hstable : (prefixWord ++ tailWord_6835151).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835151).length < 2 ^ (prefixWord ++ tailWord_6835151).sum := by decide
  have hdescent : baseEnd_6835151 < baseStart_6835151 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835151) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835177 : List Nat := [1, 2, 1, 1, 1, 2, 1, 1, 6, 5, 2]
def baseStart_6835177 : Nat := 118140960795 + 6835177 * 2 ^ 59
def prefixEnd_6835177 : Nat := 4983230072969 + 3 ^ 40 * 6835177 * 2
def baseEnd_6835177 : Nat := 3509731159556709072253099

theorem tailTrace_6835177 : CollatzResearch.WordTrace tailWord_6835177 prefixEnd_6835177 3509731159556709072253099 := by
  unfold tailWord_6835177
  simp only [CollatzResearch.WordTrace]
  refine ⟨249299385958328559138807785, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166199590638885706092538523 249299385958328559138807785)
  ·
    refine ⟨186974539468746419354105839, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249299385958328559138807785 186974539468746419354105839)
    ·
      refine ⟨280461809203119629031158759, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186974539468746419354105839 280461809203119629031158759)
      ·
        refine ⟨420692713804679443546738139, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280461809203119629031158759 420692713804679443546738139)
        ·
          refine ⟨631039070707019165320107209, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 420692713804679443546738139 631039070707019165320107209)
          ·
            refine ⟨473279303030264373990080407, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 631039070707019165320107209 473279303030264373990080407)
            ·
              refine ⟨709918954545396560985120611, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473279303030264373990080407 709918954545396560985120611)
              ·
                refine ⟨1064878431818094841477680917, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709918954545396560985120611 1064878431818094841477680917)
                ·
                  refine ⟨49916176491473195694266293, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 1064878431818094841477680917 49916176491473195694266293)
                  ·
                    refine ⟨4679641546075612096337465, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 49916176491473195694266293 4679641546075612096337465)
                    ·
                      refine ⟨3509731159556709072253099, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679641546075612096337465 3509731159556709072253099)
                      ·
                        rfl

theorem cell23_6835177_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 5, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 1, 2, 1, 1, 6, 5, 2].length) (baseStart_6835177 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835177 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835177 prefixEnd_6835177 := by exact prefixLift 6835177
  have htrace : WordTrace (prefixWord ++ tailWord_6835177) baseStart_6835177 baseEnd_6835177 := by
    simpa [prefixWord, tailWord_6835177, baseEnd_6835177] using wordTrace_append hprefix tailTrace_6835177
  have hstable : (prefixWord ++ tailWord_6835177).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835177).length < 2 ^ (prefixWord ++ tailWord_6835177).sum := by decide
  have hdescent : baseEnd_6835177 < baseStart_6835177 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835177) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835207 : List Nat := [1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 4]
def baseStart_6835207 : Nat := 118140960795 + 6835207 * 2 ^ 59
def prefixEnd_6835207 : Nat := 4983230072969 + 3 ^ 40 * 6835207 * 2
def baseEnd_6835207 : Nat := 3509746563976343954877961

theorem tailTrace_6835207 : CollatzResearch.WordTrace tailWord_6835207 prefixEnd_6835207 3509746563976343954877961 := by
  unfold tailWord_6835207
  simp only [CollatzResearch.WordTrace]
  refine ⟨249300480148219874262399875, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166200320098813249508266583 249300480148219874262399875)
  ·
    refine ⟨373950720222329811393599813, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249300480148219874262399875 373950720222329811393599813)
    ·
      refine ⟨70115760041686839636299965, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 373950720222329811393599813 70115760041686839636299965)
      ·
        refine ⟨26293410015632564863612487, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 70115760041686839636299965 26293410015632564863612487)
        ·
          refine ⟨39440115023448847295418731, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26293410015632564863612487 39440115023448847295418731)
          ·
            refine ⟨59160172535173270943128097, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39440115023448847295418731 59160172535173270943128097)
            ·
              refine ⟨44370129401379953207346073, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59160172535173270943128097 44370129401379953207346073)
              ·
                refine ⟨33277597051034964905509555, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44370129401379953207346073 33277597051034964905509555)
                ·
                  refine ⟨49916395576552447358264333, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 33277597051034964905509555 49916395576552447358264333)
                  ·
                    refine ⟨18718648341207167759349125, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 49916395576552447358264333 18718648341207167759349125)
                    ·
                      refine ⟨3509746563976343954877961, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18718648341207167759349125 3509746563976343954877961)
                      ·
                        rfl

theorem cell23_6835207_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 4, 3, 1, 1, 2, 2, 1, 3, 4].length) (baseStart_6835207 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835207 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835207 prefixEnd_6835207 := by exact prefixLift 6835207
  have htrace : WordTrace (prefixWord ++ tailWord_6835207) baseStart_6835207 baseEnd_6835207 := by
    simpa [prefixWord, tailWord_6835207, baseEnd_6835207] using wordTrace_append hprefix tailTrace_6835207
  have hstable : (prefixWord ++ tailWord_6835207).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835207).length < 2 ^ (prefixWord ++ tailWord_6835207).sum := by decide
  have hdescent : baseEnd_6835207 < baseStart_6835207 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835207) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835224 : List Nat := [2, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4]
def baseStart_6835224 : Nat := 118140960795 + 6835224 * 2 ^ 59
def prefixEnd_6835224 : Nat := 4983230072969 + 3 ^ 40 * 6835224 * 2
def baseEnd_6835224 : Nat := 3509755293147470388365383

theorem tailTrace_6835224 : CollatzResearch.WordTrace tailWord_6835224 prefixEnd_6835224 3509755293147470388365383 := by
  unfold tailWord_6835224
  simp only [CollatzResearch.WordTrace]
  refine ⟨124650550094579143082884363, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166200733459438857443845817 124650550094579143082884363)
  ·
    refine ⟨186975825141868714624326545, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124650550094579143082884363 186975825141868714624326545)
    ·
      refine ⟨140231868856401535968244909, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 186975825141868714624326545 140231868856401535968244909)
      ·
        refine ⟨52586950821150575988091841, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140231868856401535968244909 52586950821150575988091841)
        ·
          refine ⟨39440213115862931991068881, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52586950821150575988091841 39440213115862931991068881)
          ·
            refine ⟨29580159836897198993301661, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 39440213115862931991068881 29580159836897198993301661)
            ·
              refine ⟨11092559938836449622488123, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 29580159836897198993301661 11092559938836449622488123)
              ·
                refine ⟨16638839908254674433732185, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11092559938836449622488123 16638839908254674433732185)
                ·
                  refine ⟨12479129931191005825299139, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16638839908254674433732185 12479129931191005825299139)
                  ·
                    refine ⟨18718694896786508737948709, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12479129931191005825299139 18718694896786508737948709)
                    ·
                      refine ⟨3509755293147470388365383, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18718694896786508737948709 3509755293147470388365383)
                      ·
                        rfl

theorem cell23_6835224_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 2, 3, 2, 2, 3, 1, 2, 1, 4].length) (baseStart_6835224 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835224 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835224 prefixEnd_6835224 := by exact prefixLift 6835224
  have htrace : WordTrace (prefixWord ++ tailWord_6835224) baseStart_6835224 baseEnd_6835224 := by
    simpa [prefixWord, tailWord_6835224, baseEnd_6835224] using wordTrace_append hprefix tailTrace_6835224
  have hstable : (prefixWord ++ tailWord_6835224).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835224).length < 2 ^ (prefixWord ++ tailWord_6835224).sum := by decide
  have hdescent : baseEnd_6835224 < baseStart_6835224 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835224) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835264 : List Nat := [2, 1, 1, 2, 2, 3, 5, 1, 6]
def baseStart_6835264 : Nat := 118140960795 + 6835264 * 2 ^ 59
def prefixEnd_6835264 : Nat := 4983230072969 + 3 ^ 40 * 6835264 * 2
def baseEnd_6835264 : Nat := 389975092485961136873911

theorem tailTrace_6835264 : CollatzResearch.WordTrace tailWord_6835264 prefixEnd_6835264 389975092485961136873911 := by
  unfold tailWord_6835264
  simp only [CollatzResearch.WordTrace]
  refine ⟨124651279554506686498612423, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166201706072675581998149897 124651279554506686498612423)
  ·
    refine ⟨186976919331760029747918635, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 124651279554506686498612423 186976919331760029747918635)
    ·
      refine ⟨280465378997640044621877953, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186976919331760029747918635 280465378997640044621877953)
      ·
        refine ⟨210349034248230033466408465, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280465378997640044621877953 210349034248230033466408465)
        ·
          refine ⟨157761775686172525099806349, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210349034248230033466408465 157761775686172525099806349)
          ·
            refine ⟨59160665882314696912427381, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157761775686172525099806349 59160665882314696912427381)
            ·
              refine ⟨5546312426467002835540067, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 59160665882314696912427381 5546312426467002835540067)
              ·
                refine ⟨8319468639700504253310101, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546312426467002835540067 8319468639700504253310101)
                ·
                  refine ⟨389975092485961136873911, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8319468639700504253310101 389975092485961136873911)
                  ·
                    rfl

theorem cell23_6835264_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 1, 1, 2, 2, 3, 5, 1, 6].length) (baseStart_6835264 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835264 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835264 prefixEnd_6835264 := by exact prefixLift 6835264
  have htrace : WordTrace (prefixWord ++ tailWord_6835264) baseStart_6835264 baseEnd_6835264 := by
    simpa [prefixWord, tailWord_6835264, baseEnd_6835264] using wordTrace_append hprefix tailTrace_6835264
  have hstable : (prefixWord ++ tailWord_6835264).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835264).length < 2 ^ (prefixWord ++ tailWord_6835264).sum := by decide
  have hdescent : baseEnd_6835264 < baseStart_6835264 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835264) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835301 : List Nat := [1, 3, 1, 3, 2, 1, 3, 2, 2, 3, 2]
def baseStart_6835301 : Nat := 118140960795 + 6835301 * 2 ^ 59
def prefixEnd_6835301 : Nat := 4983230072969 + 3 ^ 40 * 6835301 * 2
def baseEnd_6835301 : Nat := 3509794831157866587102529

theorem tailTrace_6835301 : CollatzResearch.WordTrace tailWord_6835301 prefixEnd_6835301 3509794831157866587102529 := by
  unfold tailWord_6835301
  simp only [CollatzResearch.WordTrace]
  refine ⟨249303908609879328316321757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166202605739919552210881171 249303908609879328316321757)
  ·
    refine ⟨93488965728704748118620659, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249303908609879328316321757 93488965728704748118620659)
    ·
      refine ⟨140233448593057122177930989, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93488965728704748118620659 140233448593057122177930989)
      ·
        refine ⟨52587543222396420816724121, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140233448593057122177930989 52587543222396420816724121)
        ·
          refine ⟨39440657416797315612543091, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52587543222396420816724121 39440657416797315612543091)
          ·
            refine ⟨59160986125195973418814637, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39440657416797315612543091 59160986125195973418814637)
            ·
              refine ⟨22185369796948490032055489, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 59160986125195973418814637 22185369796948490032055489)
              ·
                refine ⟨16639027347711367524041617, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 22185369796948490032055489 16639027347711367524041617)
                ·
                  refine ⟨12479270510783525643031213, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16639027347711367524041617 12479270510783525643031213)
                  ·
                    refine ⟨4679726441543822116136705, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12479270510783525643031213 4679726441543822116136705)
                    ·
                      refine ⟨3509794831157866587102529, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679726441543822116136705 3509794831157866587102529)
                      ·
                        rfl

theorem cell23_6835301_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 3, 2, 1, 3, 2, 2, 3, 2].length) (baseStart_6835301 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835301 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835301 prefixEnd_6835301 := by exact prefixLift 6835301
  have htrace : WordTrace (prefixWord ++ tailWord_6835301) baseStart_6835301 baseEnd_6835301 := by
    simpa [prefixWord, tailWord_6835301, baseEnd_6835301] using wordTrace_append hprefix tailTrace_6835301
  have hstable : (prefixWord ++ tailWord_6835301).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835301).length < 2 ^ (prefixWord ++ tailWord_6835301).sum := by decide
  have hdescent : baseEnd_6835301 < baseStart_6835301 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835301) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835314 : List Nat := [3, 2, 1, 2, 2, 1, 2, 2, 3, 1, 4]
def baseStart_6835314 : Nat := 118140960795 + 6835314 * 2 ^ 59
def prefixEnd_6835314 : Nat := 4983230072969 + 3 ^ 40 * 6835314 * 2
def baseEnd_6835314 : Nat := 3509801506406375036239969

theorem tailTrace_6835314 : CollatzResearch.WordTrace tailWord_6835314 prefixEnd_6835314 3509801506406375036239969 := by
  unfold tailWord_6835314
  simp only [CollatzResearch.WordTrace]
  refine ⟨62326095689708057884136249, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166202921839221487691029997 62326095689708057884136249)
  ·
    refine ⟨46744571767281043413102187, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62326095689708057884136249 46744571767281043413102187)
    ·
      refine ⟨70116857650921565119653281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 46744571767281043413102187 70116857650921565119653281)
      ·
        refine ⟨52587643238191173839739961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 70116857650921565119653281 52587643238191173839739961)
        ·
          refine ⟨39440732428643380379804971, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 52587643238191173839739961 39440732428643380379804971)
          ·
            refine ⟨59161098642965070569707457, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39440732428643380379804971 59161098642965070569707457)
            ·
              refine ⟨44370823982223802927280593, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59161098642965070569707457 44370823982223802927280593)
              ·
                refine ⟨33278117986667852195460445, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 44370823982223802927280593 33278117986667852195460445)
                ·
                  refine ⟨12479294245000444573297667, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33278117986667852195460445 12479294245000444573297667)
                  ·
                    refine ⟨18718941367500666859946501, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12479294245000444573297667 18718941367500666859946501)
                    ·
                      refine ⟨3509801506406375036239969, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18718941367500666859946501 3509801506406375036239969)
                      ·
                        rfl

theorem cell23_6835314_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 1, 2, 2, 1, 2, 2, 3, 1, 4].length) (baseStart_6835314 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835314 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835314 prefixEnd_6835314 := by exact prefixLift 6835314
  have htrace : WordTrace (prefixWord ++ tailWord_6835314) baseStart_6835314 baseEnd_6835314 := by
    simpa [prefixWord, tailWord_6835314, baseEnd_6835314] using wordTrace_append hprefix tailTrace_6835314
  have hstable : (prefixWord ++ tailWord_6835314).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835314).length < 2 ^ (prefixWord ++ tailWord_6835314).sum := by decide
  have hdescent : baseEnd_6835314 < baseStart_6835314 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835314) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835327 : List Nat := [1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 4]
def baseStart_6835327 : Nat := 118140960795 + 6835327 * 2 ^ 59
def prefixEnd_6835327 : Nat := 4983230072969 + 3 ^ 40 * 6835327 * 2
def baseEnd_6835327 : Nat := 3509808181654883485377409

theorem tailTrace_6835327 : CollatzResearch.WordTrace tailWord_6835327 prefixEnd_6835327 3509808181654883485377409 := by
  unfold tailWord_6835327
  simp only [CollatzResearch.WordTrace]
  refine ⟨249304856907785134756768235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166203237938523423171178823 249304856907785134756768235)
  ·
    refine ⟨373957285361677702135152353, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249304856907785134756768235 373957285361677702135152353)
    ·
      refine ⟨280467964021258276601364265, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373957285361677702135152353 280467964021258276601364265)
      ·
        refine ⟨210350973015943707451023199, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280467964021258276601364265 210350973015943707451023199)
        ·
          refine ⟨315526459523915561176534799, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210350973015943707451023199 315526459523915561176534799)
          ·
            refine ⟨473289689285873341764802199, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315526459523915561176534799 473289689285873341764802199)
            ·
              refine ⟨709934533928810012647203299, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 473289689285873341764802199 709934533928810012647203299)
              ·
                refine ⟨1064901800893215018970804949, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 709934533928810012647203299 1064901800893215018970804949)
                ·
                  refine ⟨24958635958434727007128241, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 7 1064901800893215018970804949 24958635958434727007128241)
                  ·
                    refine ⟨18718976968826045255346181, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 24958635958434727007128241 18718976968826045255346181)
                    ·
                      refine ⟨3509808181654883485377409, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18718976968826045255346181 3509808181654883485377409)
                      ·
                        rfl

theorem cell23_6835327_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 1, 1, 1, 1, 7, 2, 4].length) (baseStart_6835327 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835327 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835327 prefixEnd_6835327 := by exact prefixLift 6835327
  have htrace : WordTrace (prefixWord ++ tailWord_6835327) baseStart_6835327 baseEnd_6835327 := by
    simpa [prefixWord, tailWord_6835327, baseEnd_6835327] using wordTrace_append hprefix tailTrace_6835327
  have hstable : (prefixWord ++ tailWord_6835327).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835327).length < 2 ^ (prefixWord ++ tailWord_6835327).sum := by decide
  have hdescent : baseEnd_6835327 < baseStart_6835327 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835327) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835331 : List Nat := [1, 1, 1, 3, 3, 2, 2, 1, 5, 2, 2]
def baseStart_6835331 : Nat := 118140960795 + 6835331 * 2 ^ 59
def prefixEnd_6835331 : Nat := 4983230072969 + 3 ^ 40 * 6835331 * 2
def baseEnd_6835331 : Nat := 3509810235577501469727391

theorem tailTrace_6835331 : CollatzResearch.WordTrace tailWord_6835331 prefixEnd_6835331 3509810235577501469727391 := by
  unfold tailWord_6835331
  simp only [CollatzResearch.WordTrace]
  refine ⟨249305002799770643439913847, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166203335199847095626609231 249305002799770643439913847)
  ·
    refine ⟨373957504199655965159870771, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249305002799770643439913847 373957504199655965159870771)
    ·
      refine ⟨560936256299483947739806157, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373957504199655965159870771 560936256299483947739806157)
      ·
        refine ⟨210351096112306480402427309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 560936256299483947739806157 210351096112306480402427309)
        ·
          refine ⟨78881661042114930150910241, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 210351096112306480402427309 78881661042114930150910241)
          ·
            refine ⟨59161245781586197613182681, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 78881661042114930150910241 59161245781586197613182681)
            ·
              refine ⟨44370934336189648209887011, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 59161245781586197613182681 44370934336189648209887011)
              ·
                refine ⟨66556401504284472314830517, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44370934336189648209887011 66556401504284472314830517)
                ·
                  refine ⟨6239662641026669279515361, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 5 66556401504284472314830517 6239662641026669279515361)
                  ·
                    refine ⟨4679746980770001959636521, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6239662641026669279515361 4679746980770001959636521)
                    ·
                      refine ⟨3509810235577501469727391, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679746980770001959636521 3509810235577501469727391)
                      ·
                        rfl

theorem cell23_6835331_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 3, 3, 2, 2, 1, 5, 2, 2].length) (baseStart_6835331 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835331 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835331 prefixEnd_6835331 := by exact prefixLift 6835331
  have htrace : WordTrace (prefixWord ++ tailWord_6835331) baseStart_6835331 baseEnd_6835331 := by
    simpa [prefixWord, tailWord_6835331, baseEnd_6835331] using wordTrace_append hprefix tailTrace_6835331
  have hstable : (prefixWord ++ tailWord_6835331).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835331).length < 2 ^ (prefixWord ++ tailWord_6835331).sum := by decide
  have hdescent : baseEnd_6835331 < baseStart_6835331 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835331) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835337 : List Nat := [1, 2, 1, 1, 4, 3, 2, 9]
def baseStart_6835337 : Nat := 118140960795 + 6835337 * 2 ^ 59
def prefixEnd_6835337 : Nat := 4983230072969 + 3 ^ 40 * 6835337 * 2
def baseEnd_6835337 : Nat := 129993085794867720231569

theorem tailTrace_6835337 : CollatzResearch.WordTrace tailWord_6835337 prefixEnd_6835337 129993085794867720231569 := by
  unfold tailWord_6835337
  simp only [CollatzResearch.WordTrace]
  refine ⟨249305221637748906464632265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166203481091832604309754843 249305221637748906464632265)
  ·
    refine ⟨186978916228311679848474199, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249305221637748906464632265 186978916228311679848474199)
    ·
      refine ⟨280468374342467519772711299, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 186978916228311679848474199 280468374342467519772711299)
      ·
        refine ⟨420702561513701279659066949, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 280468374342467519772711299 420702561513701279659066949)
        ·
          refine ⟨78881730283818989936075053, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 420702561513701279659066949 78881730283818989936075053)
          ·
            refine ⟨29580648856432121226028145, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 78881730283818989936075053 29580648856432121226028145)
            ·
              refine ⟨22185486642324090919521109, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 29580648856432121226028145 22185486642324090919521109)
              ·
                refine ⟨129993085794867720231569, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 9 22185486642324090919521109 129993085794867720231569)
                ·
                  rfl

theorem cell23_6835337_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 9].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 1, 1, 4, 3, 2, 9].length) (baseStart_6835337 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835337 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835337 prefixEnd_6835337 := by exact prefixLift 6835337
  have htrace : WordTrace (prefixWord ++ tailWord_6835337) baseStart_6835337 baseEnd_6835337 := by
    simpa [prefixWord, tailWord_6835337, baseEnd_6835337] using wordTrace_append hprefix tailTrace_6835337
  have hstable : (prefixWord ++ tailWord_6835337).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835337).length < 2 ^ (prefixWord ++ tailWord_6835337).sum := by decide
  have hdescent : baseEnd_6835337 < baseStart_6835337 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835337) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835351 : List Nat := [1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 5]
def baseStart_6835351 : Nat := 118140960795 + 6835351 * 2 ^ 59
def prefixEnd_6835351 : Nat := 4983230072969 + 3 ^ 40 * 6835351 * 2
def baseEnd_6835351 : Nat := 3509820505190591391477299

theorem tailTrace_6835351 : CollatzResearch.WordTrace tailWord_6835351 prefixEnd_6835351 3509820505190591391477299 := by
  unfold tailWord_6835351
  simp only [CollatzResearch.WordTrace]
  refine ⟨249305732259698186855641907, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166203821506465457903761271 249305732259698186855641907)
  ·
    refine ⟨373958598389547280283462861, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249305732259698186855641907 373958598389547280283462861)
    ·
      refine ⟨140234474396080230106298573, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373958598389547280283462861 140234474396080230106298573)
      ·
        refine ⟨52587927898530086289861965, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 140234474396080230106298573 52587927898530086289861965)
        ·
          refine ⟨19720472961948782358698237, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 52587927898530086289861965 19720472961948782358698237)
          ·
            refine ⟨7395177360730793384511839, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 19720472961948782358698237 7395177360730793384511839)
            ·
              refine ⟨11092766041096190076767759, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395177360730793384511839 11092766041096190076767759)
              ·
                refine ⟨16639149061644285115151639, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11092766041096190076767759 16639149061644285115151639)
                ·
                  refine ⟨24958723592466427672727459, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16639149061644285115151639 24958723592466427672727459)
                  ·
                    refine ⟨37438085388699641509091189, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24958723592466427672727459 37438085388699641509091189)
                    ·
                      refine ⟨3509820505190591391477299, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37438085388699641509091189 3509820505190591391477299)
                      ·
                        rfl

theorem cell23_6835351_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 3, 3, 3, 1, 1, 1, 1, 5].length) (baseStart_6835351 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835351 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835351 prefixEnd_6835351 := by exact prefixLift 6835351
  have htrace : WordTrace (prefixWord ++ tailWord_6835351) baseStart_6835351 baseEnd_6835351 := by
    simpa [prefixWord, tailWord_6835351, baseEnd_6835351] using wordTrace_append hprefix tailTrace_6835351
  have hstable : (prefixWord ++ tailWord_6835351).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835351).length < 2 ^ (prefixWord ++ tailWord_6835351).sum := by decide
  have hdescent : baseEnd_6835351 < baseStart_6835351 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835351) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835358 : List Nat := [4, 3, 1, 1, 2, 1, 1, 4, 2, 4]
def baseStart_6835358 : Nat := 118140960795 + 6835358 * 2 ^ 59
def prefixEnd_6835358 : Nat := 4983230072969 + 3 ^ 40 * 6835358 * 2
def baseEnd_6835358 : Nat := 1169941366518390954696589

theorem tailTrace_6835358 : CollatzResearch.WordTrace tailWord_6835358 prefixEnd_6835358 1169941366518390954696589 := by
  unfold tailWord_6835358
  simp only [CollatzResearch.WordTrace]
  refine ⟨31163248446334103381393341, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166203991713781884700764485 31163248446334103381393341)
  ·
    refine ⟨11686218167375288768022503, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 31163248446334103381393341 11686218167375288768022503)
    ·
      refine ⟨17529327251062933152033755, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11686218167375288768022503 17529327251062933152033755)
      ·
        refine ⟨26293990876594399728050633, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17529327251062933152033755 26293990876594399728050633)
        ·
          refine ⟨19720493157445799796037975, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 26293990876594399728050633 19720493157445799796037975)
          ·
            refine ⟨29580739736168699694056963, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 19720493157445799796037975 29580739736168699694056963)
            ·
              refine ⟨44371109604253049541085445, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 29580739736168699694056963 44371109604253049541085445)
              ·
                refine ⟨8319583050797446788953521, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 44371109604253049541085445 8319583050797446788953521)
                ·
                  refine ⟨6239687288098085091715141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 8319583050797446788953521 6239687288098085091715141)
                  ·
                    refine ⟨1169941366518390954696589, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 6239687288098085091715141 1169941366518390954696589)
                    ·
                      rfl

theorem cell23_6835358_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 3, 1, 1, 2, 1, 1, 4, 2, 4].length) (baseStart_6835358 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835358 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835358 prefixEnd_6835358 := by exact prefixLift 6835358
  have htrace : WordTrace (prefixWord ++ tailWord_6835358) baseStart_6835358 baseEnd_6835358 := by
    simpa [prefixWord, tailWord_6835358, baseEnd_6835358] using wordTrace_append hprefix tailTrace_6835358
  have hstable : (prefixWord ++ tailWord_6835358).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835358).length < 2 ^ (prefixWord ++ tailWord_6835358).sum := by decide
  have hdescent : baseEnd_6835358 < baseStart_6835358 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835358) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835359 : List Nat := [1, 1, 2, 6, 3, 1, 2, 2, 1, 1, 3]
def baseStart_6835359 : Nat := 118140960795 + 6835359 * 2 ^ 59
def prefixEnd_6835359 : Nat := 4983230072969 + 3 ^ 40 * 6835359 * 2
def baseEnd_6835359 : Nat := 3509824613035827360177263

theorem tailTrace_6835359 : CollatzResearch.WordTrace tailWord_6835359 prefixEnd_6835359 3509824613035827360177263 := by
  unfold tailWord_6835359
  simp only [CollatzResearch.WordTrace]
  refine ⟨249306024043669204221933131, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166204016029112802814622087 249306024043669204221933131)
  ·
    refine ⟨373959036065503806332899697, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249306024043669204221933131 373959036065503806332899697)
    ·
      refine ⟨280469277049127854749674773, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373959036065503806332899697 280469277049127854749674773)
      ·
        refine ⟨13146997361677868191391005, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 6 280469277049127854749674773 13146997361677868191391005)
        ·
          refine ⟨4930124010629200571771627, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13146997361677868191391005 4930124010629200571771627)
          ·
            refine ⟨7395186015943800857657441, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930124010629200571771627 7395186015943800857657441)
            ·
              refine ⟨5546389511957850643243081, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 2 7395186015943800857657441 5546389511957850643243081)
              ·
                refine ⟨4159792133968387982432311, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 5546389511957850643243081 4159792133968387982432311)
                ·
                  refine ⟨6239688200952581973648467, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159792133968387982432311 6239688200952581973648467)
                  ·
                    refine ⟨9359532301428872960472701, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6239688200952581973648467 9359532301428872960472701)
                    ·
                      refine ⟨3509824613035827360177263, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9359532301428872960472701 3509824613035827360177263)
                      ·
                        rfl

theorem cell23_6835359_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 6, 3, 1, 2, 2, 1, 1, 3].length) (baseStart_6835359 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835359 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835359 prefixEnd_6835359 := by exact prefixLift 6835359
  have htrace : WordTrace (prefixWord ++ tailWord_6835359) baseStart_6835359 baseEnd_6835359 := by
    simpa [prefixWord, tailWord_6835359, baseEnd_6835359] using wordTrace_append hprefix tailTrace_6835359
  have hstable : (prefixWord ++ tailWord_6835359).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835359).length < 2 ^ (prefixWord ++ tailWord_6835359).sum := by decide
  have hdescent : baseEnd_6835359 < baseStart_6835359 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835359) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835365 : List Nat := [1, 3, 1, 2, 1, 5, 1, 4, 1, 2, 2]
def baseStart_6835365 : Nat := 118140960795 + 6835365 * 2 ^ 59
def prefixEnd_6835365 : Nat := 4983230072969 + 3 ^ 40 * 6835365 * 2
def baseEnd_6835365 : Nat := 3509827693919754336702235

theorem tailTrace_6835365 : CollatzResearch.WordTrace tailWord_6835365 prefixEnd_6835365 3509827693919754336702235 := by
  unfold tailWord_6835365
  simp only [CollatzResearch.WordTrace]
  refine ⟨249306242881647467246651549, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166204161921098311497767699 249306242881647467246651549)
  ·
    refine ⟨93489841080617800217494331, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249306242881647467246651549 93489841080617800217494331)
    ·
      refine ⟨140234761620926700326241497, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93489841080617800217494331 140234761620926700326241497)
      ·
        refine ⟨105176071215695025244681123, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 140234761620926700326241497 105176071215695025244681123)
        ·
          refine ⟨157764106823542537867021685, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 105176071215695025244681123 157764106823542537867021685)
          ·
            refine ⟨14790385014707112925033283, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 157764106823542537867021685 14790385014707112925033283)
            ·
              refine ⟨22185577522060669387549925, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14790385014707112925033283 22185577522060669387549925)
              ·
                refine ⟨4159795785386375510165611, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 4 22185577522060669387549925 4159795785386375510165611)
                ·
                  refine ⟨6239693678079563265248417, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159795785386375510165611 6239693678079563265248417)
                  ·
                    refine ⟨4679770258559672448936313, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 6239693678079563265248417 4679770258559672448936313)
                    ·
                      refine ⟨3509827693919754336702235, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679770258559672448936313 3509827693919754336702235)
                      ·
                        rfl

theorem cell23_6835365_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 2, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 2, 1, 5, 1, 4, 1, 2, 2].length) (baseStart_6835365 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835365 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835365 prefixEnd_6835365 := by exact prefixLift 6835365
  have htrace : WordTrace (prefixWord ++ tailWord_6835365) baseStart_6835365 baseEnd_6835365 := by
    simpa [prefixWord, tailWord_6835365, baseEnd_6835365] using wordTrace_append hprefix tailTrace_6835365
  have hstable : (prefixWord ++ tailWord_6835365).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835365).length < 2 ^ (prefixWord ++ tailWord_6835365).sum := by decide
  have hdescent : baseEnd_6835365 < baseStart_6835365 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835365) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835391 : List Nat := [1, 1, 2, 2, 2, 2, 4, 1, 3, 3, 2]
def baseStart_6835391 : Nat := 118140960795 + 6835391 * 2 ^ 59
def prefixEnd_6835391 : Nat := 4983230072969 + 3 ^ 40 * 6835391 * 2
def baseEnd_6835391 : Nat := 3509841044416771234977115

theorem tailTrace_6835391 : CollatzResearch.WordTrace tailWord_6835391 prefixEnd_6835391 3509841044416771234977115 := by
  unfold tailWord_6835391
  simp only [CollatzResearch.WordTrace]
  refine ⟨249307191179553273687098027, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166204794119702182458065351 249307191179553273687098027)
  ·
    refine ⟨373960786769329910530647041, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249307191179553273687098027 373960786769329910530647041)
    ·
      refine ⟨280470590076997432897985281, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 373960786769329910530647041 280470590076997432897985281)
      ·
        refine ⟨210352942557748074673488961, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 2 280470590076997432897985281 210352942557748074673488961)
        ·
          refine ⟨157764706918311056005116721, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210352942557748074673488961 157764706918311056005116721)
          ·
            refine ⟨118323530188733292003837541, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 157764706918311056005116721 118323530188733292003837541)
            ·
              refine ⟨22185661910387492250719539, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 118323530188733292003837541 22185661910387492250719539)
              ·
                refine ⟨33278492865581238376079309, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22185661910387492250719539 33278492865581238376079309)
                ·
                  refine ⟨12479434824592964391029741, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 33278492865581238376079309 12479434824592964391029741)
                  ·
                    refine ⟨4679788059222361646636153, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 3 12479434824592964391029741 4679788059222361646636153)
                    ·
                      refine ⟨3509841044416771234977115, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679788059222361646636153 3509841044416771234977115)
                      ·
                        rfl

theorem cell23_6835391_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 2, 2, 2, 2, 4, 1, 3, 3, 2].length) (baseStart_6835391 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835391 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835391 prefixEnd_6835391 := by exact prefixLift 6835391
  have htrace : WordTrace (prefixWord ++ tailWord_6835391) baseStart_6835391 baseEnd_6835391 := by
    simpa [prefixWord, tailWord_6835391, baseEnd_6835391] using wordTrace_append hprefix tailTrace_6835391
  have hstable : (prefixWord ++ tailWord_6835391).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835391).length < 2 ^ (prefixWord ++ tailWord_6835391).sum := by decide
  have hdescent : baseEnd_6835391 < baseStart_6835391 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835391) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835397 : List Nat := [1, 3, 1, 1, 1, 1, 3, 1, 3, 8]
def baseStart_6835397 : Nat := 118140960795 + 6835397 * 2 ^ 59
def prefixEnd_6835397 : Nat := 4983230072969 + 3 ^ 40 * 6835397 * 2
def baseEnd_6835397 : Nat := 1169948041766899403834029

theorem tailTrace_6835397 : CollatzResearch.WordTrace tailWord_6835397 prefixEnd_6835397 1169948041766899403834029 := by
  unfold tailWord_6835397
  simp only [CollatzResearch.WordTrace]
  refine ⟨249307410017531536711816445, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166204940011687691141210963 249307410017531536711816445)
  ·
    refine ⟨93490278756574326266931167, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 3 249307410017531536711816445 93490278756574326266931167)
    ·
      refine ⟨140235418134861489400396751, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 93490278756574326266931167 140235418134861489400396751)
      ·
        refine ⟨210353127202292234100595127, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140235418134861489400396751 210353127202292234100595127)
        ·
          refine ⟨315529690803438351150892691, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 210353127202292234100595127 315529690803438351150892691)
          ·
            refine ⟨473294536205157526726339037, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 315529690803438351150892691 473294536205157526726339037)
            ·
              refine ⟨177485451076934072522377139, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 473294536205157526726339037 177485451076934072522377139)
              ·
                refine ⟨266228176615401108783565709, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 177485451076934072522377139 266228176615401108783565709)
                ·
                  refine ⟨99835566230775415793837141, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 3 266228176615401108783565709 99835566230775415793837141)
                  ·
                    refine ⟨1169948041766899403834029, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 8 99835566230775415793837141 1169948041766899403834029)
                    ·
                      rfl

theorem cell23_6835397_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 8].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 3, 1, 1, 1, 1, 3, 1, 3, 8].length) (baseStart_6835397 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835397 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835397 prefixEnd_6835397 := by exact prefixLift 6835397
  have htrace : WordTrace (prefixWord ++ tailWord_6835397) baseStart_6835397 baseEnd_6835397 := by
    simpa [prefixWord, tailWord_6835397, baseEnd_6835397] using wordTrace_append hprefix tailTrace_6835397
  have hstable : (prefixWord ++ tailWord_6835397).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835397).length < 2 ^ (prefixWord ++ tailWord_6835397).sum := by decide
  have hdescent : baseEnd_6835397 < baseStart_6835397 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835397) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835438 : List Nat := [4, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2]
def baseStart_6835438 : Nat := 118140960795 + 6835438 * 2 ^ 59
def prefixEnd_6835438 : Nat := 4983230072969 + 3 ^ 40 * 6835438 * 2
def baseEnd_6835438 : Nat := 3509865178007532551089399

theorem tailTrace_6835438 : CollatzResearch.WordTrace tailWord_6835438 prefixEnd_6835438 3509865178007532551089399 := by
  unfold tailWord_6835438
  simp only [CollatzResearch.WordTrace]
  refine ⟨31163613176297875089257371, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 4 166205936940255333809372645 31163613176297875089257371)
  ·
    refine ⟨46745419764446812633886057, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 31163613176297875089257371 46745419764446812633886057)
    ·
      refine ⟨35059064823335109475414543, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 2 46745419764446812633886057 35059064823335109475414543)
      ·
        refine ⟨52588597235002664213121815, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35059064823335109475414543 52588597235002664213121815)
        ·
          refine ⟨78882895852503996319682723, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52588597235002664213121815 78882895852503996319682723)
          ·
            refine ⟨118324343778755994479524085, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78882895852503996319682723 118324343778755994479524085)
            ·
              refine ⟨11092907229258374482455383, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 5 118324343778755994479524085 11092907229258374482455383)
              ·
                refine ⟨16639360843887561723683075, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11092907229258374482455383 16639360843887561723683075)
                ·
                  refine ⟨24959041265831342585524613, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 16639360843887561723683075 24959041265831342585524613)
                  ·
                    refine ⟨4679820237343376734785865, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24959041265831342585524613 4679820237343376734785865)
                    ·
                      refine ⟨3509865178007532551089399, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679820237343376734785865 3509865178007532551089399)
                      ·
                        rfl

theorem cell23_6835438_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 4, 1, 2, 1, 1, 1, 5, 1, 1, 4, 2].length) (baseStart_6835438 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835438 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835438 prefixEnd_6835438 := by exact prefixLift 6835438
  have htrace : WordTrace (prefixWord ++ tailWord_6835438) baseStart_6835438 baseEnd_6835438 := by
    simpa [prefixWord, tailWord_6835438, baseEnd_6835438] using wordTrace_append hprefix tailTrace_6835438
  have hstable : (prefixWord ++ tailWord_6835438).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835438).length < 2 ^ (prefixWord ++ tailWord_6835438).sum := by decide
  have hdescent : baseEnd_6835438 < baseStart_6835438 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835438) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835458 : List Nat := [3, 4, 1, 1, 3, 1, 1, 1, 2, 1, 5]
def baseStart_6835458 : Nat := 118140960795 + 6835458 * 2 ^ 59
def prefixEnd_6835458 : Nat := 4983230072969 + 3 ^ 40 * 6835458 * 2
def baseEnd_6835458 : Nat := 3509875447620622472839307

theorem tailTrace_6835458 : CollatzResearch.WordTrace tailWord_6835458 prefixEnd_6835458 3509875447620622472839307 := by
  unfold tailWord_6835458
  simp only [CollatzResearch.WordTrace]
  refine ⟨62327408717577636032446757, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166206423246873696086524685 62327408717577636032446757)
  ·
    refine ⟨11686389134545806756083767, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 4 62327408717577636032446757 11686389134545806756083767)
    ·
      refine ⟨17529583701818710134125651, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11686389134545806756083767 17529583701818710134125651)
      ·
        refine ⟨26294375552728065201188477, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17529583701818710134125651 26294375552728065201188477)
        ·
          refine ⟨9860390832273024450445679, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 26294375552728065201188477 9860390832273024450445679)
          ·
            refine ⟨14790586248409536675668519, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9860390832273024450445679 14790586248409536675668519)
            ·
              refine ⟨22185879372614305013502779, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 14790586248409536675668519 22185879372614305013502779)
              ·
                refine ⟨33278819058921457520254169, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 22185879372614305013502779 33278819058921457520254169)
                ·
                  refine ⟨24959114294191093140190627, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 33278819058921457520254169 24959114294191093140190627)
                  ·
                    refine ⟨37438671441286639710285941, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 24959114294191093140190627 37438671441286639710285941)
                    ·
                      refine ⟨3509875447620622472839307, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 5 37438671441286639710285941 3509875447620622472839307)
                      ·
                        rfl

theorem cell23_6835458_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 1, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 4, 1, 1, 3, 1, 1, 1, 2, 1, 5].length) (baseStart_6835458 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835458 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835458 prefixEnd_6835458 := by exact prefixLift 6835458
  have htrace : WordTrace (prefixWord ++ tailWord_6835458) baseStart_6835458 baseEnd_6835458 := by
    simpa [prefixWord, tailWord_6835458, baseEnd_6835458] using wordTrace_append hprefix tailTrace_6835458
  have hstable : (prefixWord ++ tailWord_6835458).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835458).length < 2 ^ (prefixWord ++ tailWord_6835458).sum := by decide
  have hdescent : baseEnd_6835458 < baseStart_6835458 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835458) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835484 : List Nat := [2, 2, 3, 1, 1, 1, 3, 1, 1, 1, 7]
def baseStart_6835484 : Nat := 118140960795 + 6835484 * 2 ^ 59
def prefixEnd_6835484 : Nat := 4983230072969 + 3 ^ 40 * 6835484 * 2
def baseEnd_6835484 : Nat := 3509888798117639371114187

theorem tailTrace_6835484 : CollatzResearch.WordTrace tailWord_6835484 prefixEnd_6835484 3509888798117639371114187 := by
  unfold tailWord_6835484
  simp only [CollatzResearch.WordTrace]
  refine ⟨124655291584108175285116753, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166207055445477567046822337 124655291584108175285116753)
  ·
    refine ⟨93491468688081131463837565, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 124655291584108175285116753 93491468688081131463837565)
    ·
      refine ⟨35059300758030424298939087, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93491468688081131463837565 35059300758030424298939087)
      ·
        refine ⟨52588951137045636448408631, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35059300758030424298939087 52588951137045636448408631)
        ·
          refine ⟨78883426705568454672612947, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52588951137045636448408631 78883426705568454672612947)
          ·
            refine ⟨118325140058352682008919421, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 78883426705568454672612947 118325140058352682008919421)
            ·
              refine ⟨44371927521882255753344783, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 118325140058352682008919421 44371927521882255753344783)
              ·
                refine ⟨66557891282823383630017175, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 44371927521882255753344783 66557891282823383630017175)
                ·
                  refine ⟨99836836924235075445025763, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 66557891282823383630017175 99836836924235075445025763)
                  ·
                    refine ⟨149755255386352613167538645, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 99836836924235075445025763 149755255386352613167538645)
                    ·
                      refine ⟨3509888798117639371114187, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 7 149755255386352613167538645 3509888798117639371114187)
                      ·
                        rfl

theorem cell23_6835484_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 1, 7].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 2, 3, 1, 1, 1, 3, 1, 1, 1, 7].length) (baseStart_6835484 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835484 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835484 prefixEnd_6835484 := by exact prefixLift 6835484
  have htrace : WordTrace (prefixWord ++ tailWord_6835484) baseStart_6835484 baseEnd_6835484 := by
    simpa [prefixWord, tailWord_6835484, baseEnd_6835484] using wordTrace_append hprefix tailTrace_6835484
  have hstable : (prefixWord ++ tailWord_6835484).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835484).length < 2 ^ (prefixWord ++ tailWord_6835484).sum := by decide
  have hdescent : baseEnd_6835484 < baseStart_6835484 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835484) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835508 : List Nat := [2, 5, 1, 1, 1, 1, 4, 1, 2, 5]
def baseStart_6835508 : Nat := 118140960795 + 6835508 * 2 ^ 59
def prefixEnd_6835508 : Nat := 4983230072969 + 3 ^ 40 * 6835508 * 2
def baseEnd_6835508 : Nat := 1169967040551115759071359

theorem tailTrace_6835508 : CollatzResearch.WordTrace tailWord_6835508 prefixEnd_6835508 1169967040551115759071359 := by
  unfold tailWord_6835508
  simp only [CollatzResearch.WordTrace]
  refine ⟨124655729260064701334553589, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 2 166207639013419601779404785 124655729260064701334553589)
  ·
    refine ⟨11686474618131065750114399, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 124655729260064701334553589 11686474618131065750114399)
    ·
      refine ⟨17529711927196598625171599, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 11686474618131065750114399 17529711927196598625171599)
      ·
        refine ⟨26294567890794897937757399, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 17529711927196598625171599 26294567890794897937757399)
        ·
          refine ⟨39441851836192346906636099, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 26294567890794897937757399 39441851836192346906636099)
          ·
            refine ⟨59162777754288520359954149, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 39441851836192346906636099 59162777754288520359954149)
            ·
              refine ⟨11093020828929097567491403, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 4 59162777754288520359954149 11093020828929097567491403)
              ·
                refine ⟨16639531243393646351237105, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093020828929097567491403 16639531243393646351237105)
                ·
                  refine ⟨12479648432545234763427829, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16639531243393646351237105 12479648432545234763427829)
                  ·
                    refine ⟨1169967040551115759071359, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 5 12479648432545234763427829 1169967040551115759071359)
                    ·
                      rfl

theorem cell23_6835508_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 5].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 2, 5, 1, 1, 1, 1, 4, 1, 2, 5].length) (baseStart_6835508 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835508 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835508 prefixEnd_6835508 := by exact prefixLift 6835508
  have htrace : WordTrace (prefixWord ++ tailWord_6835508) baseStart_6835508 baseEnd_6835508 := by
    simpa [prefixWord, tailWord_6835508, baseEnd_6835508] using wordTrace_append hprefix tailTrace_6835508
  have hstable : (prefixWord ++ tailWord_6835508).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835508).length < 2 ^ (prefixWord ++ tailWord_6835508).sum := by decide
  have hdescent : baseEnd_6835508 < baseStart_6835508 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835508) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835511 : List Nat := [1, 1, 3, 1, 2, 1, 1, 1, 6, 4, 2]
def baseStart_6835511 : Nat := 118140960795 + 6835511 * 2 ^ 59
def prefixEnd_6835511 : Nat := 4983230072969 + 3 ^ 40 * 6835511 * 2
def baseEnd_6835511 : Nat := 3509902662095310765476563

theorem tailTrace_6835511 : CollatzResearch.WordTrace tailWord_6835511 prefixEnd_6835511 3509902662095310765476563 := by
  unfold tailWord_6835511
  simp only [CollatzResearch.WordTrace]
  refine ⟨249311567939118534181466387, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166207711959412356120977591 249311567939118534181466387)
  ·
    refine ⟨373967351908677801272199581, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249311567939118534181466387 373967351908677801272199581)
    ·
      refine ⟨140237756965754175477074843, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 373967351908677801272199581 140237756965754175477074843)
      ·
        refine ⟨210356635448631263215612265, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 140237756965754175477074843 210356635448631263215612265)
        ·
          refine ⟨157767476586473447411709199, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 210356635448631263215612265 157767476586473447411709199)
          ·
            refine ⟨236651214879710171117563799, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 157767476586473447411709199 236651214879710171117563799)
            ·
              refine ⟨354976822319565256676345699, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 236651214879710171117563799 354976822319565256676345699)
              ·
                refine ⟨532465233479347885014518549, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 354976822319565256676345699 532465233479347885014518549)
                ·
                  refine ⟨24959307819344432110055557, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 532465233479347885014518549 24959307819344432110055557)
                  ·
                    refine ⟨4679870216127081020635417, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 4 24959307819344432110055557 4679870216127081020635417)
                    ·
                      refine ⟨3509902662095310765476563, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 2 4679870216127081020635417 3509902662095310765476563)
                      ·
                        rfl

theorem cell23_6835511_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4, 2].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 6, 4, 2].length) (baseStart_6835511 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835511 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835511 prefixEnd_6835511 := by exact prefixLift 6835511
  have htrace : WordTrace (prefixWord ++ tailWord_6835511) baseStart_6835511 baseEnd_6835511 := by
    simpa [prefixWord, tailWord_6835511, baseEnd_6835511] using wordTrace_append hprefix tailTrace_6835511
  have hstable : (prefixWord ++ tailWord_6835511).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835511).length < 2 ^ (prefixWord ++ tailWord_6835511).sum := by decide
  have hdescent : baseEnd_6835511 < baseStart_6835511 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835511) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835562 : List Nat := [3, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4]
def baseStart_6835562 : Nat := 118140960795 + 6835562 * 2 ^ 59
def prefixEnd_6835562 : Nat := 4983230072969 + 3 ^ 40 * 6835562 * 2
def baseEnd_6835562 : Nat := 3509928849608690065938829

theorem tailTrace_6835562 : CollatzResearch.WordTrace tailWord_6835562 prefixEnd_6835562 3509928849608690065938829 := by
  unfold tailWord_6835562
  simp only [CollatzResearch.WordTrace]
  refine ⟨62328357015483442472893235, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166208952041289179927715293 62328357015483442472893235)
  ·
    refine ⟨93492535523225163709339853, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 62328357015483442472893235 93492535523225163709339853)
    ·
      refine ⟨35059700821209436391002445, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 93492535523225163709339853 35059700821209436391002445)
      ·
        refine ⟨13147387807953538646625917, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35059700821209436391002445 13147387807953538646625917)
        ·
          refine ⟨4930270427982576992484719, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 3 13147387807953538646625917 4930270427982576992484719)
          ·
            refine ⟨7395405641973865488727079, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 4930270427982576992484719 7395405641973865488727079)
            ·
              refine ⟨11093108462960798233090619, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395405641973865488727079 11093108462960798233090619)
              ·
                refine ⟨16639662694441197349635929, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093108462960798233090619 16639662694441197349635929)
                ·
                  refine ⟨12479747020830898012226947, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16639662694441197349635929 12479747020830898012226947)
                  ·
                    refine ⟨18719620531246347018340421, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 12479747020830898012226947 18719620531246347018340421)
                    ·
                      refine ⟨3509928849608690065938829, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 4 18719620531246347018340421 3509928849608690065938829)
                      ·
                        rfl

theorem cell23_6835562_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 1, 3, 3, 3, 1, 1, 1, 2, 1, 4].length) (baseStart_6835562 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835562 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835562 prefixEnd_6835562 := by exact prefixLift 6835562
  have htrace : WordTrace (prefixWord ++ tailWord_6835562) baseStart_6835562 baseEnd_6835562 := by
    simpa [prefixWord, tailWord_6835562, baseEnd_6835562] using wordTrace_append hprefix tailTrace_6835562
  have hstable : (prefixWord ++ tailWord_6835562).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835562).length < 2 ^ (prefixWord ++ tailWord_6835562).sum := by decide
  have hdescent : baseEnd_6835562 < baseStart_6835562 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835562) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835565 : List Nat := [1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 3]
def baseStart_6835565 : Nat := 118140960795 + 6835565 * 2 ^ 59
def prefixEnd_6835565 : Nat := 4983230072969 + 3 ^ 40 * 6835565 * 2
def baseEnd_6835565 : Nat := 3509930390050653554201315

theorem tailTrace_6835565 : CollatzResearch.WordTrace tailWord_6835565 prefixEnd_6835565 3509930390050653554201315 := by
  unfold tailWord_6835565
  simp only [CollatzResearch.WordTrace]
  refine ⟨249313537480922901403932149, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166209024987281934269288099 249313537480922901403932149)
  ·
    refine ⟨23373144138836522006618639, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 5 249313537480922901403932149 23373144138836522006618639)
    ·
      refine ⟨35059716208254783009927959, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 23373144138836522006618639 35059716208254783009927959)
      ·
        refine ⟨52589574312382174514891939, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 35059716208254783009927959 52589574312382174514891939)
        ·
          refine ⟨78884361468573261772337909, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 52589574312382174514891939 78884361468573261772337909)
          ·
            refine ⟨7395408887678743291156679, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 5 78884361468573261772337909 7395408887678743291156679)
            ·
              refine ⟨11093113331518114936735019, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395408887678743291156679 11093113331518114936735019)
              ·
                refine ⟨16639669997277172405102529, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 11093113331518114936735019 16639669997277172405102529)
                ·
                  refine ⟨12479752497957879303826897, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 2 16639669997277172405102529 12479752497957879303826897)
                  ·
                    refine ⟨9359814373468409477870173, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 2 12479752497957879303826897 9359814373468409477870173)
                    ·
                      refine ⟨3509930390050653554201315, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9359814373468409477870173 3509930390050653554201315)
                      ·
                        rfl

theorem cell23_6835565_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 5, 1, 1, 1, 5, 1, 1, 2, 2, 3].length) (baseStart_6835565 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835565 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835565 prefixEnd_6835565 := by exact prefixLift 6835565
  have htrace : WordTrace (prefixWord ++ tailWord_6835565) baseStart_6835565 baseEnd_6835565 := by
    simpa [prefixWord, tailWord_6835565, baseEnd_6835565] using wordTrace_append hprefix tailTrace_6835565
  have hstable : (prefixWord ++ tailWord_6835565).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835565).length < 2 ^ (prefixWord ++ tailWord_6835565).sum := by decide
  have hdescent : baseEnd_6835565 < baseStart_6835565 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835565) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835585 : List Nat := [1, 2, 4, 3, 2, 2, 1, 2, 6]
def baseStart_6835585 : Nat := 118140960795 + 6835585 * 2 ^ 59
def prefixEnd_6835585 : Nat := 4983230072969 + 3 ^ 40 * 6835585 * 2
def baseEnd_6835585 : Nat := 389993406629304830661247

theorem tailTrace_6835585 : CollatzResearch.WordTrace tailWord_6835585 prefixEnd_6835585 389993406629304830661247 := by
  unfold tailWord_6835585
  simp only [CollatzResearch.WordTrace]
  refine ⟨249314266940850444819660209, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166209511293900296546440139 249314266940850444819660209)
  ·
    refine ⟨186985700205637833614745157, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 249314266940850444819660209 186985700205637833614745157)
    ·
      refine ⟨35059818788557093802764717, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 4 186985700205637833614745157 35059818788557093802764717)
      ·
        refine ⟨13147432045708910176036769, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 35059818788557093802764717 13147432045708910176036769)
        ·
          refine ⟨9860574034281682632027577, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 2 13147432045708910176036769 9860574034281682632027577)
          ·
            refine ⟨7395430525711261974020683, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 2 9860574034281682632027577 7395430525711261974020683)
            ·
              refine ⟨11093145788566892961031025, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 7395430525711261974020683 11093145788566892961031025)
              ·
                refine ⟨8319859341425169720773269, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 2 11093145788566892961031025 8319859341425169720773269)
                ·
                  refine ⟨389993406629304830661247, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8319859341425169720773269 389993406629304830661247)
                  ·
                    rfl

theorem cell23_6835585_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 2, 4, 3, 2, 2, 1, 2, 6].length) (baseStart_6835585 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835585 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835585 prefixEnd_6835585 := by exact prefixLift 6835585
  have htrace : WordTrace (prefixWord ++ tailWord_6835585) baseStart_6835585 baseEnd_6835585 := by
    simpa [prefixWord, tailWord_6835585, baseEnd_6835585] using wordTrace_append hprefix tailTrace_6835585
  have hstable : (prefixWord ++ tailWord_6835585).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835585).length < 2 ^ (prefixWord ++ tailWord_6835585).sum := by decide
  have hdescent : baseEnd_6835585 < baseStart_6835585 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835585) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835595 : List Nat := [1, 1, 1, 1, 4, 3, 1, 6, 1, 1, 3]
def baseStart_6835595 : Nat := 118140960795 + 6835595 * 2 ^ 59
def prefixEnd_6835595 : Nat := 4983230072969 + 3 ^ 40 * 6835595 * 2
def baseEnd_6835595 : Nat := 3509945794470288436826177

theorem tailTrace_6835595 : CollatzResearch.WordTrace tailWord_6835595 prefixEnd_6835595 3509945794470288436826177 := by
  unfold tailWord_6835595
  simp only [CollatzResearch.WordTrace]
  refine ⟨249314631670814216527524239, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 1 166209754447209477685016159 249314631670814216527524239)
  ·
    refine ⟨373971947506221324791286359, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 1 249314631670814216527524239 373971947506221324791286359)
    ·
      refine ⟨560957921259331987186929539, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 1 373971947506221324791286359 560957921259331987186929539)
      ·
        refine ⟨841436881888997980780394309, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 1 560957921259331987186929539 841436881888997980780394309)
        ·
          refine ⟨157769415354187121396323933, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 4 841436881888997980780394309 157769415354187121396323933)
          ·
            refine ⟨59163530757820170523621475, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 3 157769415354187121396323933 59163530757820170523621475)
            ·
              refine ⟨88745296136730255785432213, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 1 59163530757820170523621475 88745296136730255785432213)
              ·
                refine ⟨4159935756409230739942135, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 6 88745296136730255785432213 4159935756409230739942135)
                ·
                  refine ⟨6239903634613846109913203, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 1 4159935756409230739942135 6239903634613846109913203)
                  ·
                    refine ⟨9359855451920769164869805, ?_, ?_⟩
                    · exact (by decide : CollatzResearch.ExactOddStep 1 6239903634613846109913203 9359855451920769164869805)
                    ·
                      refine ⟨3509945794470288436826177, ?_, ?_⟩
                      · exact (by decide : CollatzResearch.ExactOddStep 3 9359855451920769164869805 3509945794470288436826177)
                      ·
                        rfl

theorem cell23_6835595_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 1, 3].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 1, 1, 1, 1, 4, 3, 1, 6, 1, 1, 3].length) (baseStart_6835595 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835595 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835595 prefixEnd_6835595 := by exact prefixLift 6835595
  have htrace : WordTrace (prefixWord ++ tailWord_6835595) baseStart_6835595 baseEnd_6835595 := by
    simpa [prefixWord, tailWord_6835595, baseEnd_6835595] using wordTrace_append hprefix tailTrace_6835595
  have hstable : (prefixWord ++ tailWord_6835595).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835595).length < 2 ^ (prefixWord ++ tailWord_6835595).sum := by decide
  have hdescent : baseEnd_6835595 < baseStart_6835595 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835595) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

def tailWord_6835602 : List Nat := [3, 2, 3, 3, 1, 1, 3, 1, 6]
def baseStart_6835602 : Nat := 118140960795 + 6835602 * 2 ^ 59
def prefixEnd_6835602 : Nat := 4983230072969 + 3 ^ 40 * 6835602 * 2
def baseEnd_6835602 : Nat := 389994376537207767715405

theorem tailTrace_6835602 : CollatzResearch.WordTrace tailWord_6835602 prefixEnd_6835602 389994376537207767715405 := by
  unfold tailWord_6835602
  simp only [CollatzResearch.WordTrace]
  refine ⟨62328721745447214180757265, ?_, ?_⟩
  · exact (by decide : CollatzResearch.ExactOddStep 3 166209924654525904482019373 62328721745447214180757265)
  ·
    refine ⟨46746541309085410635567949, ?_, ?_⟩
    · exact (by decide : CollatzResearch.ExactOddStep 2 62328721745447214180757265 46746541309085410635567949)
    ·
      refine ⟨17529952990907028988337981, ?_, ?_⟩
      · exact (by decide : CollatzResearch.ExactOddStep 3 46746541309085410635567949 17529952990907028988337981)
      ·
        refine ⟨6573732371590135870626743, ?_, ?_⟩
        · exact (by decide : CollatzResearch.ExactOddStep 3 17529952990907028988337981 6573732371590135870626743)
        ·
          refine ⟨9860598557385203805940115, ?_, ?_⟩
          · exact (by decide : CollatzResearch.ExactOddStep 1 6573732371590135870626743 9860598557385203805940115)
          ·
            refine ⟨14790897836077805708910173, ?_, ?_⟩
            · exact (by decide : CollatzResearch.ExactOddStep 1 9860598557385203805940115 14790897836077805708910173)
            ·
              refine ⟨5546586688529177140841315, ?_, ?_⟩
              · exact (by decide : CollatzResearch.ExactOddStep 3 14790897836077805708910173 5546586688529177140841315)
              ·
                refine ⟨8319880032793765711261973, ?_, ?_⟩
                · exact (by decide : CollatzResearch.ExactOddStep 1 5546586688529177140841315 8319880032793765711261973)
                ·
                  refine ⟨389994376537207767715405, ?_, ?_⟩
                  · exact (by decide : CollatzResearch.ExactOddStep 6 8319880032793765711261973 389994376537207767715405)
                  ·
                    rfl

theorem cell23_6835602_ordinary_descent (u : Nat) :
    ∃ endpoint, ordinaryRun ([1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 6].sum + [1, 2, 1, 1, 1, 1, 2, 2, 1, 2, 1, 1, 2, 1, 1, 1, 1, 1, 1, 1, 3, 1, 2, 1, 1, 1, 1, 1, 3, 1, 1, 2, 4, 3, 1, 1, 2, 2, 1, 1, 3, 2, 3, 3, 1, 1, 3, 1, 6].length) (baseStart_6835602 + u * 2 ^ 82) = endpoint ∧
      endpoint < baseStart_6835602 + u * 2 ^ 82 := by
  have hprefix : WordTrace prefixWord baseStart_6835602 prefixEnd_6835602 := by exact prefixLift 6835602
  have htrace : WordTrace (prefixWord ++ tailWord_6835602) baseStart_6835602 baseEnd_6835602 := by
    simpa [prefixWord, tailWord_6835602, baseEnd_6835602] using wordTrace_append hprefix tailTrace_6835602
  have hstable : (prefixWord ++ tailWord_6835602).sum < 82 := by decide
  have hcontract : 3 ^ (prefixWord ++ tailWord_6835602).length < 2 ^ (prefixWord ++ tailWord_6835602).sum := by decide
  have hdescent : baseEnd_6835602 < baseStart_6835602 := by decide
  rcases family_descends (prefixWord ++ tailWord_6835602) htrace hstable hcontract hdescent u with ⟨endpoint, hfull, hlt⟩
  exact ⟨endpoint, wordTrace_ordinary hfull, hlt⟩

end V185TrunkScan23Incremental
